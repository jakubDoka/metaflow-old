# MetaFlow

## Mindset

(All you see is more planned then implemented and subject of change.)

MetaFlow, as its name tells, is focused on complex metaprogramming. This means you can write code to generate code (to generate code...), make DSL-s (Domain Specific Language) that can be used by other people by just including your package in dependencies. Features include Generics, Templates and String/Token/Ast/IR macros. Though Templates will be just macros generated by macro from standard library. This is no easy task, fortunately Metaflow uses Cranelift backend so all macros can be jit compiled. Garbage collector is not built into language but can be created with macros. Idea is to make macro analyze a datatype and generate code that traverses RC and ARC references to find cycles and solve other problems.
This makes garbage collector optional and it is more likely, standard library will not rely on it.

Metaflow is not object oriented and it does not support reflection as a default feature. On the other hand it allows user simplify the mess in other ways. Lets demonstrate.

```mf

struct Counter:
  count: int

impl Counter:
  fun inc(c: &Counter):
    ++c.count

struct Something:
  embed counter: Counter

attr entry
fun main -> int:
  var s: Something

  # subtract 12
  s.counter.count -= 2
  s.count -= 10

  loop:
    if s.count < 0:
      break
    # increment 3
    Counter::inc(&s.counter)
    s.counter.inc()
    s.inc()

  # return 0
  return s.count
```

Each type can embed multiple fields and field and it works recursively. Every function can be called in dot style on the first argument. Though you still can use `pub` and `priv` to restrict use of code items and fields. This is merely to give authors more tools to create friendly API for their libraries.

MetaFlow is space significant language. Indentation matters, semicolon isn't even recognized by lexer (yet).

Even though I stated that Metaflow is not OO, you can still relate functions with types. It can come really handy when working with generics and this form of static dispatch is a most preferable and minimal.

Metaflow is mainly inspired by Nim, Go and Rust. Compiler is written in Rust and it probably will stay that way.

### Limitations

#### No Module Cyclic Dependencies

Cyclic dependencies caused by 'use' keyword are detected and reported as errors. This simple limitation allows for nice features and optimized compilation. For example, this means compiler can disregard order of definitions within the file and eliminates forward definition syntax. All metaprogramming features also rely on this limitation. Compiler compiles module in sorted order so you can determinate in which order files compile ([more on this here](#order-of-compilation)). Then there are also performance reasons as less complex data-structures have to be maintained at the same time. 

#### Macros

There are just one simple limitation that allows for other nice features. Macro cannot be called from module where it is defined. That means compiler can disregard order of definitions. The order matters only on module level.

## Documentation

This section documents most of the properties of MetaFlow.

### Source organization

Compiler considers files as separate modules. Whole project including project manifest is considered a Package. Packages can be imported in [manifest](#manifest). Cyclic dependency either between packages or modules is not allowed.

### Definition order

Order of definitions within module does not matter but general practice (i just copied) is writing declaration after use, when possible for any code item. This does not include global 'var', 'const' and 'let', they should be on the top of the file right after 'use'. Mentioned 'use' keyword can be used only once per file and must be first. Other occurrences of 'use' will result in error.

### Order of compilation

Compilation order is stable and controllable. For example you have modules A -> [B, C] -> D and you want the C to be compiled after B because they change globals state in D during compile time. This can be achieved by adding C -> B.

### Manifest

Dependency management is done trough git. Its really simple actually. In manifest you specify:

```mf
dependencies:
  something "github.come/someone/something@tag"
  # or
  something_local "local/path/to/something" 
  # its best to use paths within project so 
  # other people can st...use your code easily
```

You can now 'use' modules from `something` as:

```mf
use
  "something" # for the root
  alias "something/submodule" # submodule but you now refer to items as 'alias::item'
```

You can refer to items from module as `<alias or module file name>::item` but this is only last resort as you can omit this if there is no name collision. Alias is also optional as by default, last segment of path is used as alias.

Package structure is determined by manifest but also some implementation details. (i am too lazy to solve...). Manifest has to contain the 'root' attribute with a name of root module, all other modules have to be located in sub-directory with the name of root module:

```txt
package.mfm # contains: root = "src/main.mf"
src/
  main.mf
  main/
    sub.mf
    other_sub.mf
```

Why is it like this? Well, dependencies can be aliased and so first segment of the module path has to be disregarded and replaced with the root file name. Thus simply, first path segment is always the root name.

You can control where are dependencies placed by using `METAFLOW_CACHE`. This simple batch file will prepare environment and compile the project:

```bat
@rem sets cache to directory local to project, generally 
@rem you want to save space and use global cache
set METAFLOW_CACHE=deps
@rem calls the compiler specifying directory with manifest
mf .
```

### Syntax

The syntax is expressed with following syntax so that this section is not infinite.

- `()` - for grouping items
- `{}` - items inside can repeat or be absent
- `[]` - items inside are optional
- `''` - text between is a regex
- `|` - open choice between left and right items until `()` or other '|' at same level
- `=` - assigns syntax rules to alias
- `:` - item after can be written in indented block, block can have multiple lines
- `#` - items after are commented out
- whitespace does not matter

Now the explained example:

```txt
opinion = 'this is ' [ 'not ' ] 'good'
# matches 'this is good' and 'this is not good'
annoying_child = 'Dad! ' :( 'When will we arrive?' )
# matches 'Dad! When will we arrive?' but also
# 'Dad! 
#  When will we arrive?
#  When will we arrive?
#  When will we arrive?
#  When will we arrive?
#  When will we arrive?'
swearing = 'Be quiet.' | 'Shut ' [ 'the '  ( 'hell' | '####' ) ] ' up!' 
# matches 'shut the hell up' but also 'shut the #### up' and 'shut up'
# or 'Be quiet.'
travel = { annoying_child swearing }
# here we combine second and third syntax and repeat it 
# variable amount of times
```

Now the real syntax:

```txt
file = [ use '\n' ] { item '\n' }
use = 'use' :( [ ident ] string )
item = 
  impl |
  function |
  global | 
  struct

impl =
  'impl'
  [ vis ] [ generics ] type
  ':' :( function | operator_override | global )
function = 
  'fun' 
  [ vis ] ident [ generics ] 
  [ '(' [ fun_arg { ',' fun_arg } ] ')' ]
  [ '->' type ] 
  call_convention
  [ ':' : statement ]
operator_override = 
  'fun' 
  [ vis ] op [ generics ] 
  '(' fun_arg [ ',' fun_arg ] ')'
  '->' type 
  ':' : statement
global =
  ( 'var' | 'let' ) 
  [ vis ]
  :( 
    ident { ',' ident } 
    ( 
      ':' type [ '=' expression ] | 
      '=' expression 
    ) 
  )
struct = 
  'struct'
  [ vis ] ident [ generics ]
  [ ':' : field ]

field = 
  [ vis ] [ 'embed' ] 
  ident { ',' ident } 
  ':' type

statement =
  if | 
  loop | 
  break | 
  continue | 
  return_stmt | 
  variable | 
  expr
if = 
  'if' expr ':' : statement 
  { elif ':' : statement } 
  [ 'else' ':' : statement ]
loop = 'loop' [ label ] ':' : statement
break = 'break' [ label ] [ expr ]
continue = 'continue' [ label ]
return = 'return' [ expr ]
variable = 
  ( 'var' | 'let' ) 
  :( 
    ident { ',' ident } 
    ( 
      ':' type [ '=' expression ] | 
      '=' expression 
    ) 
  )

expr = 
  literal | 
  call | 
  access | 
  assign | 
  binary | 
  unary | 
  cast | 
  reference | 
  dereference

literal =
  number |
  string |
  bool |
  '\'' char '\''

number = "\d+\.?\d*([iuf]\d{0, 2})?"
string = '"' { char } '"'
bool = 'true' | 'false'

call = [expr '.'] ident '(' [ expr { ',' expr } ] ')'
access = [expr '.'] ident
assign = expr '=' expr
binary = expr op expr
unary = op expr
cast = expr 'as' type
ref = '&' expr
deref = '*' expr

type = 
  ident [ '[' type { ',' type } ']' ] |
  'fun' [ '(' type { ',' type} ')' ] [ '->' type ] call_convention |
  '&' type
generics = '[' ident { ',' ident } ']'
args = '(' { [ 'var' ] ident { ',' ident } ':' type } ')'
vis = 'pub' | 'priv'
char = '([^\\']|\\(\\|\'|a|b|e|f|v|n|r|t|0|[0-7]{3}|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{8}))'
label = '\'[a-zA-Z0-9_]+\b'
op = '([\+\-\*/%\^=<>!&\|\?:~]+|\b(min|max|abs)\b)'
call_convention = ident
ident = '\b[a-zA-Z_][a-zA-Z0-9_]*\b'

```

### To be continued

## Compiler design

This section merely describes how compiler works as a reference. Things you see may be planned in a future, but are written in present tense.

### Memory management and access

Almost all the data compiler uses during compilation is stored in constructs contained in `crate::util::storage`. Each ordered container has an accessor type that implements `crate::util::storage::IndexPointer`. Every entity has its Index type that has a descriptive name and data itself is in `<name>Ent` struct. This is safe and convenient way of creating complex structures like graphs without ref count and over all makes borrow checker happy.

Exception to this rule is `crate::ast::Ast` which does not use this kind of storage for sanity reasons, it also does not need to as its only used as immutable structure.

What you will see a lot is `self.context.pool.get()` whenever temporary Vec is needed. Pool saves used Vec-s and only allocate if there is not vec to reuse. What pool returns is PoolRef that will send it self to pool upon drop. The lifetime of the pool is ont related to Vecs when they are borrowed, instead pool panics if it is dropped before all Vecs are returned to it. This ensures we dont have to deal with livetimes but also assert some safety on debug builds.

All items that has particular name from source code are hashed with sdbm hash and combined with custom hashing mentod. Related to this, custom hashmap is used that focuses on integer ids. Idea is to improve performance as we do not need default safe hashes. Other reason for using custom hashes is speed up of static dispatch of nongeneric functions.

### Compilation steps

Compiler divides compilation into several steps to make code more organized and manageable. Passes are divided into:

- lexing
- ast building
- ast sorting
- type parsing
- function parsing
- generating cranelift ir
