# MetaFlow

## Setting up

To setup compiler you have to have Git, Rust and Cargo installed so you can compile the project. Following commands are needed: 

```bat
git clone --depth 1 https://github.com/jakubDoka/metaflow
git submodule update --remote --recursive
cargo build --release
```

You will also need `cc` for linking the program. For me the path of `cc` is `C:\msys64\mingw64\bin\cc.exe` which beautifully shows what you have to install. Though you can link with any other linker by specifying `--linker <name>` flag `cc` is just default. 

## Mindset

(All you see is more planned then implemented and subject of change.)

MetaFlow, as its name tells, is focused on complex metaprogramming. This means you can write code to generate code (to generate code...), make DSL-s (Domain Specific Language) that can be used by other people by just including your package in dependencies. Features include Generics, Templates and String/Token/Ast/IR macros. Though Templates will be just macros generated by macro from standard library. This is no easy task, fortunately Metaflow uses Cranelift backend so all macros can be jit compiled.

There are no builtin garbage collection but moving semantics (Like rust).

Metaflow is not object oriented and it does not support reflection or inheritance as a default feature. On the other hand it allows user simplify the mess in other ways.

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

Cyclic dependencies caused by 'use' keyword are detected and reported as errors. All metaprogramming features rely on this limitation. 

#### Macro limitations

There are just one simple limitation that allows for other nice features. Macro cannot be called from module where it is defined. That means compiler can disregard order of definitions. The order matters only on module level.

## Documentation

This section documents most of the properties of MetaFlow.

### Source organization

Compiler considers files as separate modules. Whole project including project manifest is considered a Package. Packages can be imported in [manifest](#manifest). Cyclic dependencies either between packages or modules are not allowed.

### Definition order

Order of definitions within module does not matter but general practice (i just copied) is writing declaration after use when possible for any code item. This does not include global 'var' and 'let', they should be on the top of the file right after 'use'. Mentioned 'use' keyword can be used only once per file and must be first. Other occurrences of 'use' will result in error.

### Order of compilation

Compilation order is stable and controllable. For example you have modules A -> [B, C] -> D and you want the C to be compiled after B because they change globals state in D during compile time. This can be achieved by adding C -> B.

### Manifest

Dependency management is done trough git. Its really simple actually. In manifest you specify:

```mf
dependencies:
  something "github.com/someone/something@tag"
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

You can refer to items from module as `<alias or module file name>::item` but this is only last resort as you can omit this if there is no name collision. Alias is also optional, as by default, last segment of path is used as alias.

Package structure is determined by manifest but also some implementation details. (i am too lazy to solve...). Manifest has to contain the 'root' attribute with a name of root module, all other modules have to be located in sub-directory with the name of root module:

```txt
package.mfm # contains: root = "src/main.mf"
src/
  main.mf
  main/
    sub.mf
    other_sub.mf
```

Why is it like this? Well, dependencies can be aliased and so first segment of the module path has to be disregarded and replaced with the root file name of owning package. Thus simply, first path segment is always the root name.

You can control where are dependencies placed by using `METAFLOW_CACHE`. This simple batch file will prepare environment and compile the project:

```bat
@rem sets cache to directory local to project, generally 
@rem you want to save space and use global cache
set METAFLOW_CACHE=deps
@rem calls the compiler specifying directory with manifest
mf .
```

Important thing to note is that compiler will simply clone the repository with given version (and depth 1) and place it into cache, it no longer checks if dependency is outdated and only reinstalls if you change the version. It also does not discard old versions.

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
# matches 'Dad! When will we arrive?' but also '
#Dad!
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

```py
module = [ use '\n' ] { item '\n' }
use = 'use' :( [ ident ] string )
item = 
  impl |
  attr |
  doc_comment |
  function |
  global_var |
  struct

impl =
  'impl'
  [ vis ] [ generics ] datatype
  ':' :( function | operator_override | global_var )
attr = 
  'attr' attr_element { ',' attr_element }
attr_element = 
  ident '=' expr | 
  ident [ '(' attr_element { ',' attr_element } ')' ] )
function = 
  'fun' 
  [ vis ] ident [ generics ] 
  [ '(' [ fun_arg { ',' fun_arg } ] ')' ]
  [ '->' datatype ] 
  call_convention
  [ ':' : statement ]
operator_override = 
  'fun' 
  [ vis ] op [ generics ] 
  '(' fun_arg [ ',' fun_arg ] ')'
  '->' datatype 
  ':' : statement
global_var =
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
  break_stmt | 
  continue_stmt | 
  return_stmt | 
  variable |
  expr

break_stmt = 'break' [ label ] [ expr ]
continue_stmt = 'continue' [ label ]
return_stmt = 'return' [ expr ]
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
  if_expr | 
  for_expr |
  literal | 
  call | 
  access | 
  assign | 
  binary | 
  unary | 
  cast | 
  reference | 
  dereference

if_expr = 
  'if' expr ':' : statement 
  { 'elif' expr ':' : statement } 
  [ 'else' ':' : statement ]
for_expr = 'for' [ label ] [ expr [ 'in' expr ] ] ':' : statement
literal =
  number |
  string |
  boolean |
  '\'' char '\''

# underscores in numbers are allowed
number = "[\d_]+\.?[\d_]*([iuf]\d{0, 2})?"
string = '"' { char } '"'
boolean = 'true' | 'false'

call = [expr '.'] ident '(' [ expr { ',' expr } ] ')'
access = [expr '.'] ident
assign = expr '=' expr
binary = expr op expr
unary = op expr
cast = expr 'as' datatype
ref = '&' expr
deref = '*' expr

datatype = 
  ident [ '[' datatype { ',' datatype } ']' ] |
  'fun' [ '(' datatype { ',' datatype } ')' ] [ '->' datatype ] call_convention |
  '&' datatype
generics = '[' ident { ',' ident } ']'
args = '(' { [ 'var' ] ident { ',' ident } ':' datatype } ')'
vis = 'pub' | 'priv'
char = '([^\\\']|\\(\\|\'|a|b|e|f|v|n|r|t|0|[0-7]{3}|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{8}))'
label = '\'[a-zA-Z0-9_]+\b'
op = '([\+\-\*/%\^=<>!&\|\?:~]+|\b(min|max|abs)\b)'
call_convention = ident
ident = '\b[a-zA-Z_][a-zA-Z0-9_]*\b'
# skipped when lexing
comment = '#.*' | '#\[[\s\S\]*]#'
# not skipped
doc_comment = '##.*' | '##\[[\s\S\]*]#'
```

### File items

File can contain several items:
- `use` - Only one per file and it is always the first item. It is used for importing other modules. Reason why you are limited when declaring dependencies is a fact that compiler can build the module tree without parsing and analyzing the ast.
- `function` - Function is where you place your logic. Example:

```nim
## calculates n-th element of fibonacci sequence
fun fib(n: int) -> int:
  if n < 2:
    1
  else:
    fib(n - 1) + fin(n - 2)
```
- `attr` - Attributes are here to reduce amount of keywords and boilerplate in code. For example if you want to make function inline you write `attr inline` above the function. If you want to make all functions in the file inline you can place `attr push(inline)` on the top of the file. When you add `attr pop`, last pushed attribute will no longer be applied.
- `doc_comment` - Preserved in ast for documentation generation. (TODO)
- `global` - Global variables can contain expression that will be evaluated at the beginning of program.
- `struct` - Struct defines relation of data with finite size.
- `impl` - Impl block defines relation between data and logic. Functions and globals defined inside a block, will be related with for example `struct` which allows dot notation when calling the function but you can still refer to items in block by prefixing them with the name of `struct` (`Datatype::item`). Operator functions can only be defined in impl block.

All file items also have its visibility. By default, items are visible to modules from the same package. If you want to make items private the file you can use `priv`, if you want to make items visible to potential users of the package, you use `pub`. Tree levels of privacy are inspired by usual complaints of programmers regarding other programming languages. Option to make things public across project is very common task so Metaflow chooses this as its default option.

### Control flow

- `if` - Essential conditional that decides what to execute base of boolean condition. It also acts as expression and can evaluate into a value. Example:

```nim
let number = if condition: 1 else: 2

if condition:
  assert(condition == true)
elif other_condition: 
  assert(condition == false)
  assert(other_condition == true)
else:
  assert(condition == false)
  assert(other_condition == false)
```

- `for` - Allows repeating instructions variable amount of times. Keyword is related with `break`, which terminates the loop, and `continue`, which jumps back to first instruction of the loop. loop can be used in three ways:
```py
# infinite
for: pass

# TODO
# while condition holds
for condition: pass
# can be written as
for: if condition:
  pass
else: break

# TODO
# until iterator yields None
for item in iterator: pass
# can be written as
for:
  let item = iterator.next()
  if item.is_none(): break
  else:
    let item = item.unwrap()
    pass
```

### To be continued

## Compiler design

This section merely describes how compiler works as a reference. Things you see may be planned in a future, but are written in present tense.

### Memory management and access

Design of the compiler is inspired by cranelift and it uses `cranelift_entity` almost everywhere. Good example is the Ast that uses the `ListPool` to build the tree and then quickly clear it later on. Serializing this kind of structure is also easier for processor.

What you will see a lot is `self.context.pool.get()` whenever temporary Vec is needed. Pool saves used Vec-s and only allocate if there is not vec to reuse. What pool returns is PoolRef that will send it self to pool upon drop. The lifetime of the pool is ont related to Vecs when they are borrowed, instead pool panics if it is dropped before all Vecs are returned to it. This ensures we don't have to deal with lifetimes but also assert some safety on debug builds.

All items that has particular name from source code are hashed with sdbm hash and combined with custom hashing method. Related to this, custom hashmap is used that focuses on integer ids. Idea is to improve performance as we do not need default safe hashes.

### Compilation steps

Compiler divides compilation into several steps to make code more organized and manageable. Passes are divided into:

- lexing
- ast building
- ast sorting
- type parsing
- function parsing / building ir
- generating cranelift ir

Reason to have two levels of ir is that compiler needs to analyze the source code and ast is not enough, in contrary, cranelift ir does not allow for storing some data and mutating the structures. Metaflow ir is similar to cranelift ir but lot higher level. This also takes some load from function parsing, which is already most complex stage.