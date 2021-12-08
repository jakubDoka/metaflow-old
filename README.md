# MetaFlow

## Documentation

This section documents most of the properties of MetaFlow

### Good to know

Ambiguous identifiers are shadowed by first encountered occurrence.

### Source organization

Compiler considers files as separate modules. Whole project including project manifest is considered a Package. Packages can be imported in manifest (section 'dependencies'). Cyclic dependency either between packages or modules is no allowed. This allows compiler to compile more efficiently and over all makes code easier to traverse as no two files reference each other.

### Definition order

Order if definitions within module does not matter but general practice (i just declared) is writing declaration after use when possible for any code item. This does not include global 'var' and 'let', they should be on the top of the file right after 'use'. Mentioned 'use' keyword can be used only once per file and must be first. Other occurrences of 'use' will result in error.

### Order of compilation

Compilation is divided into cycles. Compiler finds packages that does not depend on each other and have all dependency compiled and compiles them on separate threads. This also means compilation order is stable but arbitrary, all you can rely on is the fact that all items in dependent modules are compiled before current module. If you want to determinate order of compilation, for example you have module A -> [B, C] -> D and you want the C to be compiled after B because they change globals state in D during compile time. This can be achieved by making C -> B.

### Dependency management

Dependency management is done trough git. Its really simple actually. In manifest you specify:

```mf
extern something "github.come/someone/something@tag"
```

You can now 'use' modules from `something` as:

```mf
use extern
  "something"
  alias "something/submodule"
```

You can refer to items from module as `<alias or module file name>::item` but this is only last resort as you can omit this if there is no name collision.  

### To be continued

## Compiler design

This section merely describes how compiler works as a reference for me. Things you see may be planned in a future, but are written in present tense.

### Memory management and access

Almost all the data compiler uses during compilation is stored in constructs contained in `crate::util::storage`. Each ordered container has an accessor type that implements `crate::util::storage::IndexPointer`. Every entity has its Index type that has a descriptive name and data it self is in `<name>Ent` struct. This is safe and convenient way of creating complex structures like graphs without ref count and over all makes borrow checker happy.

Exception to this rule is `crate::ast::Ast` which does not use this kind of storage for sanity reasons, it also does not need to as its only used as immutable structure.

### Concurrency strategy

The concurrency model is lock free (so far) but not wait free. Each thread compiles one Package at the time fow which all dependencies are compiled. Compiler builds the graph, checks for cycles and sorts nodes in order where each module has no dependency before him. (root module is first, tail modules are last). Same procedure goes for modules within package. Files that are not used are not compiled unless you depend on them, so even depending on huge library for one low level feature does not affect compile time but will take space on disc.
