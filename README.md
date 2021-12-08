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

Package structure is determined by manifest but also some implementation details i am too lazy to solve... anyway, you have to specify the 'root' attribute with a name of root module and you have to place submodules into directory with the same name as the root module. For example:

```txt
package.mfm // contains: root = "src/main.mf"
src/
  main.mf
  main/
    sub.mf
    other_sub.mf
```

Why is it like this? Well, dependencies can be aliased and so first segment of the module path has to be disregarded and replaced with the root file name. Thus simply, first path segment is always the root name.

### To be continued

## Compiler design

This section merely describes how compiler works as a reference for me. Things you see may be planned in a future, but are written in present tense.

### Memory management and access

Almost all the data compiler uses during compilation is stored in constructs contained in `crate::util::storage`. Each ordered container has an accessor type that implements `crate::util::storage::IndexPointer`. Every entity has its Index type that has a descriptive name and data it self is in `<name>Ent` struct. This is safe and convenient way of creating complex structures like graphs without ref count and over all makes borrow checker happy.

Exception to this rule is `crate::ast::Ast` which does not use this kind of storage for sanity reasons, it also does not need to as its only used as immutable structure.
