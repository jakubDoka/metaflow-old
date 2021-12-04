# MetaFlow

## Compiler Design

The main unit of code is a file. Dependency cycles between files is not allowed which allows making compilation reasonably multi-threaded when possible, and also allows for nicer metaprogramming features. Order of declarations in a module does not matter but macro cannot be used in a module it was defined. This way you can use use already defined functions in macros to produce ne functions and structures. Macro recursing it self is also disallowed by design and hopefully is not too great limitation. This way macros can be jit compiled and called by compiler to produce anything.

