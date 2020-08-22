# Pointless to Haskell Compiler
This transpiler is an implementation of a dynamic, declarative and functional programming lanuage named [Pointless](https://github.com/pointless-lang/pointless/). It compiles that to Haskell. Currently it does object tracking for error reporting and greets you with error messages with line numbers. It also detects errors like duplicate definitions and undefined variables at compile-time.

# Dependencies
Haskell runtime requires you to install two additional dependencies, I used Haskell platform but I don't know how many of these are avalible in Haskell by default, they are `System.Ramdom` and `Data.Hashable`. So just `cabal install` them.

# Limitations
There are many limitation in this compiler right now, as it's runtime doesn't implement many language fields such as IO features of Pointless. They will be implemented later as the compiler continues to evolves.

# How to use
It's very simple, first you build it with your favorite flags with nim's compiler then you write command like this,
```
compiler example.ptls
```
So basically, file name of the compiler followed by that of the source file you need to compile.
```
[compiler-exe-name] [source-file-name]
```
To run the generated file you should look at the generated folder named `output` and your files will be avalible there.  Then you can run them like this.
```
[source-file-name].lua
```
so, for examle `example.ptls` would turn into `example.hs`.
