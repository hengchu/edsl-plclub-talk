# edsl-plclub-talk

This repository contains the full implementation of the toy DSL presented in my
PLClub talk on combining deep and shallow representations for EDSL, using the
technique from
http://www.cse.chalmers.se/~josefs/publications/svenningsson2015combining.pdf

In particular, we show one possible type of sophisticated program analysis
that's enabled by the deep representation of the EDSL--symbolic execution.

`src/EDSL.hs`: contains the AST definition, and the `Syntactic` typeclass and
instantiates `Syntactic` for arrow types, and monadic effect types. There are
also a dozen or so examples programs written using the shallow representation at
the bottom of the file.

`src/Concrete.hs`: implements the definitional interpreter for the DSL

`src/Symbolic.hs`: implements a lazy, call-by-value symbolic execution engine
for the DSL

`src/Solver.hs`: implements `untilCrash` and `untilCrashIO`, which consume a
(potentially infinite) stream of path conditions, and stops on the first
satisfying path condition, signaling the discovery of a possible crash in the
DSL program.

Talk slides: https://docs.google.com/presentation/d/1VB8C2wZ1ffk5QredN6mBLAaWeaT_8huMowZDyiZfKds/edit?usp=sharing
