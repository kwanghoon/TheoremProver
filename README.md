TheoremProver
=============

A Haskell Implemetation of a Tactical Theorem Prover in L.C. Paulson's Book (ML for the Working Programmer).


GHCi, version 7.0.4: http://www.haskell.org/ghc/  :? for help

Loading package ghc-prim ... linking ... done.

Loading package integer-gmp ... linking ... done.

Loading package base ... linking ... done.

Loading package ffi-1.0 ... linking ... done.

Prelude> [1 of 1] Compiling Main             ( /Users/lazyswamp/Work/haskell/theoremprover/Main.hs, interpreted )

Ok, modules loaded: Main.

*Main> main

Starting Tactical Theorem Prover...

> goal P & Q --> Q & P

(P & Q --> Q & P)

1. empty  |- (P & Q --> Q & P)

> by impR 1

(P & Q --> Q & P)
 1. P & Q  |- Q & P

> by conjL 1

(P & Q --> Q & P)
 1. P, Q  |- Q & P

> by conjR 1

(P & Q --> Q & P)
 1. P, Q  |- Q
 2. P, Q  |- P

> by basic 2

(P & Q --> Q & P)
 1. P, Q  |- Q

> by basic 1

(P & Q --> Q & P)
No subgoals left!

> quit
end...

*Main> 
