# MiniJl for FTfJP 2019

Submission for FTfJP-2019: 
decidable tag-based semantic subtyping
for a subset of the [Julia](https://julialang.org/) language.

* [`paper`](paper) directory contains the paper.
  Run `make` withing this directory to build a pdf.

* [`Mechanization`](Mechanization) directory contains Coq code
  relevant to the paper.
  Run `make` within the directory to compile it.
  
  * [`Mechanization/MiniJl`](Mechanization/MiniJl)
    has all the definitions and proofs related to 
    tag-based semantic subtyping presented in the paper.
  
  * [`Mechanization/FullAtomicJl`](Mechanization/FullAtomicJl)
    has all the definitions and proofs related to
    the alternative tag-based semantic subtyping discussed in Sec. 5.
    (Almost the same as MiniJl but with atomic normal form.)

  * [`Mechanization/AtomicJl`](Mechanization/AtomicJl)
    has only the definitions and proofs of FullAtomicJl
    that concern the equivalence of declarative and reductive
    definitions of subtyping, without the connection to
    semantic subtyping.
