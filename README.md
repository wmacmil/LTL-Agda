# LTL-Agda

Implementation based off Huth &amp; Ryan's LOGIC IN COMPUTER SCIENCE. We are trying stay as close to the source text as possible. 

There are two deep embeddings, based of the same syntax (which should be refactored and modularized) to maximize readibility and miminize code redundancy.

* LTL.agda : represents paths (infinite series of states) as streams following [the paper](https://ieeexplore.ieee.org/document/8133459)  "An Axiomatization of Linear Temporal Logic in the Calculus of Inductive Constructions", by Solange Coupet-Grimal.
* LTL-seq.agda : represents paths as functions from natural numbers, taken as the more classically oriented thinker, and possibly intuitive 
* LTL-anka.agda : Sahllow embeddding that has mostly been merged in LTL, should possibly be discarded 

TODO : 

* Complete definitions, particularly with respect to quantifying over models and examples
* Prove equivalence of two definitions of paths
* Link to some external SMT solver
* Prove decidability
* Extend to other temporal logics (most immediately probably Signal Temporal Logic (STL))

Helpful :
-- character references
-- <spc> h d c -- help describe character
-- 𝑀 == \MiM
-- 𝑃 == \MiP
-- ⇛ == \Rrightarrow
-- gx% twice to flip
