# LTL-Agda

Implementation based off Huth &amp; Ryan's LOGIC IN COMPUTER SCIENCE. We are trying stay as close to the source text as possible. 

The two deep embeddings, based of the same syntax (which should be refactored and modularized) 

# LTL.agda : represents paths (infinite series of states) as streams following [the paper](https://ieeexplore.ieee.org/document/8133459)  "An Axiomatization of Linear Temporal Logic in the Calculus of Inductive Constructions", by Solange Coupet-Grimal.
# LTL-seq.agda : represents paths as functions from natural numbers, taken as the more classically oriented thinker, and possibly intuitive 
# LTL-anka.agda : Sahllow embeddding that has mostly been merged in LTL, should possibly be discarded 

TODO : 

# Complete definitions, particularly with respect to quantifying over models and examples
# Prove equivalence of two definitions
# Link to some external SMT solver
# Prove decidability
# Extend to other temporal logics (most immediately probably Signal Temporal Logic (STL) 
