module Model where

open import Support

{-
Refactored so-as to allow for easier (more infomrative) proofs
Originally had
L : State â ð Atom
-}
record ð (Atom : Set) : Setâ where
  field
    State : Set
    _â¶_ : rel State
    relSteps : relAlwaysSteps _â¶_
    L : State â Atom â Set
    -- L'' : Decidable L' -- Only Predicative?
