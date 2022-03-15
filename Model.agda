module Model where

open import Support

{-
Refactored so-as to allow for easier (more infomrative) proofs
Originally had
L : State → 𝑃 Atom
-}
record 𝑀 (Atom : Set) : Set₁ where
  field
    State : Set
    _⟶_ : rel State
    relSteps : relAlwaysSteps _⟶_
    L : State → Atom → Set
    -- L'' : Decidable L' -- Only Predicative?
