module SubFormula where

data atoms' : Set where
  p' : atoms'
  q' : atoms'

open import Syntax atoms'
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Empty renaming (⊥ to ⊥')
open import Relation.Nullary renaming (¬_ to ¬'_)

subFormula : ϕ → ϕ → Set
subFormula φ ψ = φ ≡ ψ ⊎ properSubFormula φ ψ
  where
    properSubFormula : ϕ → ϕ → Set
    properSubFormula φ (atom x) = ⊥'
    properSubFormula φ ⊥        = ⊥'
    properSubFormula φ ⊤        = ⊥'
    properSubFormula φ (¬ ψ)    = subFormula φ ψ
    properSubFormula φ (ψ ∨ ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ ∧ ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ ⇒ ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (X ψ)    = subFormula φ ψ
    properSubFormula φ (F ψ)    = subFormula φ ψ
    properSubFormula φ (G ψ)    = subFormula φ ψ
    properSubFormula φ (ψ U ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ W ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ R ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁

Gp' = G (atom p')
Gp'UGp' = Gp' U Gp'

Gp'⊂Gp'UGp' : subFormula Gp' Gp'UGp'
Gp'⊂Gp'UGp' = inj₂ (inj₁ (inj₁ refl))

p'⊂p' : subFormula (atom p') (atom p')
p'⊂p' = inj₁ refl

¬p'⊂q' : ¬' subFormula (atom p') (atom q')
¬p'⊂q' (inj₁ ())
¬p'⊂q' (inj₂ nah) = nah

¬Gp'UGp'⊂Gp' : ¬' subFormula Gp'UGp' Gp'
¬Gp'UGp'⊂Gp' (inj₂ (inj₁ ()))
¬Gp'UGp'⊂Gp' (inj₂ (inj₂ nah)) = nah
