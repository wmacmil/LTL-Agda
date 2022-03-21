
module Syntax (Atom : Set) where
-- Think Atom =FinSet

data ϕ : Set where
  atom        : Atom → ϕ
  ⊥ ⊤         : ϕ
  ¬_          : ϕ → ϕ
  _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
  X F G       : ϕ → ϕ
  _U_ _W_ _R_ : ϕ → ϕ → ϕ

open import Relation.Binary.PropositionalEquality
open import Data.Sum

-- whats the easiest way to get away with this?
subFormula : ϕ → ϕ → Set
subFormula φ ψ = φ ≡ ψ ⊎ properSubFormula φ ψ
  where
    properSubFormula : ϕ → ϕ → Set
    properSubFormula φ (atom x) = {!!}
    properSubFormula φ ⊥ = {!!}
    properSubFormula φ ⊤ = {!!}
    properSubFormula φ (¬ ψ) = subFormula φ ψ
    properSubFormula φ (ψ ∨ ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ ∧ ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ ⇒ ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (X ψ) = subFormula φ ψ
    properSubFormula φ (F ψ) =  subFormula φ ψ
    properSubFormula φ (G ψ) =  subFormula φ ψ
    properSubFormula φ (ψ U ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ W ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
    properSubFormula φ (ψ R ψ₁) = subFormula φ ψ ⊎ subFormula φ ψ₁
