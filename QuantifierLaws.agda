module QuantifierLaws where

open import Data.Sum
open import Data.Empty
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary

variable
  X : Set
  P : X → Set

-- --not constructively valid
-- one : ¬ ((x : X) → P x) → Σ[ x ∈ X ] ¬ (P x)
-- one ¬Px = {!!} , {!!}

two : Σ[ x ∈ X ] ¬ (P x) → ¬ ((x : X) → P x)
two (x , negPx) Px = negPx (Px x)

three : ¬ (Σ[ x ∈ X ] (P x)) → (x : X) → ¬ P x
three ¬xPx x Px = ¬xPx (x , Px)

four : ((x : X) → ¬ P x) → ¬ (Σ[ x ∈ X ] (P x))
four ∀x¬Px (x' , Px') = ∀x¬Px x' Px'

em-irrefutable : ¬ ¬ (X ⊎ ¬ X)
em-irrefutable f = f (inj₂ (λ x → f (inj₁ x)))
