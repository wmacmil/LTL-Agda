module Support where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_≤_ to _≤'_ ; _<_ to _<'_ ; _+_ to _+'_)
open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)

-- -- power set
𝑃 : Set → Set
𝑃 s = s → Bool

-- 𝑃 Bool has four member, we encode the empty set as follows
empt : 𝑃 Bool
empt false = false
empt true = false


nTimes : {A : Set} → ℕ → (A → A) → (A → A)
nTimes zero f = id
nTimes (suc n) f a = nTimes n f (f a)

nTimesCommutesWith-f : {A : Set} → ∀ f n → (a : A) → f (nTimes n f a) ≡ nTimes n f (f a)
nTimesCommutesWith-f f zero a    = refl
nTimesCommutesWith-f f (suc n) a = nTimesCommutesWith-f f n (f a)

module QuantifierLaws where

open import Data.Sum
open import Data.Empty
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary

variable
  X : Set
  P : X → Set

--not constructively valid
postulate
  one : ¬ ((x : X) → P x) → Σ[ x ∈ X ] ¬ (P x)
-- one ¬Px = {!!} , {!!}

two : Σ[ x ∈ X ] ¬ (P x) → ¬ ((x : X) → P x)
two (x , negPx) Px = negPx (Px x)

three : ¬ (Σ[ x ∈ X ] (P x)) → (x : X) → ¬ P x
three ¬xPx x Px = ¬xPx (x , Px)

four : ((x : X) → ¬ P x) → ¬ (Σ[ x ∈ X ] (P x))
four ∀x¬Px (x' , Px') = ∀x¬Px x' Px'

em-irrefutable : ¬ ¬ (X ⊎ ¬ X)
em-irrefutable f = f (inj₂ (λ x → f (inj₁ x)))
