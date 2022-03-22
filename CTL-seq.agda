{-# OPTIONS --postfix-projections #-}

module CTL-seq where

import CTL-syntax
open import Support
open import Model
open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat renaming (_≤_ to _≤'_ ; _<_ to _<'_ ; _+_ to _+'_)
open import Data.Unit renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Sum
open import Relation.Nullary renaming (¬_ to ¬'_)
open import Data.Fin
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)

module Transition (Atom : Set) (M : 𝑀 Atom) where
  open CTL-syntax Atom public
  open 𝑀 M
  alwaysSteps : (sₙ : ℕ → State) → Set
  alwaysSteps s = ∀ i → s i ⟶ s (suc i)

  record Path : Set where
    field
      infSeq         : ℕ → State
      isTransitional : alwaysSteps infSeq

  open Path

  headPath : Path → State
  headPath p = p .infSeq 0

  tailPath : Path → Path
  tailPath p .infSeq x = p .infSeq (suc x)
  tailPath p .isTransitional i = p .isTransitional (suc i)

  -- path-i == drop
  path-i : ℕ → Path → Path
  path-i n = nTimes n tailPath


module Models (Atom : Set) (M : 𝑀 Atom) where
  -- open CTL-syntax Atom
  open Transition Atom M


  mutual

    future : Path → ϕ → Set
    future π ψ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ

    global : Path → ϕ → Set
    global π ψ = ∀ i → (path-i i π) ⊧ ψ

    justUpTil : ℕ → Path → ϕ → Set
    justUpTil i π ψ = ∀ (j : ℕ) → j <' i → (path-i j π) ⊧ ψ

    upTil : ℕ → Path → ϕ → Set
    upTil i π ψ = ∀ (j : ℕ) → j ≤' i → (path-i j π) ⊧ ψ

    -- can rewrite with future in first clause
    justUntil : Path → ϕ → ϕ → Set
    justUntil π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × justUpTil i π ψ

    until : Path → ϕ → ϕ → Set
    until π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × upTil i π ψ


    -- _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set
    -- M ,, s ⊧ ϕ = ∀ (π : Path) → headPath π ≡ s → π ⊧ ϕ
    --   where open Transition Atom M hiding (ϕ)

    -- Definition 3.6
    _⊧_ : Path → ϕ → Set
    _⊧_ = {!!}
    -- π ⊧ ⊥        = ⊥'
    -- π ⊧ ⊤        = ⊤'
    -- π ⊧ atom p   = L (headPath π ) p
    -- π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
    -- π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
    -- π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
    -- π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
    -- π ⊧ X ψ      = tailPath π ⊧ ψ
    -- π ⊧ F ψ      = future π ψ
    -- π ⊧ G ψ      = global π ψ
    -- π ⊧ (ψ U ψ₁) = justUntil π ψ ψ₁
    -- π ⊧ (ψ W ψ₁) = justUntil π ψ ψ₁ ⊎ global π ψ
    -- π ⊧ (ψ R ψ₁) = until π ψ₁ ψ ⊎ global π ψ


