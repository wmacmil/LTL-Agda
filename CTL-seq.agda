{-# OPTIONS --postfix-projections #-}

module CTL-seq where

import CTL-syntax
open import Function
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

  state-i : ℕ → Path → State
  state-i n π = headPath (path-i n π)

module Models (Atom : Set)  where
  open CTL-syntax Atom
  -- open Path
  -- open Transition Atom M

  -- mutual

  module _ (M : 𝑀 Atom) where

    open Transition Atom M hiding (ϕ)
    open 𝑀 M

    M,-⊧ : (s : M .𝑀.State) → ϕ → Set
    M,-⊧ s (atom x)   = L s x
    M,-⊧ s ⊥          = ⊥'
    M,-⊧ s ⊤          = ⊤'
    M,-⊧ s (¬ φ)      = ¬' (M,-⊧ s φ)
    M,-⊧ s (φ ∨ φ₁)   = (M,-⊧ s φ) ⊎ (M,-⊧ s φ₁)
    M,-⊧ s (φ ∧ φ₁)   = (M,-⊧ s φ) × (M,-⊧ s φ₁)
    M,-⊧ s (φ ⇒ φ₁)   = (M,-⊧ s φ) → (M,-⊧ s φ₁)
    M,-⊧ s (EX φ)     = Σ[ s₁ ∈ State ] (s ⟶ s₁) × (M,-⊧ s₁ φ)
-- (M,-⊧ s₁ φ)
    M,-⊧ s (EF φ)     = {!!}
    M,-⊧ s (EG φ)     = {!!}
    M,-⊧ s (AX φ)     = ∀ (s₁ : State) → s ⟶ s₁ → (M,-⊧ s₁ φ)
    M,-⊧ s (AF φ)     = ∀ (π : Path) → headPath π ≡ s → Σ[ n ∈ ℕ ] (M,-⊧ (state-i n π) φ)
    M,-⊧ s (AG φ)     = ∀ (π : Path) → headPath π ≡ s → ∀ (n : ℕ) →  (M,-⊧ (state-i n π) φ)
    M,-⊧ s (A φ U φ₁) = ∀ (π : Path) → headPath π ≡ s → {!!}
    M,-⊧ s (E φ U φ₁) = {!!}


    -- justUpTil : ℕ → Path → ϕ → Set
    -- justUpTil i π ψ = ∀ (j : ℕ) → j <' i → (path-i j π) ⊧ ψ
    -- justUntil : Path → ϕ → ϕ → Set
    -- justUntil π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × justUpTil i π ψ
    -- _,,_⊧_
    -- _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set

  _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set
  _,,_⊧_ = M,-⊧


module Example1' where

  open import Example1

  open Transition atoms ex1IsTransitionSyst
  open Path

  pathRight : Path
  pathRight .infSeq zero            = s0
  pathRight .infSeq (suc i)         = s2
  pathRight .isTransitional zero    = s0s2
  pathRight .isTransitional (suc i) = s2s2

  pathLeft : Path
  pathLeft .infSeq zero                  = s0
  pathLeft .infSeq (suc zero)            = s1
  pathLeft .infSeq (suc (suc x))         = pathLeft .infSeq x
  pathLeft .isTransitional zero          = s0s1
  pathLeft .isTransitional (suc zero)    = s1s0
  pathLeft .isTransitional (suc (suc i)) = pathLeft .isTransitional i

  -- always-q-Left : pathLeft ⊧ (atom q)
  -- always-q-Left = s0q

  -- ¬always-r-Left : pathLeft ⊧ (atom r) → ⊥'
  -- ¬always-r-Left ()

  -- alwaysEventuallyR : pathLeft ⊧ G (F (atom r))
  -- alwaysEventuallyR zero          = 1 , s1r
  -- alwaysEventuallyR (suc zero)    = 0 , s1r
  -- alwaysEventuallyR (suc (suc i)) = alwaysEventuallyR i

  pathRightS2 : Path
  pathRightS2 .infSeq x         = s2
  pathRightS2 .isTransitional x = s2s2

  -- always-r-Right : pathRightS2 ⊧ G (atom r)
  -- always-r-Right zero    = s2r
  -- always-r-Right (suc x) = always-r-Right x

  open Models atoms

  ex-1 : M ,, s0 ⊧ (atom p ∧ atom q)
  ex-1 .proj₁ = s0p
  ex-1 .proj₂ = s0q

  -- M ,, s ⊧ atom x     = {!!}
  -- M ,, s ⊧ ⊥          = {!!}
  -- M ,, s ⊧ ⊤          = {!!}
  -- M ,, s ⊧ (¬ φ)      = {!!}
  -- M ,, s ⊧ (φ ∨ φ₁)   = {!!}
  -- M ,, s ⊧ (φ ∧ φ₁)   = {!!}
  -- M ,, s ⊧ (φ ⇒ φ₁)   = {!!}
  -- M ,, s ⊧ EX φ       = {!!}
  -- M ,, s ⊧ EF φ       = {!!}
  -- M ,, s ⊧ EG φ       = {!!}
  -- M ,, s ⊧ AX φ       = {!!}
  -- M ,, s ⊧ AF φ       = {!!}
  -- M ,, s ⊧ AG φ       = ∀ (π : Path) → headPath π ≡ s → ∀ (n : ℕ) →  (M ,, state-i n π  ⊧ φ)
  --   where open Transition Atom M hiding (ϕ)
  -- M ,, s ⊧ (A φ U φ₁) = {!!}
  -- M ,, s ⊧ (E φ U φ₁) = {!!}

    -- future : Path → ϕ → Set
    -- future π ψ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ

    -- global : Path → ϕ → Set
    -- global π ψ = ∀ i → (path-i i π) ⊧ ψ

    -- justUpTil : ℕ → Path → ϕ → Set
    -- justUpTil i π ψ = ∀ (j : ℕ) → j <' i → (path-i j π) ⊧ ψ

    -- upTil : ℕ → Path → ϕ → Set
    -- upTil i π ψ = ∀ (j : ℕ) → j ≤' i → (path-i j π) ⊧ ψ

    -- -- can rewrite with future in first clause
    -- justUntil : Path → ϕ → ϕ → Set
    -- justUntil π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × justUpTil i π ψ

    -- until : Path → ϕ → ϕ → Set
    -- until π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × upTil i π ψ



    -- -- Definition 3.6
    -- _⊧_ : Path → ϕ → Set
    -- _⊧_ = {!!}
    -- -- π ⊧ ⊥        = ⊥'
    -- -- π ⊧ ⊤        = ⊤'
    -- -- π ⊧ atom p   = L (headPath π ) p
    -- -- π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
    -- -- π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
    -- -- π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
    -- -- π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
    -- -- π ⊧ X ψ      = tailPath π ⊧ ψ
    -- -- π ⊧ F ψ      = future π ψ
    -- -- π ⊧ G ψ      = global π ψ
    -- -- π ⊧ (ψ U ψ₁) = justUntil π ψ ψ₁
    -- -- π ⊧ (ψ W ψ₁) = justUntil π ψ ψ₁ ⊎ global π ψ
    -- -- π ⊧ (ψ R ψ₁) = until π ψ₁ ψ ⊎ global π ψ
