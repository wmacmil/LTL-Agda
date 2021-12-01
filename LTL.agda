{-# OPTIONS --postfix-projections #-}

module LTL where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat
open import Data.Unit renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Sum
open import Relation.Nullary renaming (¬_ to ¬'_)
open import Data.Fin
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality

module Syntax (Atom : Set) where

  data ϕ : Set where
    -- atom     : Fin n → ϕ instantiate with module instead
    atom        : Atom → ϕ
    ⊥ ⊤         : ϕ
    ¬_          : ϕ → ϕ
    _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
    X F G       : ϕ → ϕ
    _U_ _W_ _R_ : ϕ → ϕ → ϕ

  -- isSubForm : ϕ → ϕ → Set
  -- isSubForm ψ phi = {!phi \!}

open Syntax

rel : Set → Set₁
rel s = s → s → Set

-- power set
𝑃 : Set → Set
𝑃 s = s → Bool

-- 𝑃 Bool has four member
-- for example, we encode the empty set as follows
empt : 𝑃 Bool
empt false = false
empt true = false

relAlwaysSteps : {S : Set} → rel S → Set
relAlwaysSteps {S} rₛ = ∀ (s : S) → Σ[ s' ∈ S ] (rₛ s s')

module Transition (Atom : Set) (State : Set) (_⟶_ : rel State) where

  record 𝑀 : Set where
    field
      relSteps : relAlwaysSteps _⟶_
      L : State → 𝑃 Atom

  record Stream : Set where
    coinductive
    constructor cons
    field
      hd : State
      tl : Stream

  open Stream

  nextState : Stream → State
  nextState s = hd (tl s)

  from-ithState : (i : ℕ) → Stream → Stream
  from-ithState zero x    = x
  from-ithState (suc i) x = from-ithState i (tl x)

  record streamAlwaysTransitions (stream : Stream) : Set where
    coinductive
    field
      headValid : hd stream ⟶ nextState stream
      tailValid : streamAlwaysTransitions (tl stream)

  record Path : Set where
    field
      infSeq         : Stream
      isTransitional : streamAlwaysTransitions infSeq

  open streamAlwaysTransitions
  open Path

  tailPath : Path → Path
  tailPath p .infSeq         = tl (infSeq p)
  tailPath p .isTransitional = tailValid (isTransitional p)

  _⊧_ : Path → ϕ Atom → Set
  π ⊧ ⊥        = ⊥'
  π ⊧ ⊤        = ⊤'
  π ⊧ atom x   = {!!}
  π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
  π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
  π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
  π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
  π ⊧ X ψ      = tailPath π ⊧ ψ
  π ⊧ F ψ      = {!!}
  π ⊧ G ψ      = {!!}
  π ⊧ (ψ U ψ₁) = {!!}
  π ⊧ (ψ W ψ₁) = {!!}
  π ⊧ (ψ R ψ₁) = {!!}
  -- open Stream
  -- record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
  --   coinductive
  --   field
  --     hd-≈ : hd xs ≡ hd ys
  --     tl-≈ : tl xs ≈ tl ys



module Example1 where

  data states : Set where
    s0 : states
    s1 : states
    s2 : states

  data atoms : Set where
    p : atoms
    q : atoms
    r : atoms

  data steps : rel states where
  -- data steps : states → states → Set where
    s0s1 : steps s0 s1
    s0s2 : steps s0 s2
    s1s0 : steps s1 s0
    s1s2 : steps s1 s2
    s2s2 : steps s2 s2

  steps-relAlwaysSteps : relAlwaysSteps steps
  steps-relAlwaysSteps s0 = s1 , s0s1
  steps-relAlwaysSteps s1 = s0 , s1s0
  steps-relAlwaysSteps s2 = s2 , s2s2

  l : states → 𝑃 atoms
  l s0 p = true
  l s0 q = true
  l s0 r = false
  l s1 p = false
  l s1 q = true
  l s1 r = true
  l s2 p = false
  l s2 q = false
  l s2 r = true

  open Transition atoms
  open 𝑀

  ex1IsTransitionSyst : 𝑀 states steps
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L        = l


-- character references
-- 𝑀 == \MiM
-- 𝑃 == \MiP
