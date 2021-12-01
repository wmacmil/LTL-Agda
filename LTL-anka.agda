-- {-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality.Core

record Stream (A : Set) : Set where
  coinductive
  constructor cons
  field
    hd : A
    tl : Stream A

open Stream

record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
 coinductive
 field
   hd-≈ : hd xs ≡ hd ys
   tl-≈ : tl xs ≈ tl ys

module _ (State : Set) where

  stream : Set
  stream = Stream State

  -- Formula : Set₁
  Formula = stream -> Set

  X : Formula -> stream -> Set
  X P σ = P (tl σ)

  -- record □ (P : Formula) : Formula where
  record □ (P : Formula) (σ : stream) : Set where
    coinductive
    constructor C-always
    field
      always-h : P σ
      always-t : □ P (tl σ)

  open □

  -- data ◇ (P : Formula) (σ : stream) : Set where
  --   ev_h : P σ → ◇ P σ
  --   ev_t : P (tl σ) -> ◇ P σ
  data ◇ (P : Formula) : Formula where
    ev-h : ∀ σ → P σ → ◇ P σ
    ev-t : ∀ σ → P (tl σ) → ◇ P σ

  open ◇

  data _U_ (P Q : Formula) : Formula where
    until-h : ∀ σ → Q σ → (P U Q) σ
    -- until_t : ∀ s σ → P (cons s σ) → (P U Q) σ → (P U Q) (cons s σ)
    until-t : ∀ σ → P σ → (P U Q) (tl σ) → (P U Q) σ

  example : Formula → Formula
  example P = X (◇ (□ P))

  infinitely-often : Formula → Formula
  infinitely-often P = □ (◇ P)

  □-idempotent : ∀ P σ → □ P σ → □ (□ P) σ
  -- □-idempotent P σ x = C-always x (□-idempotent {!!} {!!} {!!})
  □-idempotent P σ x .always-h = x
  □-idempotent P σ x .always-t = □-idempotent P (tl σ) (always-t x)
