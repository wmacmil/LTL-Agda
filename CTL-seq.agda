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

  -- TODO : prove the along-path equivalent to the other formulations
  along-path : Path → State → Set
  along-path π s = ⊥' ⊎ Σ[ n ∈ ℕ ] state-i n π ≡ s

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
    M,-⊧ s (¬ φ)      = ¬' M,-⊧ s φ
    M,-⊧ s (φ ∨ φ₁)   = M,-⊧ s φ ⊎ M,-⊧ s φ₁
    M,-⊧ s (φ ∧ φ₁)   = M,-⊧ s φ × M,-⊧ s φ₁
    M,-⊧ s (φ ⇒ φ₁)   = M,-⊧ s φ → M,-⊧ s φ₁
    M,-⊧ s (EX φ)     = Σ[ s₁ ∈ State ] s ⟶ s₁ × M,-⊧ s₁ φ
    -- M,-⊧ s (EF φ)     = Σ[ π ∈ Path ] headPath π ≡ s × Σ[ n ∈ ℕ ] M,-⊧ (state-i n π) φ
    M,-⊧ s (EF φ)     = Σ[ π ∈ Path ] headPath π ≡ s × Σ[ sᵢ ∈ State ] (along-path π sᵢ ) × M,-⊧ sᵢ φ
    M,-⊧ s (EG φ)     = Σ[ π ∈ Path ] headPath π ≡ s × ∀ (n : ℕ) → M,-⊧ (state-i n π) φ
    M,-⊧ s (AX φ)     = ∀ (s₁ : State) → s ⟶ s₁ → (M,-⊧ s₁ φ)
    M,-⊧ s (AF φ)     = ∀ π → headPath π ≡ s → Σ[ n ∈ ℕ ] M,-⊧ (state-i n π) φ
    M,-⊧ s (AG φ)     = ∀ π → headPath π ≡ s → ∀ (n : ℕ) → M,-⊧ (state-i n π) φ
    M,-⊧ s (A φ U φ₁) = ∀ π → headPath π ≡ s → Σ[ i ∈ ℕ ] M,-⊧ (state-i i π) φ₁ × ∀ j → j <' i →  M,-⊧ (state-i j π) φ
    M,-⊧ s (E φ U φ₁) = Σ[ π ∈ Path ] headPath π ≡ s × Σ[ i ∈ ℕ ] M,-⊧ (state-i i π) φ₁ × ∀ j → j <' i →  M,-⊧ (state-i j π) φ

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

  ex-2 : M ,, s0 ⊧ (¬ (atom r))
  ex-2 ()

  ex-3 : M ,, s0 ⊧ ⊤
  ex-3 = tt

  ex-4 : M ,, s0 ⊧ EX (atom q ∧ atom r)
  ex-4 = s1 , (s0s1 , s1q , s1r)

  ex-5 : M ,, s0 ⊧ (¬ AX (atom q ∧ atom r))
  ex-5 x = let f = proj₁ (x s2 s0s2) in destroy f
    where
      destroy : l' s2 q → ⊥'
      destroy ()

  -- lemma
  -- ex-6' : ∀ s → M ,, s ⊧ (¬ (atom p ∧ atom r))
  -- ex-6' s0 ()
  -- ex-6' s1 ()
  -- ex-6' s2 ()

  -- needed to reforumalate definition of ⊧
  ex-6 : M ,, s0 ⊧ (¬ EF (atom p ∧ atom r))
  ex-6 (π , π0=s0 , s0 , ())
  ex-6 (π , π0=s0 , s1 , ())
  ex-6 (π , π0=s0 , s2 , ())

  -- lemma : r is always true on pathRight


  beginsWith-s2-always-s2 : (p : Path) → headPath p ≡ s2 → headPath (tailPath p) ≡ s2
  beginsWith-s2-always-s2 π x
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  beginsWith-s2-always-s2 π refl | .s2 | s2 | a = refl

  -- copied from ltl-Seq
  ex-7' : M ,, s2 ⊧ (AG (atom r))
  ex-7' π π0=s2 zero with headPath π
  ... | s2 = s2r
  ex-7' π π0=s2 (suc n) =
    ex-7'
      (tailPath π)
      (beginsWith-s2-always-s2 π π0=s2)
      n

  ex-7 : M ,, s2 ⊧ (EG (atom r))
  ex-7 =
    pathRightS2 ,
    refl ,
    ex-7' pathRightS2 refl

  -- why isn't agda able to infer this?
  ex-8 : M ,, s0 ⊧ (AF (atom r))
  ex-8 π init
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  ... | s0 | s1 | z = 1 , {!!}
  ... | s0 | s2 | z = 1 , {!!}

  ex-9 : M ,, s0 ⊧ (E ((atom p) ∧ (atom q)) U (atom r))
  ex-9 = pathRight , (refl , 1 , (s2r , λ { zero x → s0p , s0q ; (suc j) (s≤s ())}))

  -- same issue
  ex-10 : M ,, s0 ⊧ (A (atom p) U (atom r))
  ex-10 π init -- = 1 , ({!!} , {!!})
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  ex-10 π init | s0 | s1 | z = 1 , {!!} , (λ { zero (s≤s x) → {!!} ; (suc j) (s≤s ())})
  ex-10 π init | s0 | s2 | z = {!!}

  -- -- namely, the rightpath is always available
  -- ex-11 :  M ,, s0 ⊧ (AG (((atom p) ∨ ((atom q) ∨ (atom r))) ⇒ (EF (EG (atom r)))))
  -- ex-11 π init zero x₁ = pathRight , ({!refl!} , ({!!} , {!!}))
  -- ex-11 π init (suc n) x₁ = {!!}
  -- -- ex-11 π init n x₁ = pathRightS2 , ({!!} , {!!})
   
