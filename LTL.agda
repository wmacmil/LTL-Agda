{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

module LTL where

import Syntax
open import Model
open import Function using (_∘_)
open import Support
open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat
open import Data.Unit renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Sum
open import Relation.Nullary renaming (¬_ to ¬'_)
open import Data.Fin
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality

module Transition (Atom : Set) (M : 𝑀 Atom) where
  open Syntax Atom public
  open 𝑀 M
  record Stream : Set where
    coinductive
    field
      hd : State
      tl : Stream

  open Stream

  nextState : Stream → State
  nextState = hd ∘ tl

  stream-i : ℕ → Stream → Stream
  stream-i n = nTimes n tl

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

  headPath : Path → State
  headPath x = hd (infSeq x)

  tailPath : Path → Path
  tailPath p .infSeq         = tl (infSeq p)
  tailPath p .isTransitional = tailValid (isTransitional p)

  path-i : ℕ → Path → Path
  path-i n = nTimes n tailPath

  record G-pf (ψ : Path → Set) (π : Path) : Set where
    coinductive
    field
      ∀-h : ψ π
      ∀-t : G-pf ψ (tailPath π)

  data F-pf (P : Path → Set) (σ : Path) : Set where
    ev-H : P σ → F-pf P σ
    ev-T : F-pf P (tailPath σ) -> F-pf P σ

  data U-Pf (P Q : Path → Set) (σ : Path) : Set where
    until-h : Q σ → (U-Pf P Q) σ
    until-t : P σ → (U-Pf P Q) (tailPath σ) → (U-Pf P Q) σ

  data Uincl-Pf (P Q : Path → Set) (σ : Path) : Set where
    untilI-h : P σ → Q σ → (Uincl-Pf P Q) σ
    untilI-t : P σ → (Uincl-Pf P Q) (tailPath σ) → (Uincl-Pf P Q) σ

  _⊧_ : Path → ϕ → Set
  π ⊧ ⊥        = ⊥'
  π ⊧ ⊤        = ⊤'
  π ⊧ atom x   = (L (headPath π) x)
  π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
  π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
  π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
  π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
  π ⊧ X ψ      = tailPath π ⊧ ψ
  π ⊧ F ψ      = F-pf (_⊧ ψ) π
  π ⊧ G ψ      = G-pf (_⊧ ψ) π
  -- π ⊧ G ψ      = ∀ (n : ℕ) → drop n π ⊧ ψ
  π ⊧ (ψ U ψ₁) = U-Pf (_⊧ ψ) (_⊧ ψ₁) π
  π ⊧ (ψ W ψ₁) = (U-Pf (_⊧ ψ) (_⊧ ψ₁) π) ⊎ G-pf (_⊧ ψ) π
  π ⊧ (ψ R ψ₁) = Uincl-Pf (_⊧ ψ₁) (_⊧ ψ) π ⊎ G-pf (_⊧ ψ) π

module Models (Atom : Set)  where

  open Syntax Atom

  --Definition 3.8
  _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set
  M ,, s ⊧ ϕ = ∀ (π : Path) → headPath π ≡ s → π ⊧ ϕ
    where open Transition Atom M hiding (ϕ)


module Example1' where

  open import Example1
  open Transition atoms ex1IsTransitionSyst
  open Path
  open Stream
  open streamAlwaysTransitions

  s2Stream : Stream
  s2Stream .hd = s2
  s2Stream .tl = s2Stream

  s2Transitions : streamAlwaysTransitions s2Stream
  s2Transitions .headValid = s2s2
  s2Transitions .tailValid = s2Transitions

  s2Path : Path
  s2Path .infSeq         = s2Stream
  s2Path .isTransitional = s2Transitions

  -- rightmost branch on computation tree
  pathRight : Path
  pathRight .infSeq .hd                = s0
  pathRight .infSeq .tl                = s2Path .infSeq
  pathRight .isTransitional .headValid = s0s2
  pathRight .isTransitional .tailValid = s2Path .isTransitional

  seqLEven : Stream
  seqLOdd  : Stream
  seqLEven .hd = s0
  seqLEven .tl = seqLOdd
  seqLOdd  .hd = s1
  seqLOdd  .tl = seqLEven

  transLEven : streamAlwaysTransitions seqLEven
  transLOdd  : streamAlwaysTransitions seqLOdd
  transLEven .headValid = s0s1
  transLEven .tailValid = transLOdd
  transLOdd  .headValid = s1s0
  transLOdd  .tailValid = transLEven

  pathLeft : Path
  pathLeft .infSeq = seqLEven
  pathLeft .isTransitional = transLEven

  open Models atoms

  ex-1 : M ,, s0 ⊧ (atom p ∧ atom q)
  ex-1 π init rewrite init = s0p , s0q

  ex-2 : M ,, s0 ⊧ (¬ (atom r))
  ex-2 π π0=s0 x with headPath π
  ex-2 π refl () | .s0

  ex-3 : M ,, s0 ⊧ ⊤
  ex-3 π init = tt

  ex-4 : M ,, s0 ⊧ X (atom r)
  ex-4 π π0=s0
    with headPath π | (hd (tl (infSeq π))) | headValid (isTransitional π)
  ex-4 π refl | .s0 | s1 | z = s1r
  ex-4 π refl | .s0 | s2 | z = s2r

  ex-5 : ¬' (M ,, s0 ⊧ X (atom q ∧ atom r))
  ex-5 x with x pathRight refl
  ex-5 x | () , s2r

  ex-6 : ∀ (s : states) → (M ,, s ⊧ G (¬ (atom p ∧ atom r)))
  ex-6 s0 π π0=s .G-pf.∀-h rewrite π0=s = λ {()}
  ex-6 s1 π π0=s .G-pf.∀-h rewrite π0=s = λ {()}
  ex-6 s2 π π0=s .G-pf.∀-h rewrite π0=s = λ {()}
  ex-6 s0 π π0=s .G-pf.∀-t = ex-6 (headPath (tailPath π)) (tailPath π) refl
  ex-6 s1 π π0=s .G-pf.∀-t = ex-6 (headPath (tailPath π)) (tailPath π) refl
  ex-6 s2 π π0=s .G-pf.∀-t = ex-6 (headPath (tailPath π)) (tailPath π) refl


  beginsWith-s2-always-s2 : ∀ p → headPath p ≡ s2 → headPath (tailPath p) ≡ s2
  beginsWith-s2-always-s2 π x
    with headPath π |  (hd (tl (infSeq π))) | headValid (isTransitional π)
  beginsWith-s2-always-s2 π refl | .s2 | s2 | a = refl

  ex-7 : M ,, s2 ⊧ G (atom r)
  ex-7 π init .G-pf.∀-h rewrite init = s2r
  ex-7 π init .G-pf.∀-t =
    ex-7
      (tailPath π)
      (beginsWith-s2-always-s2 π init)
      {- Ankas Solution
      (helper
        (headPath π)
        (hd (tl (infSeq π)))
        init
        (headValid (isTransitional π)))
      where
        helper : ∀ u w → u ≡ s2 → steps u w → w ≡ s2
        helper .s2 .s2 refl s2s2 = refl
      -}

  -- ex-9-i : pathLeft ⊧ (G (F (atom r)))
  -- ex-9-i .Transition.G-pf.∀-h = ev-T (ev-T {!!})
  -- ex-9-i .Transition.G-pf.∀-t = {!!}

  ex-6-i : ∀ (s : states) → (M ,, s ⊧ G (¬ (atom p ∧ atom r)))
  ex-6-i s0 π π0=s .G-pf.∀-h rewrite π0=s = λ { ()}
  ex-6-i s1 π π0=s .G-pf.∀-h rewrite π0=s = λ { ()}
  ex-6-i s2 π π0=s .G-pf.∀-h rewrite π0=s = λ { ()}
  ex-6-i s π π0=s .G-pf.∀-t = ex-6-i (headPath (tailPath π)) (tailPath π) refl
  -- ex-6 : (M ,, s0 ⊧ G (¬ (atom p ∧ atom r)))

  ¬q∧r⇒∀s2 : ∀ p → p ⊧ ((¬ (atom q)) ∧ atom r) → headPath p ≡ s2
  ¬q∧r⇒∀s2 π x
    with headPath π
  ¬q∧r⇒∀s2 π (fst , s1r) | .s1 = ⊥-elim (fst s1q)
  ¬q∧r⇒∀s2 π (fst , s2r) | .s2 = refl

  path-i-CommutesWithTailPath : ∀ π n → path-i (suc n) π ≡ tailPath (path-i n π)
  path-i-CommutesWithTailPath π n = sym (nTimesCommutesWith-f tailPath n π)

  ex-8-s2-lemma : (M ,, s2 ⊧ ((F (G (atom r)))))
  ex-8-s2-lemma π init =
    ev-H (ex-7 π init)

  -- move-future :
  --   ∀ π n ϕ →
  --   Transition.future atoms M (path-i n π) ϕ
  --   → Transition.future atoms M π ϕ

  ex-8-s2 : (M ,, s2 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
  ex-8-s2 π init x₁ = ev-H (ex-7 π init) --  let y = ex-8-s2-lemma in y π x
  -- something like const . ev-H . ex-y

  -- can we call one of the others as a lemma, like when it does start at s2
  -- ex-8-s0 : (M ,, s0 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
  -- ex-8-s0 π init
  --   with headPath π
  -- ex-8-s0 π refl | .s0 = λ {
  -- -- ex-8-s0 π init | headπ = λ {
  --   (Transition.ev-H x) → let x' = lemma π x in {!!} ; -- how to derive this contradiction?
  --   (Transition.ev-T x) → {!x!}} -- want to recursively call the ex-8-s0 case



