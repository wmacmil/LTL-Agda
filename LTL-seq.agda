{-# OPTIONS --postfix-projections #-}

module LTL-seq where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.Unit renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Sum
open import Relation.Nullary renaming (¬_ to ¬'_)
open import Data.Fin
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)

module Syntax (Atom : Set) where

  data ϕ : Set where
    -- atom     : Fin n → ϕ instantiate with module instead
    atom        : Atom → ϕ
    ⊥ ⊤         : ϕ
    ¬_          : ϕ → ϕ
    _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
    X F G       : ϕ → ϕ
    _U_ _W_ _R_ : ϕ → ϕ → ϕ

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


{-
Refactored so-as to allow for easier (more infomrative) proofs
Originally had
  L : State → 𝑃 Atom
-}
record 𝑀 (Atom : Set) : Set₁ where
  field
    State : Set
    _⟶_ : rel State
    relSteps : relAlwaysSteps _⟶_
    L : State → Atom → Set
    -- L'' : Decidable L' -- Only Predicative?

module Transition (Atom : Set) (Model : 𝑀 Atom) where
  open Syntax Atom public
  open 𝑀 Model

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
  path-i zero p = p
  path-i (suc i) p = path-i i (tailPath p)

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

    -- Definition 3.6
    _⊧_ : Path → ϕ → Set
    π ⊧ ⊥        = ⊥'
    π ⊧ ⊤        = ⊤'
    -- π ⊧ atom p   = T (L (headPath π ) p)
    π ⊧ atom p   = L (headPath π ) p
    π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
    π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
    π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
    π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
    π ⊧ X ψ      = tailPath π ⊧ ψ
    π ⊧ F ψ      = future π ψ
    π ⊧ G ψ      = global π ψ
    π ⊧ (ψ U ψ₁) = justUntil π ψ ψ₁
    π ⊧ (ψ W ψ₁) = justUntil π ψ ψ₁ ⊎ global π ψ
    π ⊧ (ψ R ψ₁) = until π ψ₁ ψ ⊎ global π ψ


    -- for defining equivalence

    _⇛_ : {Path} → ϕ → ϕ → Set
    _⇛_ {π} ϕ ψ = π ⊧ ϕ → π ⊧ ψ

    _⇚_ : {Path} → ϕ → ϕ → Set
    _⇚_ {π} ϕ ψ = _⇛_ {π} ψ ϕ

    _≣_ : {Path} → ϕ → ϕ → Set
    _≣_ {π} ϕ ψ = (_⇛_ {π} ϕ ψ) × (_⇚_ {π} ϕ ψ)

    -- The textbook doesn't used constructive logic
    -- We should really see this as (and refactor it too) via the quantifier
    -- laws
    -- negGF : {π : Path} → (φ : ϕ) →  _≣_ {π} (¬ (G φ)) (F (¬ φ))
    -- negGF {pi} φ = le , ri
    --   where
    --     le : _⇛_ {pi} (¬ (G φ)) (F (¬ φ))
    --     le x = {!!} , {!!} -- not provable

    ri : {π : Path} (φ : ϕ) → _⇚_ {π} (¬ (G φ)) (F (¬ φ))
    ri ϕ (n , ¬nthPi⊧φ) Gφ = ¬nthPi⊧φ (Gφ n)

    negFG : {π : Path} → (φ : ϕ) →  _≣_ {π} (¬ (F φ)) (G (¬ φ))
    negFG {pi} φ = le , ri'
      where
        le : _⇛_ {pi} (¬ (F φ)) (G (¬ φ))
        le ¬Fφ n later-φ = ¬Fφ (n , later-φ)
        ri' : _⇚_ {pi} (¬ (F φ)) (G (¬ φ))
        ri' G¬phi (fst , snd) = G¬phi fst snd



module Model (Atom : Set) where

  open Syntax Atom -- public

  --Definition 3.8
  _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set
  M ,, s ⊧ ϕ = ∀ (π : Path) → headPath π ≡ s → π ⊧ ϕ
    where open Transition Atom M hiding (ϕ)

  -- _⇛_ : (M : 𝑀 Atom) → Transition.Path → ϕ → ϕ → Set
  -- _⇛_ M ϕ = ?
  --   where open Transition Atom M hiding (ϕ; Path)

{-
Taken from Figure 3.3
Defined on page 178
-}
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

  -- To conform with our power-set definition
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

  data l' : states → atoms → Set where
    s0p : l' s0 p
    s0q : l' s0 q
    s1q : l' s1 q
    s1r : l' s1 r
    s2r : l' s2 r

  l'' : Decidable l'
  l'' s0 p = yes s0p
  l'' s0 q = yes s0q
  l'' s0 r = no (λ ())
  l'' s1 p = no (λ ())
  l'' s1 q = yes s1q
  l'' s1 r = yes s1r
  l'' s2 p = no (λ ())
  l'' s2 q = no (λ ())
  l'' s2 r = yes s2r

  open 𝑀

  ex1IsTransitionSyst : 𝑀 atoms
  ex1IsTransitionSyst .State = states
  ex1IsTransitionSyst ._⟶_ = steps
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L = l'
  -- ex1IsTransitionSyst .L'' = l''

  M = ex1IsTransitionSyst

  open Transition atoms ex1IsTransitionSyst
  open Path

  -- rightmost and leftmost branches on computation tree
  pathRight : Path
  pathRight .infSeq zero = s0
  pathRight .infSeq (suc i) = s2
  pathRight .isTransitional zero = s0s2
  pathRight .isTransitional (suc i) = s2s2

  pathLeft : Path
  pathLeft .infSeq zero = s0
  pathLeft .infSeq (suc zero) = s1
  pathLeft .infSeq (suc (suc x)) = pathLeft .infSeq x
  pathLeft .isTransitional zero = s0s1
  pathLeft .isTransitional (suc zero) = s1s0
  pathLeft .isTransitional (suc (suc i)) = pathLeft .isTransitional i

  always-q-Left : pathLeft ⊧ (atom q)
  always-q-Left = s0q

  ¬always-r-Left : pathLeft ⊧ (atom r) → ⊥'
  ¬always-r-Left ()

  alwaysEventuallyR : pathLeft ⊧ G (F (atom r))
  alwaysEventuallyR zero = 1 , s1r
  alwaysEventuallyR (suc zero) = 0 , s1r
  alwaysEventuallyR (suc (suc i)) = alwaysEventuallyR i

  pathRightS2 : Path
  pathRightS2 .infSeq x = s2
  pathRightS2 .isTransitional x = s2s2

  always-r-Right : pathRightS2 ⊧ G (atom r)
  always-r-Right zero = s2r
  always-r-Right (suc x) = always-r-Right x

  open Model atoms

  ex-1 : M ,, s0 ⊧ (atom p ∧ atom q)
  ex-1 π π0=s0 rewrite π0=s0 = s0p , s0q

  ex-2 : M ,, s0 ⊧ (¬ (atom r))
  ex-2 π π0=s0 x with headPath π
  ex-2 π refl () | .s0

  ex-3 : M ,, s0 ⊧ ⊤
  ex-3 π init = tt

  ex-4 : M ,, s0 ⊧ X (atom r)
  ex-4 π π0=s0
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  ex-4 π refl | .s0 | y | z = {!z!}
  -- ex-4 π refl | .s0 | s1 | x = s1r
  -- ex-4 π refl | .s0 | s2 | x = s2r

  {-
  Can alternatively interpret the negation inside the formula
  ex-5 : M ,, s0 ⊧ (¬ (X (atom q ∧ atom r)))
  ex-5 π π0=s0 p'
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  ex-5 π refl (s1q , s1r) | .s0 | s1 | x = {!!}
  ex-5 π refl () | .s0 | s2 | x
  -}
  ex-5 : ¬' (M ,, s0 ⊧ X (atom q ∧ atom r))
  ex-5 x with x pathRight refl
  ex-5 x | () , s2r

  -- -- why?
  -- -- the left path clearly has no state with both, since its only s0s and s1s
  -- -- any s2 has only r
  -- ex-6 : (M ,, s0 ⊧ G (¬ (atom p ∧ atom r)))
  -- ex-6 π π0=s0 n p'

  -- How to use the inductive Hypothesis
  ex-7 : M ,, s2 ⊧ G (atom r)
  ex-7 π π0=s0 zero with headPath π
  ex-7 π refl zero | .s2 = s2r
  ex-7 π π0=s0 (suc n) with headPath π
  ex-7 π init (suc n) | x = {!ex-7 π ? n!}



  -- below is Warrick trying to understand how to get at example 7

  -- that the path repeats itself
  lemma0 : (p : Path) → headPath p ≡ s2 → headPath (tailPath p) ≡ s2
  lemma0 π x
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  lemma0 π refl | .s2 | s2 | a = refl

  -- how can we avoid introducing all relevant info into the context
  lemma01 : (p : Path) → headPath p ≡ s2 → headPath (path-i 2 p) ≡ s2
  lemma01 π x
    with headPath π | (π .infSeq 1) | (π .isTransitional 0) | (π .infSeq 2) | (π .isTransitional 1)
  lemma01 π refl | .s2 | s2 | s2s2 | s2 | y0 = refl

  lemmaLemma' : (path : Path) (n : ℕ) → (path-i 100 path .infSeq 0) ≡ (path .infSeq 100)
  lemmaLemma' path n = refl

  -- how to prove this? is this a relevant lemma, really?
  -- it shouldn't relatively simple, but also
  lemmaLemma : (path : Path) (n : ℕ) → (path-i n path .infSeq 0) ≡ (path .infSeq n)
  lemmaLemma path zero = refl
  lemmaLemma path (suc n) = {!!}
    where
    -- ih : path-i n path .infSeq 0 ≡ path .infSeq n
      ih = lemmaLemma path n

  -- path-i : ℕ → Path → Path
  -- this seems like the canonical piece of information needed for exercise 7
  lemmai : (p : Path) → headPath p ≡ s2 → (i : ℕ) → headPath (path-i i p) ≡ s2
  lemmai π init zero with headPath π
  lemmai π refl zero | .s2 = refl
  lemmai π init (suc n)
    with headPath π | (path-i n (tailPath π) .infSeq 0) | (path-i n (tailPath π) .isTransitional 0)
  lemmai π refl (suc n) | .s2 | x | y = {!x!}

  -- lemmai π x n
  --   with headPath π
  -- -- with headPath path | path Path.infSeq 1
  -- lemmai π refl zero | .s2 = {!!}
  -- lemmai π refl (suc n) | .s2 = {!!}

-- character references
-- <spc> h d c -- help describe character
-- 𝑀 == \MiM
-- 𝑃 == \MiP
-- ⇛ == \Rrightarrow
-- gx% twice to flip
