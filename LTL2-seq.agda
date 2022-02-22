{-# OPTIONS --postfix-projections #-}

module LTL2-seq where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat renaming (_≤_ to _≤'_ ; _<_ to _<'_)
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


record 𝑀 (Atom : Set) (State : Set) : Set₁ where
  field
    _⟶_ : rel State
    relSteps : relAlwaysSteps _⟶_
    L : State → 𝑃 Atom

module Transition (Atom : Set) (State : Set) (Model : 𝑀 Atom State) where
  open Syntax Atom public
  open 𝑀 Model

  alwaysSteps : (sₙ : ℕ → State) → Set
  alwaysSteps s = ∀ i → s i ⟶ s (suc i)


  -- record Path : Set where
  --   field
  --     infSeq         : ℕ → State
  --     isTransitional : alwaysSteps infSeq

  record Path : Set where
    field
      initial : State
      infSeq         : ℕ → State
      initialSteps : initial ⟶ infSeq 0
      isTransitional : alwaysSteps infSeq

  open Path

  -- initialPath : Path → (s : State) → Σ[ s' ∈ State ] s ⟶ s' → Path -- need an accompanying proof that the state steps
  -- initialPath record { infSeq = infSeq ; isTransitional = isTransitional } state steps .Path.infSeq zero = state
  -- initialPath record { infSeq = infSeq ; isTransitional = isTransitional } x₁ steps .Path.infSeq (suc n) = infSeq n
  -- initialPath record { infSeq = infSeq ; isTransitional = isTransitional } x₁ steps .Path.isTransitional = λ i → {!!}

  headPath : Path → State
  headPath p = p .initial

  -- pathStartsAt : Path → State → Set
  -- pathStartsAt p s = (headPath p) ≡ s

  tailPath : Path → Path
  tailPath p .initial = p .infSeq 0
  tailPath p .infSeq x = p .infSeq (suc x)
  tailPath p .initialSteps = p .isTransitional 0
  tailPath p .isTransitional i = p .isTransitional (suc i)
  -- tailPath p .infSeq x = p .infSeq (suc x)
  -- tailPath p .isTransitional i = p .isTransitional (suc i)

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
    justUpTil i π ψ = (∀ (j : ℕ) → j <' i → (path-i j π) ⊧ ψ)

    upTil : ℕ → Path → ϕ → Set
    upTil i π ψ = (∀ (j : ℕ) → j ≤' i → (path-i j π) ⊧ ψ)

    -- can rewrite with future in first clause
    justUntil : Path → ϕ → ϕ → Set
    justUntil π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × justUpTil i π ψ

    until : Path → ϕ → ϕ → Set
    until π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × upTil i π ψ

    -- Definition 3.6
    _⊧_ : Path → ϕ → Set
    π ⊧ ⊥        = ⊥'
    π ⊧ ⊤        = ⊤'
    π ⊧ atom p   = T (L (headPath π ) p)
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

  -- a : 𝑀 Atom
  -- a = record { State = {!!} ; _⟶_ = {!!} ; relSteps = {!!} ; L = {!!} }

module Model (Atom : Set) (State : Set) where

  -- open Syntax Atom public
  open Transition Atom State

  --Definition 3.7
  _,⊧_ : (M : 𝑀 Atom State) → ϕ M → Set
  _,⊧_ M ψ = ∀ (p : Path M) → _⊧_ M p ψ

  -- -- M , s ⊧ ψ = ∀ (p : Path M) → (π : pathStartsAt M p s) → _⊧_ M p ψ
  -- M , s ⊧ ψ = ∀ (p : Path M) → _⊧_ M (p.infSeq 0) ψ

  -- _,_⊧'_ : (M : 𝑀 Atom State) → (p : Path M) → (headPath M p) → ϕ M → Set
  -- M , p ⊧' ψ = _⊧_ M p ψ
  -- -- M , s ⊧ ψ = ? -- ∀ (p : Path M) → (π : pathStartsAt M p s) → _⊧_ M p ψ
  --   -- where open M

  -- pathStartsAt
  -- record { State = State ; _⟶_ = _⟶_ ; relSteps = relSteps ; L = L } ,⊧ x = ∀ (s : State) → {!  !}
  -- M , s ⊧ ψ = {!M!}

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

  open 𝑀

  ex1IsTransitionSyst : 𝑀 atoms states
  -- ex1IsTransitionSyst .State = states
  ex1IsTransitionSyst ._⟶_ = steps
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L = l

  open Transition atoms states ex1IsTransitionSyst
  open Path

  -- rightmost and leftmost branches on computation tree

  pathRight : Path
  pathRight .initial = s0
  pathRight .infSeq i = s2
  pathRight .initialSteps = s0s2
  pathRight .isTransitional i = s2s2

  -- pathRight .infSeq zero = s0
  -- pathRight .infSeq (suc i) = s2
  -- pathRight .isTransitional zero = s0s2
  -- pathRight .isTransitional (suc i) = s2s2

-- extra work
  pathLeft : Path
  pathLeft .initial = s0
  pathLeft .infSeq zero = s1
  pathLeft .infSeq (suc zero) = s0
  pathLeft .infSeq (suc (suc i)) = pathLeft .infSeq i
  pathLeft .initialSteps = s0s1
  pathLeft .isTransitional zero = s1s0
  pathLeft .isTransitional (suc zero) = s0s1
  pathLeft .isTransitional (suc (suc i)) = pathLeft .isTransitional i

  -- pathLeft .infSeq zero = s0
  -- pathLeft .infSeq (suc zero) = s1
  -- pathLeft .infSeq (suc (suc x)) = pathLeft .infSeq x
  -- pathLeft .isTransitional zero = s0s1
  -- pathLeft .isTransitional (suc zero) = s1s0
  -- pathLeft .isTransitional (suc (suc i)) = pathLeft .isTransitional i


  -- allPathsStartAt-s0 : (p' : Path) → pathStartsAt p' s0
  -- allPathsStartAt-s0 record { infSeq = infSeq ; isTransitional = isTransitional } = {!refl  !}


  always-q-0 : ∀ (path : Path) → (path .initial ≡ s0) → path ⊧ (atom q)
  always-q-0 record { initial = s0 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } x = tt

  always-q-1 : ∀ (path : Path) → (path .initial ≡ s0) → (path ⊧ ((atom q) ∧ (atom r)) → ⊥')
  always-q-1 record { initial = s0 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } x ()

  --can also quantify over initial state
  -- r comes after p

  --idea of goesRight?

  always-q-2 : ∀ (path : Path) → (path .initial ≡ s0) → path ⊧ F (atom r) → (path .infSeq) ≡ (pathRight .infSeq)
  always-q-2 record { initial = .s0 ; infSeq = infSeq₁ ; initialSteps = initialSteps₁ ; isTransitional = isTransitional₁ } refl y = {!!} -- but then we know that infSeq₁ of i is always s2, how do we say this

  -- -- extensionality would come in handy
  -- always-q-2 : ∀ (path : Path) → (path .initial ≡ s0) → path ⊧ G (F (atom p)) → path ≡ pathLeft
  -- always-q-2 path isS0 y = {!!}

  -- always-q-2 : ∀ (path : Path) → (path .initial ≡ s0) → path ⊧ ((G (F (atom p))) ⇒ (G (F (atom r))))

  -- always-q-2 record { initial = s0 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } refl y zero = 1 , {!y!}
  -- always-q-2 record { initial = s0 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } refl x₁ (suc i) = {!!}

  -- always-q-0 record { initial = s0 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } = tt
  -- always-q-0 record { initial = s1 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } = {!!}
  -- always-q-0 record { initial = s2 ; infSeq = infSeq ; initialSteps = initialSteps ; isTransitional = isTransitional } = {!!}

  always-q-Left : pathLeft ⊧ (atom q)
  always-q-Left = tt

  ¬always-r-Left : pathLeft ⊧ (atom r) → ⊥'
  ¬always-r-Left ()

  alwaysEventuallyR : pathLeft ⊧ G (F (atom r))
  alwaysEventuallyR zero = 1 , tt
  alwaysEventuallyR (suc zero) = 0 , tt
  alwaysEventuallyR (suc (suc i)) = alwaysEventuallyR i


  -- oneLem : _⊧_ ex1IsTransitionSyst s0 ((atom p) ∧ (atom q))

  open Model atoms states

  -- one : ex1IsTransitionSyst ,⊧ ((atom p) ∧ (atom q))
  -- one = λ p₁ → {!!} , {!!} 


  -- -- one : ex1IsTransitionSyst , s0 ⊧ (p ∧ q)
  -- one : _,_⊧'_ ex1IsTransitionSyst {!!} ((atom p) ∧ (atom q))
  -- one = {!!}

  -- one : _,_⊧_ ex1IsTransitionSyst s0 ((atom p) ∧ (atom q))
  -- one M π = {!cong!} , {!!}
  --   where
  --     lemma : T (l (Transition.headPath _ _ _ M) p)
  --     lemma = {!!}

  -- ex1IsTransitionSyst

-- character references
-- <spc> h d c -- help describe character
-- 𝑀 == \MiM
-- 𝑃 == \MiP
