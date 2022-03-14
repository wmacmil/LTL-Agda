{-# OPTIONS --postfix-projections #-}

module LTL-seq where

open import Support
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

module Syntax (Atom : Set) where
-- Think Atom =FinSet

  data ϕ : Set where
    atom        : Atom → ϕ
    ⊥ ⊤         : ϕ
    ¬_          : ϕ → ϕ
    _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
    X F G       : ϕ → ϕ
    _U_ _W_ _R_ : ϕ → ϕ → ϕ

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
  path-i n = nTimes n tailPath

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


module Model (Atom : Set) where
  open Syntax Atom
  --Definition 3.8

  _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set
  M ,, s ⊧ ϕ = ∀ (π : Path) → headPath π ≡ s → π ⊧ ϕ
    where open Transition Atom M hiding (ϕ)

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
  -- boolean blind
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
  ex1IsTransitionSyst .State    = states
  ex1IsTransitionSyst ._⟶_      = steps
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L        = l'
  -- ex1IsTransitionSyst .L''   = l''

  M = ex1IsTransitionSyst

  open Transition atoms ex1IsTransitionSyst
  open Path

  -- rightmost and leftmost branches on computation tree
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
  ex-4 π refl | .s0 | s1 | x = s1r
  ex-4 π refl | .s0 | s2 | x = s2r

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

  -- special case for real example, (M ,, s0 ⊧ G (¬ (atom p ∧ atom r)))
  ex-6 : ∀ (s : states) → (M ,, s ⊧ G (¬ (atom p ∧ atom r)))
  ex-6 s0 π π0=s 0 rewrite π0=s = λ { ()}
  ex-6 s1 π π0=s 0 rewrite π0=s = λ { ()}
  ex-6 s2 π π0=s 0 rewrite π0=s = λ { ()}
  ex-6 s0 π π0=s (suc n) = ex-6 (headPath (tailPath π)) (tailPath π) refl n
  ex-6 s1 π π0=s (suc n) = ex-6 (headPath (tailPath π)) (tailPath π) refl n
  ex-6 s2 π π0=s (suc n) = ex-6 (headPath (tailPath π)) (tailPath π) refl n

  beginsWith-s2-always-s2 : (p : Path) → headPath p ≡ s2 → headPath (tailPath p) ≡ s2
  beginsWith-s2-always-s2 π x
    with headPath π | (π .infSeq 1) | (π .isTransitional 0)
  beginsWith-s2-always-s2 π refl | .s2 | s2 | a = refl

  ex-7 : M ,, s2 ⊧ G (atom r)
  ex-7 π π0=s0 zero with headPath π
  ex-7 π refl zero | .s2 = s2r
  ex-7 π init (suc n) =
    ex-7
      (tailPath π)
      (beginsWith-s2-always-s2 π init)
      n

  ¬q∧r⇒∀s2 : ∀ p → p ⊧ ((¬ (atom q)) ∧ atom r) → headPath p ≡ s2
  ¬q∧r⇒∀s2 π x
    with headPath π
  ¬q∧r⇒∀s2 π (fst , s1r) | .s1 = ⊥-elim (fst s1q)
  ¬q∧r⇒∀s2 π (fst , s2r) | .s2 = refl

  path-i-CommutesWithTailPath : ∀ π n → path-i (suc n) π ≡ tailPath (path-i n π)
  path-i-CommutesWithTailPath π n = sym (nTimesCommutesWith-f tailPath n π)

  move-future : ∀ π n ϕ →
                Transition.future atoms M (path-i n π) ϕ
              → Transition.future atoms M π ϕ
  move-future π zero ϕ₁ (m , n-pf) = m , n-pf
  move-future π (suc n) ϕ₁ (m , n-pf) =
    move-future π n ϕ₁
      (suc m ,
      subst
        (λ x → nTimes m tailPath x ⊧ ϕ₁)
        (path-i-CommutesWithTailPath π n )
        n-pf)

  ex-8 :
    (s : states) → (M ,, s ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
  ex-8 s π init (n , n-cond) =
    let π' = path-i n π in
    move-future π n (G (atom r)) (ex-8-s2 π' (¬q∧r⇒∀s2 π' n-cond) (0 , n-cond))
      where
        ex-8-s2 : (M ,, s2 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
        ex-8-s2 π init x₁ = 0 , (ex-7 π init)

  ex-9-ii : pathLeft ⊧ (G (F (atom p)))
  ex-9-ii zero = 0 , s0p
  ex-9-ii (suc zero) = 1 , s0p
  ex-9-ii (suc (suc n)) = ex-9-ii n

  -- ex-9-iii : ¬' (pathRight ⊧ ((G (F (atom p)))))
  -- ex-9-iii f = ⊥-elim {!f!}
  -- -- ex-9-iii : pathRight ⊧ (¬ (G (F (atom p))))
  -- -- ex-9-iii n with (pathLeft .infSeq 0) | (pathLeft .isTransitional 0)
  -- -- ex-9-iii n | s0 | s0s1 = ⊥-elim {!n!}

  -- in fact, this is the instance of a more general lemma
  -- for any formula φ, G φ ⇒ G (F (φ)), it is used in the above proof as well
  ex-10-s2 : (M ,, s2 ⊧ (G (F (atom r))))
  ex-10-s2 π x i = 0 , ex-7 π x i

  ex-10 : ∀ (s : states) → (M ,, s ⊧ (G (F (atom r))))
  ex-10 s0 π π0=s zero
    rewrite π0=s           = 1 , ex-4 π π0=s
  ex-10 s1 π π0=s zero
    rewrite π0=s           = 0 , subst (λ x → l' x r) (sym π0=s) s1r
  ex-10 s2 π π0=s zero     = ex-10-s2 π π0=s 0
  ex-10 s0 π π0=s (suc n)  = ex-10 (headPath (tailPath π)) (tailPath π) refl n
  ex-10 s1 π π0=s (suc n)  = ex-10 (headPath (tailPath π)) (tailPath π) refl n
  ex-10 s2 π π0=s (suc n)  = ex-10-s2 π π0=s (suc n)

  weakenFormula : ∀ s φ ψ → M ,, s ⊧ ψ → M ,, s ⊧ (φ ⇒ ψ)
  weakenFormula s φ ψ ψTrue π init pf = ψTrue π init

  ex-10-coro-s0 : M ,, s0 ⊧ (G (F (atom p)) ⇒ (G (F (atom r))))
  ex-10-coro-s0 = weakenFormula s0 (G (F (atom p))) (G (F (atom r))) (ex-10 s0)

module Equivalences (Atom : Set) (Model : 𝑀 Atom) where
  open Transition Atom Model

  _⇛_ : {Path} → ϕ → ϕ → Set
  _⇛_ {π} ϕ ψ = π ⊧ ϕ → π ⊧ ψ

  _⇚_ : {Path} → ϕ → ϕ → Set
  _⇚_ {π} ϕ ψ = _⇛_ {π} ψ ϕ

  _≣_ : {Path} → ϕ → ϕ → Set
  _≣_ {π} ϕ ψ = (_⇛_ {π} ϕ ψ) × (_⇚_ {π} ϕ ψ)

  -- only true classically
  postulate
    le : {π : Path} {φ : ϕ} → _⇛_ {π} (¬ (G φ)) (F (¬ φ))

  -- The textbook doesn't used constructive logic
  -- We should really see this as (and refactor it too) via the quantifier
  -- laws
  negGF : {π : Path} → (φ : ϕ) →  _≣_ {π} (¬ (G φ)) (F (¬ φ))
  negGF {pi} φ = le {pi} {φ} , ri φ
    where
      ri : {π : Path} (φ : ϕ) → _⇚_ {π} (¬ (G φ)) (F (¬ φ))
      ri ϕ (n , ¬nthPi⊧φ) Gφ = ¬nthPi⊧φ (Gφ n)

  negFG : {π : Path} → (φ : ϕ) →  _≣_ {π} (¬ (F φ)) (G (¬ φ))
  negFG {pi} φ = le' , ri'
    where
      le' : _⇛_ {pi} (¬ (F φ)) (G (¬ φ))
      le' ¬Fφ n later-φ = ¬Fφ (n , later-φ)
      ri' : _⇚_ {pi} (¬ (F φ)) (G (¬ φ))
      ri' G¬phi (fst , snd) = G¬phi fst snd

-- character references
-- <spc> h d c -- help describe character
-- 𝑀 == \MiM
-- 𝑃 == \MiP
-- ⇛ == \Rrightarrow
-- gx% twice to flip
