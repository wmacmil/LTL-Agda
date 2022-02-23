\begin{code}[hide]
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

module introLTL where

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
\end{code}

\section{LTL in Agda}

We briefly introduce Linear Temporal Logic using Agda's syntax for the reader
unfamiliar with LTL, interactive theorem provers, or both. Although there is a
vast literature on the subject - theoretical, philosophical, and applied - over
a long historical arc spanning almost 70 years, we hope that introducing the
basic syntax and semantics in Agda will both validate our perspective as well as
add motivate a somewhat different perspective.

\subsection{Motivating LTL}

The primary ideas that we lean on are in motivating our development are :

\begin{itemize}
\item LTL is captures, at least to some degree, natural human intution. That is, we hope that the logic is a reflection of what most people do and how they reason in their every day lives.
\item LTL is decidable.
\item LTL can serve as template for more expressive or nuanced logical ideas.
\item LTL is expressive enough, for route and motion planning
\item There are large number of well engineered and established model checkers.
\end{itemize}

We believe that the modalities of quanitfying events in time with regards to
\emph{some future time} and \emph{forever} admit a mathematically coherent
theory in addition to offering philosophically interesting and practical
questions. Despite being more computationally complex than propisitional logic,
our application of for relatively simple route planning don't require
particularly large formulas, and so the complexity of ensuring proper
translations from natural language (in addition to other components) is of a
much bigger concern than computational complextiy.

The main idea of temporal logics is that events, which may be abstract or
grounded in reality, take place sequentially. Our everyday language captures
this with notions of before, after, in between, forever, later, until, and so-on
(pun intendend). The explicit type of order may be up to debate, as well as the
units by which time is measured, but LTL suppresses more complex notions of the
units by which time is kept as well as the possible worlds branches, a
simpifying assuption we'll accept for the time being.

We base this formalization off Huth \& Ryan's introductory account in \emph{LOGIC IN COMPUTER SCIENCE}

The syntax of LTL consists of atomic events (which should ideally be grounded to reality), the normal logical colletives, and


\begin{code}
  data ϕ : Set where
    -- atom     : Fin n → ϕ instantiate with module instead
    atom        : Atom → ϕ
    ⊥ ⊤         : ϕ
    ¬_          : ϕ → ϕ
    _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
    X F G       : ϕ → ϕ
    _U_ _W_ _R_ : ϕ → ϕ → ϕ
\end{code}


\begin{code}
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

record 𝑀 (Atom : Set) : Set₁ where
  field
    State : Set
    _⟶_ : rel State
    relSteps : relAlwaysSteps _⟶_
    -- L : State → 𝑃 Atom
    L : State → Atom → Set

module Transition (Atom : Set) (Model : 𝑀 Atom) where
  open Syntax Atom public
  open 𝑀 Model
  record Stream : Set where
    coinductive
    -- constructor cons
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

  headPath : Path → State
  headPath x = hd (infSeq x)

  tailPath : Path → Path
  tailPath p .infSeq         = tl (infSeq p)
  tailPath p .isTransitional = tailValid (isTransitional p)

  -- drop : ℕ → Path → Path
  -- drop 0 x = x
  -- drop (suc n) x = tailPath (drop n x)

  -- module _ (M : 𝑀) where
  --   open 𝑀 M

  record G-pf (ψ : Path → Set) (π : Path) : Set where
    coinductive
    field
      ∀-h : ψ π
      ∀-t : G-pf ψ (tailPath π)

  data F-pf (P : Path → Set) (σ : Path) : Set where
    ev_h : P σ → F-pf P σ
    ev_t : F-pf P (tailPath σ) -> F-pf P σ

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


module Model (Atom : Set)  where

  open Syntax Atom -- public

  --Definition 3.8
  _,,_⊧_ : (M : 𝑀 Atom) → (s : M .𝑀.State) → ϕ → Set
  M ,, s ⊧ ϕ = ∀ (π : Path) → headPath π ≡ s → π ⊧ ϕ
    where open Transition Atom M hiding (ϕ)


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

  data l' : states → atoms → Set where
    s0p : l' s0 p
    s0q : l' s0 q
    s1q : l' s1 q
    s1r : l' s1 r
    s2r : l' s2 r

  open 𝑀

  ex1IsTransitionSyst : 𝑀 atoms
  ex1IsTransitionSyst .State = states
  ex1IsTransitionSyst ._⟶_ = steps
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L = l'

  --abreviation
  M = ex1IsTransitionSyst

  open Transition atoms ex1IsTransitionSyst

  open Path
  open Stream
  open streamAlwaysTransitions

--   -- _◅_ : ∀ {i j k} (x : T i j) (xs : Star T j k) → Star T i k

  s2Stream : Stream
  s2Stream .hd = s2
  s2Stream .tl = s2Stream

  s2Transitions : streamAlwaysTransitions s2Stream
  s2Transitions .headValid = s2s2
  s2Transitions .tailValid = s2Transitions

  s2Path : Path
  s2Path .infSeq = s2Stream
  s2Path .isTransitional = s2Transitions

  -- rightmost branch on computation tree
  pathRight : Path
  pathRight .infSeq .hd = s0
  pathRight .infSeq .tl = s2Path .infSeq
  pathRight .isTransitional .headValid = s0s2
  pathRight .isTransitional .tailValid = s2Path .isTransitional

  seqLEven : Stream
  seqLOdd : Stream
  seqLEven .hd = s0
  seqLEven .tl = seqLOdd
  seqLOdd .hd = s1
  seqLOdd .tl = seqLEven

  transLEven : streamAlwaysTransitions seqLEven
  transLOdd : streamAlwaysTransitions seqLOdd
  transLEven .headValid = s0s1
  transLEven .tailValid = transLOdd
  transLOdd .headValid = s1s0
  transLOdd .tailValid = transLEven

  pathLeft : Path
  pathLeft .infSeq = seqLEven
  pathLeft .isTransitional = transLEven

  open Model atoms

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

  ex-7 : M ,, s2 ⊧ G (atom r)
  ex-7 π init
    with headPath π | (hd (tl (infSeq π))) | headValid (isTransitional π)
  ex-7 π refl | .s2 | s2 | s2s2 = record { ∀-h = {!!} ; ∀-t = ex-7 {!π!} {!!} }
    -- record {
    --   ∀-h = {!!} ;
    --   ∀-t = {!!} }
\end{code}




-- -- character references
-- -- 𝑀 == \MiM
-- -- 𝑃 == \MiP
