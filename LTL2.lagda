\begin{code}[hide]
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

module LTL2 where

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
questions. Despite having higher computational complexity than propisitional logic,
our application of for relatively simple route planning don't require
particularly large formulas, and so the complexity of ensuring proper
translations from natural language (in addition to other components) is of a
much bigger concern than computational complextiy.

The main idea of temporal logics is that events, which may be abstract or
grounded in reality, take place sequentially. Our everyday language captures
this with notions of before, after, between, forever, later, until, and so-on
(pun intendend). The explicit type of order may be up to debate, as well as the
units by which time is measured, but LTL suppresses more complex notions of the
continuous time (at least from a computational view), as well as the branching over possible worlds seen in CTL,
simpifying assuptions we'll accept for the time being.

We base this formalization off Huth \& Ryan's introductory account in
\emph{LOGIC IN COMPUTER SCIENCE}. We shall highlight differences with their
presentation, as well as differences with other pieces of our system as they
arrive.

The syntax of LTL is are formulas $\phi$ inductively defined type consists of

\begin{itemize}
\item Atomic events (which should ideally be grounded to reality), specified externally as some type
\item The standard propositional colletives for truthity, falsity, conjunction, disjunction, and negation
\item Unary temporal operators representing
\begin{itemize}
\item the next state $X$,
\item the existence of a future state $F$,
\item the notion of henceforth, or forever $G$
\end{itemize}
\item Binary temporal operators representing
\begin{itemize}
\item The inclusive states in between two events next state $U$,
\item weak until $W$
\item Release
\end{itemize}
\end{itemize}

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
\begin{code}[hide]
-- power set
𝑃 : Set → Set
𝑃 s = s → Bool

-- 𝑃 Bool has four member
-- for example, we encode the empty set as follows
empt : 𝑃 Bool
empt false = false
empt true = false
\end{code}

This syntax represents a weak boundary of this study. The job of actual
determining how a formula should pertain to reality can be best left to other
experts. Nonetheless, as verifiability has been a primary pretext for this work,
and our development of the semantcs demonstrate Agda's expressivitness,
elegance, and enforcement of correct-by-consturction programs. Noting that a
binary relation $rel$ is a higher type over a type $s$ - a type of types indexed by two
elements of $s$, we can then define the property of a relation always being able
to take another step. That is, for any element of $s$, we can always construct a
element $s'$ which it is related to, that it always steps to.

\begin{code}
rel : Set → Set₁
rel s = s → s → Set

relAlwaysSteps : {S : Set} → rel S → Set
relAlwaysSteps {S} rₛ = ∀ (s : S) → Σ[ s' ∈ S ] (rₛ s s')
\end{code}

A dichotomy over the epistemological status of logic that is whether logical knowledge
is primarily about inference, in the proof theoretic traditions, or truth, in the model
theoretic traditions, can be both juxtaposed and understood better in our work here.

Theorem provers have often promote ``syntactic view'' of logic, with programs and proofs derivations ruling due to the undecidable notion of generating a proof object for a given type.

The ``semantic view'' is much more well esablished in the verification
community, where model checkers, whose primary notion is of ``a model'', and
what the feasibility, or truth, of a piece of syntax means relative to at least
some models.

We now come to fundamental notion in defining a temporal logic : a model. Given
some atomic propositions (groundable to reality) a model 𝑀 in LTL consists of a

\begin{itemize}
\item Type of states
\item A binary relation, or step function over, those states,  _⟶_
\item Evidence that the relation always can take a step or that we can't get into a stuck state, relSteps
\item A labeling function, L, which determines the atomic propositions true at a given state
\end{itemize}

\begin{code}
record 𝑀 (Atom : Set) : Set₁ where
  field
    State : Set
    _⟶_ : rel State
    relSteps : relAlwaysSteps _⟶_
    -- L : State → 𝑃 Atom
    L : State → Atom → Set
\end{code}

We note that in the textbook treatment, the labeling function provides a subset
of the set of atoms for any given state state, that the codomain of the labeller
is the powerset of the atomic propositions. We opt instead to see the labeling
function as a type indexed by states and atoms. This typed formulation provides
not only a convenience for dealing with certain beuracracies encountered using
the classical power set formulation, but allows us to forego so-called ``Boolean
Blindness''
\cite{(https://existentialtype.wordpress.com/2011/03/15/boolean-blindness/)} and
have proof objects which whose syntax more expressively represents the
arguments.

With a model defined, we next establish the fundamental notion of a path in a
model - which is the primary ingredient to establish how a formula can be
evaluated relative to sequence of events in a model. More explicitly, paths
allow us to represent time. The choice of formulation of a path is also subject
to how one interprets the infinte sequence of states over which our temporal
intuitions and expressions take place. We can either see an infinite sequence as
defined by

\begin{itemize}
\item The coinductive type of streams over states, as done in \cite{coqLTL}
\item The mathematicians view of a sequence, that is a set, of states, indexed by the natural numbers
\end{itemize}

Given a model defined in the context of some atoms, we first outline the stream
approach. A stream, often analagously referenced as an ``infinite list'', is
given by a piece of visibile data, the head, and the tail, which is just a
corecursive reference to another list whose data will be accessible later, when
it is \emph{needed} (hence, streams are a fundamental datatype in the call-by-need
operational semantics).

\begin{code}[hide]
module Transition (Atom : Set) (Model : 𝑀 Atom) where
  open Syntax Atom public
  open 𝑀 Model
\end{code}
\begin{code}
  record Stream : Set where
    coinductive
    field
      hd : State
      tl : Stream
\end{code}
\begin{code}
  open Stream

  from-ithState : (i : ℕ) → Stream → Stream
  from-ithState zero x    = x
  from-ithState (suc i) x = from-ithState i (tl x)
\end{code}

% TODO : elaborate infSeq with colors as was done in masters thesis

To define a path in a model, we need an inifinite sequence of states $infSeq$
that don't reach a stuck, or deadlocked state - $infSeq$ always transitions. We
say that the stream always transitions when the first two elements are related
by the models step function, and we can coinductively prove this for the tail of
the stream. The second state, \emph{nextState} of a stream is obviously defined
by taking the head of the tail of the stream.

\begin{code}
  nextState : Stream → State
  nextState s = hd (tl s)

  record streamAlwaysTransitions (stream : Stream) : Set where
    coinductive
    field
      headValid : hd stream ⟶ nextState stream
      tailValid : streamAlwaysTransitions (tl stream)

  record Path : Set where
    field
      infSeq         : Stream
      isTransitional : streamAlwaysTransitions infSeq
\end{code}
\begin{code}[hide]
  open streamAlwaysTransitions
  open Path
\end{code}

As paths not only contain infinite sequence of states which cohere with the
model's step relation, we define two helper functions to overload the head and
tail operations of the path's stream onto to the path itself.

\begin{code}
  headPath : Path → State
  headPath x = hd (infSeq x)

  tailPath : Path → Path
  tailPath p .infSeq         = tl (infSeq p)
  tailPath p .isTransitional = tailValid (isTransitional p)
\end{code}

We now contrast this with the mathematical view of a path, that is, we bypass
the coiinductive stream and simply that the structure of the path is given my a
map ℕ → State. We then adjust our definition of the propery of deadlock freedom.
The alwaysSteps function says, that given a sequence of states $s$, $s_i$ steps
to $s_{i+1}$ for any number $i$. Again, this is all relative to some given model
$M$. Although these look quite different, we [TODO] prove they are equivalent elsewhere [link].

\begin{code}
  alwaysSteps : (sₙ : ℕ → State) → Set
  alwaysSteps s = ∀ i → s i ⟶ s (suc i)

  record Path-seq : Set where
    field
      infSeq         : ℕ → State
      isTransitional : alwaysSteps infSeq
\end{code}
\begin{code}[hide]
  open Path-seq
\end{code}

Once again inhereting the notion of head and tail from streams, we provide can
overload these to our newly formulated sequence-based paths. In addition, we
supply a function $path-i$ that drops the first n states of a path.


\begin{code}[hide]
  headPath-seq : Path-seq → State
  headPath-seq p = p .infSeq 0

  tailPath-seq : Path-seq → Path-seq
  tailPath-seq p .infSeq          n = p .infSeq (suc n)
  tailPath-seq p .isTransitional  n = p .isTransitional (suc n)

  path-i : ℕ → Path-seq → Path-seq
  path-i zero    p = p
  path-i (suc i) p = path-i i (tailPath-seq p)
\end{code}

With this infastructure in place, we can finally define what it means for
formulas ϕ to be true relative to some path in a model. This definition, per
usual, is given by a type denoted via the semantic entailment relation _⊧_,
where π ⊧ ψ is the evidence for the truth of proposition ψ relative to path π in
our model. The fundamental temporal logical notions will be spelled out now as
they are requisite pieces of this definition of truth.

Glancing below, we see that the temporal type definitions involves a paramater
(-⊧ψ : Path → Set), which, as the variable name suggests, is to be substituted
by the semantic entailment applied to a sentence ψ. Although not mutually
recursive, these definitions should be thought of as such - and indeed they are
with alternative formulation of paths.

The idea of the universal quantifier captured via a temporal modality, the
notion of ``forever'' or ``global'', syntactically called $G$, has a meaning
which is a coinductive record G-pf. This G-pf type requires evidance both that a
path π entails the formula ψ and will do so henceforth. More specifically,
knowing that the the path π yields ψ true now, ∀-h and forever onward the tail
of path π will yield ψ true, ∀-t, we may conclude that our model retains ψ
globally in time over the path π.

\begin{code}
  record G-pf (-⊧ψ : Path → Set) (π : Path) : Set where
    coinductive
    field
      ∀-h : -⊧ψ π
      ∀-t : G-pf -⊧ψ (tailPath π)
\end{code}

To capture the notion of \emph{some} future state as temporal modality, one
recognizes that the existential quantifier is being restricted to yield the $F$
operator. However, in this case we just have to prove that a proposition ψ is
entailed by some possibly later part of path a σ. More explictly, we can give
evidence for $F ψ$ via an inductive type F-pf. If we currently know that σ ⊧ ψ ,
then we know that there exists such a time that ψ is true over the path σ,
namely now. On the other hand, if we can prove that the tail of σ entails ψ at
some later time, then σ itself yields a future state where ψ is true.

\begin{code}
  data F-pf (-⊧ψ : Path → Set) (σ : Path) : Set where
    ev-H : -⊧ψ σ → F-pf -⊧ψ σ
    ev-T : F-pf -⊧ψ (tailPath σ) -> F-pf -⊧ψ σ
\end{code}

The until operator $U$ is the ``fundamental'' binary operator, meaning that some
proposition ψ holds up til ψ₁. The proof of evaluation therefore takes a single
path and two entailment operators partially applied to two different formulas.
Evidence can be given if only the the second formula ψ₁ is a semantic
consequence of the path σ, in which case the priorness of event ψ is irrelevant.
In the tail case, until-t, if one can show that ψ is a consequence of σ, and
that we can recursively validate ψ holds until ψ₁ under during the tail states
of the σ, then we know that σ semantically entails ψ until ψ₁.

Our final helper function,  Uincl-Pf, is similar to our previous until helper, except that we now require evidence that ψ is a consequence of σ in the head case where we don't dive deeper into the path σ.

\begin{code}
  data U-Pf (-⊧ψ -⊧ψ₁ : Path → Set) (σ : Path) : Set where
    until-h : -⊧ψ₁ σ → (U-Pf -⊧ψ -⊧ψ₁) σ
    until-t : -⊧ψ σ → (U-Pf -⊧ψ -⊧ψ₁) (tailPath σ) → (U-Pf -⊧ψ -⊧ψ₁) σ

  data Uincl-Pf (-⊧ψ -⊧ψ₁ : Path → Set) (σ : Path) : Set where
    untilI-h : -⊧ψ σ → -⊧ψ₁ σ → (Uincl-Pf -⊧ψ -⊧ψ₁) σ
    untilI-t : -⊧ψ σ → (Uincl-Pf -⊧ψ -⊧ψ₁) (tailPath σ) → (Uincl-Pf -⊧ψ -⊧ψ₁) σ
\end{code}

\begin{code}
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

  open import Function

  -- helper : ∀ π (init : headPath π ≡ s2) → headPath (tailPath π) ≡ s2
  helper : ∀ u w → u ≡ s2 → steps u w → w ≡ s2
  helper .s2 .s2 refl s2s2 = refl

  lemma0 : ∀ p → headPath p ≡ s2 → headPath (tailPath p) ≡ s2
  lemma0 π x
    with headPath π |  (hd (tl (infSeq π))) | headValid (isTransitional π)
  lemma0 π refl | .s2 | s2 | a = refl

  ex-7 : M ,, s2 ⊧ G (atom r)
  -- ex-7 π init = record { ∀-h = subst (λ v → l' v r) (sym init) s2r ; ∀-t = {!!} }
  ex-7 π init .G-pf.∀-h rewrite init = s2r
  ex-7 π init .G-pf.∀-t =
    ex-7
      (tailPath π) -- (tailPath π)
      (lemma0 π init)
      -- (helper
      --   (headPath π)
      --   (hd (tl (infSeq π)))
      --   init
      --   (headValid (isTransitional π)))

  ex-9-i : pathLeft ⊧ (G (F (atom r)))
  ex-9-i .Transition.G-pf.∀-h = ev-T (ev-T {!!})
  ex-9-i .Transition.G-pf.∀-t = {!!}

  -- why?
  -- the left path clearly has no state with both, since its only s0s and s1s
  -- any s2 has only r
  ex-6 : (M ,, s0 ⊧ G (¬ (atom p ∧ atom r)))
  ex-6 π π0=s0 .G-pf.∀-h rewrite π0=s0 =
    λ {()}
  ex-6 π π0=s0 .G-pf.∀-t = ex-6 {!!} {!!} -- ex-6 (tailPath π) {!help!}

  ex-8-s2-lemma : (M ,, s2 ⊧ ((F (G (atom r)))))
  ex-8-s2-lemma π init =
    ev-H (ex-7 π init)

  ex-8-s2 : (M ,, s2 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
  ex-8-s2 π init x₁ = ev-H (ex-7 π init) --  let y = ex-8-s2-lemma in y π x
  -- something like const . ev-H . ex-y

  --can think of example 8 as three lemmas?
  -- ex-8-s1 : (M ,, s1 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
  -- ex-8-s2 : (M ,, s2 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
-- if we know ¬q∧r at some point in the future
-- then we can break it down into two cases :
-- (i) ev-H - its now.
--   In this case, we know that we must already be in S2. (lemma?)
--   Then we reach a contradiction?
-- (ii) ev-T. In the later case, we can say that
-- Take whenever that is (

  lemma : ∀ p → p ⊧ ((¬ (atom q)) ∧ atom r) → headPath p ≡ s2
  lemma π x
    with headPath π
  lemma π (fst , s1r) | .s1 = ⊥-elim (fst s1q)
  lemma π (fst , s2r) | .s2 = refl

  -- can we call one of the others as a lemma, like when it does start at s2
  ex-8-s0 : (M ,, s0 ⊧ ((F ((¬ (atom q)) ∧ atom r)) ⇒ (F (G (atom r)))))
  ex-8-s0 π init
    with headPath π
  ex-8-s0 π refl | .s0 = λ {
  -- ex-8-s0 π init | headπ = λ {
    (Transition.ev-H x) → let x' = lemma π x in {!!} ; -- how to derive this contradiction?
    (Transition.ev-T x) → {!x!}} -- want to recursively call the ex-8-s0 case


-- -- character references
-- -- 𝑀 == \MiM
-- -- 𝑃 == \MiP
\end{code}
