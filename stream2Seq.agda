{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

import LTL-seq
-- open import LTL-seq using () renaming (Transition to LTL)
import LTL

import Syntax
open import Model

module stream2Seq  (Atom : Set) (M : 𝑀 Atom) where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

module StreamTrans = LTL.Transition Atom M
module SeqTrans = LTL-seq.Transition Atom M
open 𝑀 M

-- record Stream : Set where
--   coinductive
--   field
--     hd : A
--     tl : Stream

open StreamTrans using (Stream)

open Stream

record _≈_ (xs : Stream) (ys : Stream) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

SeqStream = ℕ → State
-- open SeqTrans using () renaming (Stream to SeqStream)

tailSeqStream : SeqStream → SeqStream
tailSeqStream x = λ n → x (suc n)

from-ithState : (i : ℕ) → Stream → Stream
from-ithState zero x    = x
from-ithState (suc i) x = from-ithState i (tl x)

stream->SeqStream : Stream → SeqStream
stream->SeqStream x = λ n → hd (from-ithState n x)

seqStream->Stream : SeqStream → Stream
seqStream->Stream x .hd = x 0
seqStream->Stream x .tl =
  seqStream->Stream  λ n → x (suc n)

backward : (x : Stream) → seqStream->Stream (stream->SeqStream x) ≈ x
backward stream .hd-≡ = refl
backward stream .tl-≈ = backward (tl stream)

data _≡-fun_ {A B : Set} (f : A → B) : (A → B) → Set where
  -- prop-eq : ∀ g → f ≡ g → f ≡-fun g
  ext-eq : ∀ {g} → (∀ x → f x ≡ g x) → f ≡-fun g


foward1 : (x : SeqStream) → stream->SeqStream (seqStream->Stream x) ≡-fun x
foward1 seqStream = ext-eq rec-lemma
  where
    rec-lemma : ∀ {seqStream} a →
      stream->SeqStream (seqStream->Stream seqStream) a ≡ seqStream a
    rec-lemma zero = refl
    rec-lemma (suc n) = rec-lemma n

open import Relation.Binary.Morphism
open import Data.Product

-- myIso : IsRelIsomorphism _≈_ _≡-fun_ stream->SeqStream
-- myIso .IsRelIsomorphism.isMonomorphism .IsRelMonomorphism.isHomomorphism .IsRelHomomorphism.cong
--    x = {!!}
-- myIso .IsRelIsomorphism.isMonomorphism .IsRelMonomorphism.injective x = {!!}
-- myIso .IsRelIsomorphism.surjective y = (seqStream->Stream y) , (foward1 y)



open import Axiom.Extensionality.Propositional
open import Level using (0ℓ)

postulate
  -- funext : {A B : Set} → {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g
  funext : Extensionality 0ℓ 0ℓ


foward : (x : SeqStream) → stream->SeqStream (seqStream->Stream x) ≡ x
foward seqStream = funext rec-lemma
  where
    rec-lemma : ∀ {seqStream} a →
      stream->SeqStream (seqStream->Stream seqStream) a ≡ seqStream a
    rec-lemma zero = refl
    rec-lemma (suc n) = rec-lemma n

module TransitionEq where

  open StreamTrans.streamAlwaysTransitions
  alwaysSteps-str->seq : ∀ {infSeq} → (isTransitional
                            : StreamTrans.streamAlwaysTransitions infSeq) →
                        SeqTrans.alwaysSteps (stream->SeqStream infSeq)
  alwaysSteps-str->seq isTransitional zero = isTransitional .headValid
  alwaysSteps-str->seq isTransitional (suc i) = {!alwaysSteps-str->seq isTransitional i!}

  str->seq-path : StreamTrans.Path → SeqTrans.Path
  str->seq-path record { infSeq = infSeq ; isTransitional = isTransitional }
              = record { infSeq = stream->SeqStream infSeq
                       ; isTransitional = alwaysSteps-str->seq isTransitional }
