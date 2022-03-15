{-# OPTIONS --postfix-projections #-}
-- {-# OPTIONS --guardedness #-}

module stream2Seq (A : Set) where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

record Stream : Set where
  coinductive
  field
    hd : A
    tl : Stream

open Stream

record _≈_ (xs : Stream) (ys : Stream) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

SeqStream = ℕ → A

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

postulate
  funext : {A B : Set} → {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g

foward : (x : SeqStream) → stream->SeqStream (seqStream->Stream x) ≡ x
foward seqStream = funext rec-lemma
  where
    rec-lemma : ∀ {seqStream} a →
      stream->SeqStream (seqStream->Stream seqStream) a ≡ seqStream a
    rec-lemma zero = refl
    rec-lemma (suc n) = rec-lemma n
