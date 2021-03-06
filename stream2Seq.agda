{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

import LTL-seq
-- open import LTL-seq using () renaming (Transition to LTL)
import LTL

import Syntax
open import Model

module stream2Seq  (Atom : Set) (M : ๐ Atom) where

open import Data.Bool renaming (_โจ_ to _โจ'_ ; _โง_ to _โง'_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_โก_; refl; trans; sym; cong; cong-app; subst)
open Eq.โก-Reasoning using (begin_; _โกโจโฉ_; step-โก; _โ)

module StreamTrans = LTL.Transition Atom M
module SeqTrans = LTL-seq.Transition Atom M
open ๐ M

-- record Stream : Set where
--   coinductive
--   field
--     hd : A
--     tl : Stream

open StreamTrans using (Stream)

open Stream

record _โ_ (xs : Stream) (ys : Stream) : Set where
  coinductive
  field
    hd-โก : hd xs โก hd ys
    tl-โ : tl xs โ tl ys

open _โ_

SeqStream = โ โ State
-- open SeqTrans using () renaming (Stream to SeqStream)

tailSeqStream : SeqStream โ SeqStream
tailSeqStream x = ฮป n โ x (suc n)

from-ithState : (i : โ) โ Stream โ Stream
from-ithState zero x    = x
from-ithState (suc i) x = from-ithState i (tl x)

stream->SeqStream : Stream โ SeqStream
stream->SeqStream x = ฮป n โ hd (from-ithState n x)

seqStream->Stream : SeqStream โ Stream
seqStream->Stream x .hd = x 0
seqStream->Stream x .tl =
  seqStream->Stream  ฮป n โ x (suc n)

backward : (x : Stream) โ seqStream->Stream (stream->SeqStream x) โ x
backward stream .hd-โก = refl
backward stream .tl-โ = backward (tl stream)

data _โก-fun_ {A B : Set} (f : A โ B) : (A โ B) โ Set where
  -- prop-eq : โ g โ f โก g โ f โก-fun g
  ext-eq : โ {g} โ (โ x โ f x โก g x) โ f โก-fun g


foward1 : (x : SeqStream) โ stream->SeqStream (seqStream->Stream x) โก-fun x
foward1 seqStream = ext-eq rec-lemma
  where
    rec-lemma : โ {seqStream} a โ
      stream->SeqStream (seqStream->Stream seqStream) a โก seqStream a
    rec-lemma zero = refl
    rec-lemma (suc n) = rec-lemma n

open import Relation.Binary.Morphism
open import Data.Product

-- myIso : IsRelIsomorphism _โ_ _โก-fun_ stream->SeqStream
-- myIso .IsRelIsomorphism.isMonomorphism .IsRelMonomorphism.isHomomorphism .IsRelHomomorphism.cong
--    x = {!!}
-- myIso .IsRelIsomorphism.isMonomorphism .IsRelMonomorphism.injective x = {!!}
-- myIso .IsRelIsomorphism.surjective y = (seqStream->Stream y) , (foward1 y)



open import Axiom.Extensionality.Propositional
open import Level using (0โ)

postulate
  -- funext : {A B : Set} โ {f g : A โ B} โ ((a : A) โ f a โก g a) โ f โก g
  funext : Extensionality 0โ 0โ


foward : (x : SeqStream) โ stream->SeqStream (seqStream->Stream x) โก x
foward seqStream = funext rec-lemma
  where
    rec-lemma : โ {seqStream} a โ
      stream->SeqStream (seqStream->Stream seqStream) a โก seqStream a
    rec-lemma zero = refl
    rec-lemma (suc n) = rec-lemma n

module TransitionEq where

  open StreamTrans.streamAlwaysTransitions
  alwaysSteps-str->seq : โ {infSeq} โ (isTransitional
                            : StreamTrans.streamAlwaysTransitions infSeq) โ
                        SeqTrans.alwaysSteps (stream->SeqStream infSeq)
  alwaysSteps-str->seq isTransitional zero = isTransitional .headValid
  alwaysSteps-str->seq isTransitional (suc i) = {!alwaysSteps-str->seq isTransitional i!}

  str->seq-path : StreamTrans.Path โ SeqTrans.Path
  str->seq-path record { infSeq = infSeq ; isTransitional = isTransitional }
              = record { infSeq = stream->SeqStream infSeq
                       ; isTransitional = alwaysSteps-str->seq isTransitional }
