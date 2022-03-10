{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

module stream2Seq where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

record Stream : Set where
  coinductive
  field
    hd : Bool
    tl : Stream

open Stream

record _≈_ (xs : Stream) (ys : Stream) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

Stream2 = ℕ → Bool

-- record Stream2 : Set where
--   field
--     infBoolSeq : ℕ → Bool

-- open Stream2

-- record _≈'_ (xs : Stream2) (ys : Stream2) : Set where
--   coinductive
--   field
--     fcn-≡ : infBoolSeq xs ≡ infBoolSeq ys

-- open _≈'_

evalStream2 : Stream2 → ℕ → Bool
evalStream2 x n = x n

tailStream2 : Stream2 → Stream2
tailStream2 x = λ n → x (suc n)

from-ithState : (i : ℕ) → Stream → Stream
from-ithState zero x    = x
from-ithState (suc i) x = from-ithState i (tl x)

stream2Stream2 : Stream → Stream2
stream2Stream2 x = λ n → hd (from-ithState n x)

-- take the minus one of the input streams input
stream22Stream : Stream2 → Stream
stream22Stream x .hd = x 0
stream22Stream x .tl =
  stream22Stream  λ n → x (suc n)

postulate
  funext : {A B : Set} → {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g

-- -- need funext
-- forward : (x : Stream2) → stream2Stream2 (stream22Stream x) ≈' x
-- forward record { infBoolSeq = infBoolSeq } =
--   record { fcn-≡ = funext {!!} {!!} {!!} {!!} }

-- backward : (x : Stream) → stream22Stream (stream2Stream2 x) ≈ x
-- backward = {!!}

-- false, true, true, ...

exStream2 : Stream2
exStream2 zero = false
exStream2 (suc n) = true

trueStream2 : Stream2
trueStream2 = λ x → true

trueStream : Stream
trueStream .hd = true
trueStream .tl = trueStream

exStream : Stream
exStream .hd = false
exStream .tl = trueStream
-- exStream .tl .tl = {!!}

-- forwardTrueStream : stream2Stream2 (stream22Stream trueStream2) ≈' trueStream2
-- forwardTrueStream .fcn-≡ = funext (λ a → {!!})

-- forward' : stream2Stream2 (stream22Stream exStream2) ≈' exStream2
-- forward' .fcn-≡ = funext λ
--   { zero    → refl ;
--     (suc n) → {!!}}

-- backward' : (x : Stream) → stream22Stream (stream2Stream2 x) ≈ x

lemma : (n : ℕ) → hd (from-ithState n trueStream) ≡ true
lemma zero = refl
lemma (suc n) = lemma n

backward' : (stream22Stream (stream2Stream2 trueStream)) ≈ trueStream
backward' .hd-≡ = refl
backward' .tl-≈ = backward'

-- backward' : (stream22Stream (stream2Stream2 exStream)) ≈ exStream
-- backward' .hd-≡ = refl
-- backward' .tl-≈ = {!backward'!}
