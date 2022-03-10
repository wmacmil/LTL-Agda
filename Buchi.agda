module Buchi where

open import Data.Bool
open import Level using (_⊔_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _<′_; _+_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
-- open import Data.Fin as Fin

record FSA : Set₁ where
  field
    Q : Set
    Σ' : Set
    δ : Q → Σ' → Q
    q₀ : Q
    F : Q → Set

module Transition (fsa : FSA) where
  open FSA fsa

  stringΣ = List Σ'

  -- w : a₁ ... aₙ ∈ stringΣ

  -- -- accepts : (w : stringΣ) → FSA → Set
  -- accepts : (w : stringΣ) → Set
  -- -- open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
  -- accepts [] = ⊤
  -- accepts (x ∷ w) = {!!}
  --   -- Σ[ rs ∈ (List Q) ] {!!}


-- evalFSA' : (fsa : FSA) → List (FSA.Σ fsa) → Set


-- evalFSA' fsa [] = ⊥
-- evalFSA' fsa (x ∷ xs) = helper fsa (x ∷ xs) (FSA.q₀ fsa)
--   where
--     helper : (fsa : FSA) → List (FSA.Σ fsa) → (FSA.Q fsa) → Set
--     helper fsa [] q = FSA.F fsa q
--     helper fsa (x ∷ xs) q = helper fsa xs ((FSA.δ fsa) q x)

-- data Q' : Set where
--   S₁ : Q'
--   S₂ : Q'

-- data Σ' : Set where
--   0' : Σ'
--   1' : Σ'

-- q₀' : Q'
-- q₀' = S₁

-- F' : Q' → Set
-- F' S₁ = ⊤
-- F' S₂ = ⊥

-- δ' : Q' → Σ' → Q'
-- δ' S₁ 0' = S₁
-- δ' S₁ 1' = S₂
-- δ' S₂ 0' = S₁
-- δ' S₂ 1' = S₂

-- M : FSA
-- FSA.Q M = Q'
-- FSA.Σ M = Σ'
-- FSA.δ M = δ'
-- FSA.q₀ M = q₀'
-- FSA.F M = F'

-- exF1  = evalFSA' M (0' ∷ [])
-- exF2  = evalFSA' M (1' ∷ (0' ∷ 0' ∷ 1' ∷ []))

-- -- a more general endIn that i was orignally trying to use, but likewise failed to get to work
-- data Dec (A : Set) : Set where
--   yes : A → Dec A
--   no  : (A → ⊥) → Dec A

-- sigDec : (x y : Σ') → Dec (x ≡ y)
-- sigDec 0' 0' = yes refl
-- sigDec 0' 1' = no (λ ())
-- sigDec 1' 0' = no (λ ())
-- sigDec 1' 1' = yes refl

-- endsIn : {X : Set} → ((x y : X) → Dec (x ≡ y)) → List X → X → Set
-- endsIn d [] x = ⊥
-- endsIn d (x ∷ []) x0 with (d x0 x)
-- ... | yes refl = ⊤
-- ... | no x1 = ⊥
-- endsIn d (x ∷ x1 ∷ xs) x0 = endsIn d (x1 ∷ xs) x0

-- _endsIn'_ : List Σ' → Σ' → Set
-- xs endsIn' x = endsIn sigDec xs x

-- endsIn0 : List Σ' → Set
-- endsIn0 [] = ⊥
-- endsIn0 (0' ∷ []) = ⊤
-- endsIn0 (0' ∷ x ∷ xs) = endsIn0 (x ∷ xs)
-- endsIn0 (1' ∷ xs) = endsIn0 xs

-- -- testing
-- 10endsin0 = (1' ∷ 0' ∷ []) endsIn' 0'
-- n10endsin0 = (1' ∷ 1' ∷ []) endsIn' 0'
