
module Syntax (Atom : Set) where
-- Think Atom =FinSet

data ϕ : Set where
  atom        : Atom → ϕ
  ⊥ ⊤         : ϕ
  ¬_          : ϕ → ϕ
  _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
  X F G       : ϕ → ϕ
  _U_ _W_ _R_ : ϕ → ϕ → ϕ

open import Data.List

-- that it automatically satisfies true, so if there are no location propositions
-- a trace is just a list of atoms
-- coverage versus surveillance patterns

-- data atoms : Set where
--   corner : atoms
--   person : atoms
--   home   : atoms
--   cafe   : atoms

--eventually visit all the ls
visit : List Atom → ϕ
visit [] = ⊤
visit (l ∷ ls) = (F (atom l)) ∧ visit ls

-- eventually replace eventually with efficiently : (i.e. minimize energy such that you get there)

--eventually visit l1, and then eventually visit l2,
sequentialVisit : List Atom → ϕ
sequentialVisit [] = ⊤
sequentialVisit (l ∷ ls) = F (atom l ∧ sequentialVisit ls)

-- suppose the driver doesn't actually care if they visit all the locations, as
-- long as they get to the last location
weakSequentialVisit : List Atom → ϕ
weakSequentialVisit [] = ⊤
weakSequentialVisit lss@(l ∷ ls) = sequentialVisit lss ∨ weakSequentialVisit ls

-- ordering condition
-- don't visit li+1 until you've visited li
predecessorPrecedesSuccessor : List Atom → ϕ
predecessorPrecedesSuccessor [] = ⊤
predecessorPrecedesSuccessor (l ∷ []) = ⊤
predecessorPrecedesSuccessor (lᵢ ∷ lᵢ₊₁ ∷ ls) =
  ((¬ atom lᵢ₊₁) U atom lᵢ) ∧ predecessorPrecedesSuccessor (lᵢ₊₁ ∷ ls)

orderedVisit : List Atom → ϕ
orderedVisit ls = sequentialVisit ls ∧ predecessorPrecedesSuccessor ls

-- strictness condition
-- don't visit a location twice
-- probably not realistic for our example
-- everything should also depend on the location of the vehicle
-- past temporal operators should be used to judge the success of a mission
strictSeq : List Atom → ϕ
strictSeq [] = ⊤
strictSeq (l ∷ []) = ⊤
strictSeq (lᵢ ∷ lᵢ₊₁ ∷ ls) = ((¬ atom lᵢ₊₁) U (atom lᵢ ∧ X ((¬ atom lᵢ) U atom lᵢ₊₁))) ∧ strictSeq (lᵢ₊₁ ∷ ls)

strictOrderedVisit : List Atom → ϕ
strictOrderedVisit ls = orderedVisit ls ∧ strictSeq ls

-- define a satisfaction for a trace -- only care about the finite case, but really we should generalize this
-- can ask if a trace satisisfies a formula

--Mission specifications
-- are used, among others, to synthesize, verify, simulate or guide
-- the engineering of robot software

--fair visit and patrolling, could be interpreted with respect to taking the cab around
-- a trace is just a path where the labeller is restricted to singleton sets

-- G (isRed -> (break U vel == 0) U isGreen) (unless there is an ambulance)

-- stop is really a slow and stay stop

-- G (isGreen -> Go)

-- globally, obey
