
module Syntax (Atom : Set) where
-- Think Atom =FinSet

data ϕ : Set where
  atom        : Atom → ϕ
  ⊥ ⊤         : ϕ
  ¬_          : ϕ → ϕ
  _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
  X F G       : ϕ → ϕ
  _U_ _W_ _R_ : ϕ → ϕ → ϕ


