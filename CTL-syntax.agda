module CTL-syntax (Atom : Set) where

data ϕ : Set where
  atom        : Atom → ϕ
  ⊥ ⊤         : ϕ
  ¬_          : ϕ → ϕ
  _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
  EX EF EG    : ϕ → ϕ
  AX AF AG    : ϕ → ϕ
  A_U_ E_U_   : ϕ → ϕ → ϕ
