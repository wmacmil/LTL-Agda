module Example1 where

open import Support
open import Model
open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)

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
ex1IsTransitionSyst .State    = states
ex1IsTransitionSyst ._⟶_      = steps
ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
ex1IsTransitionSyst .L        = l'
-- ex1IsTransitionSyst .L''   = l''

M = ex1IsTransitionSyst
-- open 𝑀

-- ex1IsTransitionSyst : 𝑀 atoms
-- ex1IsTransitionSyst .State = states
-- ex1IsTransitionSyst ._⟶_ = steps
-- ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
-- ex1IsTransitionSyst .L = l'

-- --abreviation
-- M = ex1IsTransitionSyst
