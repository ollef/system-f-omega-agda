module Prelude.Sigma where

open import Agda.Builtin.Sigma public

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 2 _×_