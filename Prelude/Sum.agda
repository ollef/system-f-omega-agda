module Prelude.Sum where

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 2 _⊎_