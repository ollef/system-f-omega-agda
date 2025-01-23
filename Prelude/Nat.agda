module Prelude.Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

infixr 4 _+_