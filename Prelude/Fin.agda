module Prelude.Fin where

open import Prelude.Nat
open import Prelude.PropositionalEquality

data Fin : (n : ℕ) → Set where
  zero : ∀ {n} → Fin (succ n)
  succ : ∀ {n} → Fin n → Fin (succ n)

lift : ∀ {m n} k → (Fin m → Fin n) → Fin (k + m) → Fin (k + n)
lift zero f x = f x
lift (succ k) f zero = zero
lift (succ k) f (succ x) = succ (lift k f x)

lift-commutes : ∀ {n} k l (x : Fin (l + (k + n))) → lift l succ (lift l (lift k succ) x) ≡ lift l (lift (succ k) succ) (lift l succ x)
lift-commutes k zero x = refl
lift-commutes k (succ l) zero = refl
lift-commutes k (succ l) (succ x) = cong succ (lift-commutes k l x)

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = zero
toℕ (succ x) = succ (toℕ x)