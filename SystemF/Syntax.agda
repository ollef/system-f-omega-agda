module SystemF.Syntax where

open import Prelude

data Kind : Set where
  star : Kind
  arrow : Kind → Kind → Kind

data Type (m : ℕ) : Set where
  var : Fin m → Type m
  arrow : Type m → Type m → Type m
  all : Kind → Type (succ m) → Type m
  exists : Kind → Type (succ m) → Type m
  lam : Kind → Type (succ m) → Type m
  app : Type m → Type m → Type m
  record- : ∀ {size} → Vector (Type m) size → Type m
  variant : ∀ {size} → Vector (Type m) size → Type m

data Term (m n : ℕ) : Set where
  var : Fin n → Term m n
  lam : Type m → Term m (succ n) → Term m n
  app : Term m n → Term m n → Term m n
  tlam : Kind → Term (succ m) n → Term m n
  tapp : Term m n → Type m → Term m n
  pack : Type m → Term m n → Type m → Term m n
  unpack : Term m n → Term (succ m) (succ n) → Term m n
  record- : ∀ {size} → Vector (Term m n) size → Term m n
  proj : ∀ {size} → Term m n → Fin size → Term m n
  variant : ∀ {size} → Fin size → Term m n → Term m n
  match : ∀ {size} → Term m n → Vector (Term m (succ n)) size → Term m n

data Value {m n : ℕ} : Term m n → Set where
  lam : ∀ {τ t} → Value (lam τ t)
  tlam : ∀ {κ t} → Value (tlam κ t)
  pack : ∀ {τ t τ'} → Value t → Value (pack τ t τ')
  record- : ∀ {size} {ts : Vector (Term m n) size} → All Value ts → Value (record- ts)
  variant : ∀ {size} {x : Fin size} {t} → Value t → Value (variant x t)