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
  prod : Type m → Type m → Type m
  sum : Type m → Type m → Type m

data Term (m n : ℕ) : Set where
  var : Fin n → Term m n
  lam : Type m → Term m (succ n) → Term m n
  app : Term m n → Term m n → Term m n
  tlam : Kind → Term (succ m) n → Term m n
  tapp : Term m n → Type m → Term m n
  pack : Type m → Term m n → Type m → Term m n
  unpack : Term m n → Term (succ m) (succ n) → Term m n
  prod : Term m n → Term m n → Term m n
  proj₁ proj₂ : Term m n → Term m n
  left right : Term m n → Term m n
  match : Term m n → Term m (succ n) → Term m (succ n) → Term m n

data Value {m n : ℕ} : Term m n → Set where
  lam : ∀ {τ t} → Value (lam τ t)
  tlam : ∀ {κ t} → Value (tlam κ t)
  pack : ∀ {τ t τ'} → Value t → Value (pack τ t τ')
  prod : ∀ {t₁ t₂} → Value t₁ → Value t₂ → Value (prod t₁ t₂)
  left : ∀ {t} → Value t → Value (left t)
  right : ∀ {t} → Value t → Value (right t)