module SystemF.Typing where

open import Prelude
open import Substitution
open import SystemF.Substitution
open import SystemF.Syntax

private
  instantiate : ∀ {m} (τ : Type m) (τ' : Type (succ m)) → Type m
  instantiate = Instantiate.instantiate instantiate-type-type

  weaken : ∀ {m} → Type m → Type (succ m)
  weaken = Weaken.weaken weaken-type

Context : (T : Set) → ℕ → Set
Context = Vector

TypeContext : ℕ → Set
TypeContext = Context Kind

TermContext : ℕ → ℕ → Set
TermContext m n = Context (Type m) n

data _⊢_∶_ {m} (Δ : TypeContext m) : Type m → Kind → Set where
  var : ∀ {v} → Δ ⊢ var v ∶ lookup Δ v
  arrow : ∀ {τ τ'} → Δ ⊢ τ ∶ star → Δ ⊢ τ' ∶ star → Δ ⊢ arrow τ τ' ∶ star
  all : ∀ {κ τ} → κ ∷ Δ ⊢ τ ∶ star → Δ ⊢ all κ τ ∶ star
  exists : ∀ {κ τ} → κ ∷ Δ ⊢ τ ∶ star → Δ ⊢ exists κ τ ∶ star
  lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ τ ∶ κ' → Δ ⊢ lam κ τ ∶ arrow κ κ'
  app : ∀ {τ τ' κ κ'} → Δ ⊢ τ ∶ arrow κ κ' → Δ ⊢ τ' ∶ κ → Δ ⊢ app τ τ' ∶ κ'
  prod : ∀ {τ τ'} → Δ ⊢ τ ∶ star → Δ ⊢ τ' ∶ star → Δ ⊢ prod τ τ' ∶ star
  sum : ∀ {τ τ'} → Δ ⊢ τ ∶ star → Δ ⊢ τ' ∶ star → Δ ⊢ sum τ τ' ∶ star

infix 3 _⊢_∶_

data _≡ₜ_ {m} : Type m → Type m → Set where
  trefl : ∀ {τ} → τ ≡ₜ τ
  tsym : ∀ {τ τ'} → τ ≡ₜ τ' → τ' ≡ₜ τ
  ttrans : ∀ {τ₁ τ₂ τ₃} → τ₁ ≡ₜ τ₂ → τ₂ ≡ₜ τ₃ → τ₁ ≡ₜ τ₃
  arrow : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → arrow τ₁ τ₂ ≡ₜ arrow τ₁' τ₂'
  all : ∀ {κ τ τ'} → τ ≡ₜ τ' → all κ τ ≡ₜ all κ τ'
  exists : ∀ {κ τ τ'} → τ ≡ₜ τ' → exists κ τ ≡ₜ exists κ τ'
  lam : ∀ {κ τ τ'} → τ ≡ₜ τ' → lam κ τ ≡ₜ lam κ τ'
  app : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → app τ₁ τ₂ ≡ₜ app τ₁' τ₂'
  app-lam : ∀ {κ τ τ'} → app (lam κ τ) τ' ≡ₜ instantiate τ' τ
  prod : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → prod τ₁ τ₂ ≡ₜ prod τ₁' τ₂'
  sum : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → sum τ₁ τ₂ ≡ₜ sum τ₁' τ₂'

infix 3 _≡ₜ_

data _⹁_⊢_∶_ {m n} (Δ : TypeContext m) (Γ : TermContext m n) : Term m n → Type m → Set where
  var : ∀ {v}
    → Δ ⹁ Γ ⊢ var v ∶ lookup Γ v
  lam : ∀ {τ τ' t}
    → Δ ⹁ (τ ∷ Γ) ⊢ t ∶ τ'
    → Δ ⹁ Γ ⊢ lam τ t ∶ arrow τ τ'
  app : ∀ {τ τ' t t'}
    → Δ ⹁ Γ ⊢ t ∶ arrow τ τ'
    → Δ ⹁ Γ ⊢ t' ∶ τ
    → Δ ⹁ Γ ⊢ app t t' ∶ τ'
  tlam : ∀ {κ τ t}
    → κ ∷ Δ ⹁ map weaken Γ ⊢ t ∶ τ
    → Δ ⹁ Γ ⊢ tlam κ t ∶ all κ τ
  tapp : ∀ {κ τ t τ'}
    → Δ ⹁ Γ ⊢ t ∶ all κ τ
    → Δ ⊢ τ' ∶ κ
    → Δ ⹁ Γ ⊢ tapp t τ' ∶ instantiate τ' τ
  pack : ∀ {κ τ τ' t}
    → Δ ⹁ Γ ⊢ t ∶ instantiate τ' τ
    → Δ ⊢ τ' ∶ κ
    → Δ ⹁ Γ ⊢ pack τ' t (exists κ τ) ∶ exists κ τ
  unpack : ∀ {κ τ τ' t t'}
    → Δ ⹁ Γ ⊢ t ∶ exists κ τ
    → κ ∷ Δ ⹁ τ ∷ map weaken Γ ⊢ t' ∶ weaken τ'
    → Δ ⹁ Γ ⊢ unpack t t' ∶ τ'
  prod : ∀ {τ τ' t t'}
    → Δ ⹁ Γ ⊢ t ∶ τ
    → Δ ⹁ Γ ⊢ t' ∶ τ'
    → Δ ⹁ Γ ⊢ prod t t' ∶ prod τ τ'
  proj₁ : ∀ {τ₁ τ₂ t}
    → Δ ⹁ Γ ⊢ t ∶ prod τ₁ τ₂
    → Δ ⹁ Γ ⊢ proj₁ t ∶ τ₁
  proj₂ : ∀ {τ₁ τ₂ t}
    → Δ ⹁ Γ ⊢ t ∶ prod τ₁ τ₂
    → Δ ⹁ Γ ⊢ proj₂ t ∶ τ₂
  left : ∀ {τ₁ τ₂ t}
    → Δ ⹁ Γ ⊢ t ∶ τ₁
    → Δ ⹁ Γ ⊢ left t ∶ sum τ₁ τ₂
  right : ∀ {τ₁ τ₂ t}
    → Δ ⹁ Γ ⊢ t ∶ τ₂
    → Δ ⹁ Γ ⊢ right t ∶ sum τ₁ τ₂
  match : ∀ {τ τ₁ τ₂ t t₁ t₂}
    → Δ ⹁ Γ ⊢ t ∶ sum τ₁ τ₂
    → Δ ⹁ τ₁ ∷ Γ ⊢ t₁ ∶ τ
    → Δ ⹁ τ₂ ∷ Γ ⊢ t₂ ∶ τ
    → Δ ⹁ Γ ⊢ match t t₁ t₂ ∶ τ
  type-eq : ∀ {t τ τ'}
    → Δ ⹁ Γ ⊢ t ∶ τ
    → τ ≡ₜ τ'
    → Δ ⹁ Γ ⊢ t ∶ τ'

infix 3 _⹁_⊢_∶_