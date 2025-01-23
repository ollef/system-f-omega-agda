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
  lam : ∀ {κ κ' t} → κ ∷ Δ ⊢ t ∶ κ' → Δ ⊢ lam κ t ∶ arrow κ κ'
  app : ∀ {τ τ' t t'} → Δ ⊢ t ∶ arrow τ τ' → Δ ⊢ t' ∶ τ → Δ ⊢ app t t' ∶ τ'
  record- : ∀ {size} {τs : Vector (Type m) size} → All (λ τ → Δ ⊢ τ ∶ star) τs → Δ ⊢ record- τs ∶ star
  variant : ∀ {size} {τs : Vector (Type m) size} → All (λ τ → Δ ⊢ τ ∶ star) τs → Δ ⊢ variant τs ∶ star

infix 3 _⊢_∶_

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
  record- : ∀ {size} {τs : Vector (Type m) size} {ts : Vector (Term m n) size}
    → ZipWith (λ t τ → Δ ⹁ Γ ⊢ t ∶ τ) ts τs
    → Δ ⹁ Γ ⊢ record- ts ∶ record- τs
  proj : ∀ {size} {τs : Vector (Type m) size} {t x}
    → Δ ⹁ Γ ⊢ t ∶ record- τs
    → Δ ⹁ Γ ⊢ proj t x ∶ lookup τs x
  variant : ∀ {size} {τs : Vector (Type m) size} {t x}
    → Δ ⹁ Γ ⊢ t ∶ lookup τs x
    → Δ ⹁ Γ ⊢ variant x t ∶ variant τs

infix 3 _⹁_⊢_∶_