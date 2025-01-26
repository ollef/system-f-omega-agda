module SystemF.Semantics where

open import Prelude
open import SystemF.Syntax
open import SystemF.Substitution hiding (instantiate-term; instantiate-type)
open import Substitution

instantiate-term : ∀ {m n} (t : Term m n) (t' : Term m (succ n)) → Term m n
instantiate-term = Instantiate.instantiate SystemF.Substitution.instantiate-term-term

instantiate-type : ∀ {m n} (t : Type m) (t' : Term (succ m) n) → Term m n
instantiate-type = Instantiate.instantiate SystemF.Substitution.instantiate-type-term-type

data _⟶_ {m n} : Term m n → Term m n → Set where
  app₁ : ∀ {t₁ t₂ t₁'}
    → t₁ ⟶ t₁'
    → app t₁ t₂ ⟶ app t₁' t₂
  app₂ : ∀ {t₁ t₂ t₂'}
    → Value t₁
    → t₂ ⟶ t₂'
    → app t₁ t₂ ⟶ app t₁ t₂'
  app-lam : ∀ {τ t t'}
    → Value t'
    → app (lam τ t) t' ⟶ instantiate-term t' t
  tapp : ∀ {τ t t'}
    → t ⟶ t'
    → tapp t τ ⟶ tapp t' τ
  tapp-tlam : ∀ {κ τ t}
    → tapp (tlam κ t) τ ⟶ instantiate-type τ t
  pack : ∀ {τ τ' t t'}
    → t ⟶ t'
    → pack τ t τ' ⟶ pack τ t' τ'
  unpack : ∀ {t t' t''}
    → t ⟶ t'
    → unpack t t'' ⟶ unpack t' t''
  unpack-pack : ∀ {κ τ τ' t t'}
    → Value t
    → unpack (pack τ t (exists κ τ')) t' ⟶ instantiate-term t (instantiate-type τ t')
  prod₁ : ∀ {t₁ t₁' t₂}
    → t₁ ⟶ t₁'
    → prod t₁ t₂ ⟶ prod t₁' t₂
  prod₂ : ∀ {t₁ t₂ t₂'}
    → Value t₁
    → t₂ ⟶ t₂'
    → prod t₁ t₂ ⟶ prod t₁ t₂'
  proj₁ : ∀ {t t'}
    → t ⟶ t'
    → proj₁ t ⟶ proj₁ t'
  proj₂ : ∀ {t t'}
    → t ⟶ t'
    → proj₂ t ⟶ proj₂ t'
  proj₁-prod : ∀ {t₁ t₂}
    → Value t₁
    → Value t₂
    → proj₁ (prod t₁ t₂) ⟶ t₁
  proj₂-prod : ∀ {t₁ t₂}
    → Value t₁
    → Value t₂
    → proj₂ (prod t₁ t₂) ⟶ t₂
  left : ∀ {t t'}
    → t ⟶ t'
    → left t ⟶ left t'
  right : ∀ {t t'}
    → t ⟶ t'
    → right t ⟶ right t'
  match : ∀ {t t' t₁ t₂}
    → t ⟶ t'
    → match t t₁ t₂ ⟶ match t' t₁ t₂
  match-left : ∀ {t t₁ t₂}
    → Value t
    → match (left t) t₁ t₂ ⟶ instantiate-term t t₁
  match-right : ∀ {t t₁ t₂}
    → Value t
    → match (right t) t₁ t₂ ⟶ instantiate-term t t₂

infix 4 _⟶_

¬-step-value : ∀ {m n} {t t' : Term m n}
  → Value t
  → ¬ (t ⟶ t')
¬-step-value (pack value) (pack step) = ¬-step-value value step
¬-step-value (left v) (left step) = ¬-step-value v step
¬-step-value (right v) (right step) = ¬-step-value v step
¬-step-value (prod v v') (prod₁ step) = ¬-step-value v step
¬-step-value (prod v v') (prod₂ v'' step) = ¬-step-value v' step

deterministic : ∀ {m n} {t t₁ t₂ : Term m n}
  → t ⟶ t₁
  → t ⟶ t₂
  → t₁ ≡ t₂
deterministic (app₁ step₁) (app₁ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (app₁ step₁) (app₂ v₂ step₂) = absurd (¬-step-value v₂ step₁)
deterministic (app₂ v₁ step₁) (app₁ step₂) = absurd (¬-step-value v₁ step₂)
deterministic (app₂ v₁ step₁) (app₂ v₂ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (app₂ v₁ step₁) (app-lam v₂) = absurd (¬-step-value v₂ step₁)
deterministic (app-lam v₁) (app₂ v₂ step₂) = absurd (¬-step-value v₁ step₂)
deterministic (app-lam _) (app-lam _) = refl
deterministic (tapp step₁) (tapp step₂) rewrite deterministic step₁ step₂ = refl
deterministic tapp-tlam tapp-tlam = refl
deterministic (pack step₁) (pack step₂) rewrite deterministic step₁ step₂ = refl
deterministic (unpack step₁) (unpack step₂) rewrite deterministic step₁ step₂ = refl
deterministic (unpack (pack step₁)) (unpack-pack v₂) = absurd (¬-step-value v₂ step₁)
deterministic (unpack-pack v₁) (unpack (pack step₂)) = absurd (¬-step-value v₁ step₂)
deterministic (unpack-pack v₁) (unpack-pack v₂) = refl
deterministic (prod₁ step₁) (prod₁ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (prod₁ step₁) (prod₂ v₂ step₂) = absurd (¬-step-value v₂ step₁)
deterministic (prod₂ v₁ step₁) (prod₁ step₂) = absurd (¬-step-value v₁ step₂)
deterministic (prod₂ v₁ step₁) (prod₂ v₂ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (proj₁ step₁) (proj₁-prod v₂ v₂') = absurd (¬-step-value (prod v₂ v₂') step₁)
deterministic (proj₂ step₁) (proj₂-prod v₂ v₂') = absurd (¬-step-value (prod v₂ v₂') step₁)
deterministic (proj₁-prod v₁ v₁') (proj₁ step₂) = absurd (¬-step-value (prod v₁ v₁') step₂)
deterministic (proj₂-prod v₁ v₁') (proj₂ step₂) = absurd (¬-step-value (prod v₁ v₁') step₂)
deterministic (proj₁ step₁) (proj₁ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (proj₂ step₁) (proj₂ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (proj₁-prod v₁ v₂) (proj₁-prod v₁' v₂') = refl
deterministic (proj₂-prod v₁ v₂) (proj₂-prod v₁' v₂') = refl
deterministic (left step₁) (left step₂) rewrite deterministic step₁ step₂ = refl
deterministic (right step₁) (right step₂) rewrite deterministic step₁ step₂ = refl
deterministic (match step₁) (match step₂) rewrite deterministic step₁ step₂ = refl
deterministic (match step₁) (match-left v₂) = absurd (¬-step-value (left v₂) step₁)
deterministic (match step₁) (match-right v₂) = absurd (¬-step-value (right v₂) step₁)
deterministic (match-left v₁) (match step₂) = absurd (¬-step-value (left v₁) step₂)
deterministic (match-left v₁) (match-left v₂) = refl
deterministic (match-right v₁) (match step₂) = absurd (¬-step-value (right v₁) step₂)
deterministic (match-right v₁) (match-right v₂) = refl