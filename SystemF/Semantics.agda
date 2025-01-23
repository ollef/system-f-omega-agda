module SystemF.Semantics where

open import Prelude
open import SystemF.Syntax
open import SystemF.Substitution hiding (instantiate-term; instantiate-type)
open import Substitution

instantiate-term : ∀ {m n} (t : Term m n) (t' : Term m (succ n)) → Term m n
instantiate-term = Instantiate.instantiate SystemF.Substitution.instantiate-term-term

instantiate-type : ∀ {m n} (t : Type m) (t' : Term (succ m) n) → Term m n
instantiate-type = Instantiate.instantiate SystemF.Substitution.instantiate-type-term-type

data _⟶_ : ∀ {m n} → Term m n → Term m n → Set where
  app₁ : ∀ {m n} {t₁ t₂ t₁' : Term m n}
    → t₁ ⟶ t₁'
    → app t₁ t₂ ⟶ app t₁' t₂
  app₂ : ∀ {m n} {t₁ t₂ t₂' : Term m n}
    → Value t₁
    → t₂ ⟶ t₂'
    → app t₁ t₂ ⟶ app t₁ t₂'
  lam-app : ∀ {m n τ t} {t' : Term m n}
    → Value t'
    → app (lam τ t) t' ⟶ instantiate-term t' t
  tapp : ∀ {m n τ t} {t' : Term m n}
    → t ⟶ t'
    → tapp t τ ⟶ tapp t' τ
  tlam-tapp : ∀ {m n κ τ} {t : Term (succ m) n}
    → tapp (tlam κ t) τ ⟶ instantiate-type τ t
  pack : ∀ {m n τ τ'} {t t' : Term m n}
    → t ⟶ t'
    → pack τ t τ' ⟶ pack τ t' τ'
  unpack : ∀ {m n} {t : Term m n} {t' t''}
    → t ⟶ t'
    → unpack t t'' ⟶ unpack t' t''
  unpack-pack : ∀ {m n κ τ τ'} {t : Term m n} {t'}
    → Value t
    → unpack (pack τ t (exists κ τ')) t' ⟶ instantiate-term t (instantiate-type τ t')
  proj : ∀ {m n size} {t : Term m n} {t'} {x : Fin size}
    → t ⟶ t'
    → proj t x ⟶ proj t' x
  record- : ∀ {size m n i} {ts : Vector (Term m n) size} {t' : Term m n}
    → All Value (take i ts)
    → lookup ts i ⟶ t'
    → record- ts ⟶ record- (update i t' ts)
  proj-record : ∀ {size m n} {i : Fin size} {ts : Vector (Term m n) size}
    → All Value ts
    → proj (record- ts) i ⟶ lookup ts i
  variant : ∀ {size m n} {x : Fin size} {t t' : Term m n}
    → t ⟶ t'
    → variant x t ⟶ variant x t'
  match : ∀ {size m n } {t t' : Term m n} {ts : Vector (Term m (succ n)) size}
    → t ⟶ t'
    → match t ts ⟶ match t' ts
  match-variant : ∀ {size m n x} {ts : Vector (Term m (succ n)) size} {t : Term m n}
    → Value t
    → match (variant x t) ts ⟶ instantiate-term t (lookup ts x)

infix 4 _⟶_

¬-step-value : ∀ {m n} {t t' : Term m n}
  → Value t
  → ¬ (t ⟶ t')
¬-step-value lam ()
¬-step-value tlam ()
¬-step-value (pack value) (pack step) = ¬-step-value value step
¬-step-value (record- (v ∷ vs)) (record- {i = zero} [] step) = ¬-step-value v step
¬-step-value (record- (v ∷ vs)) (record- {i = succ i} (v' ∷ vs') step) = ¬-step-value (record- vs) (record- vs' step)
¬-step-value (variant value) (variant step) = ¬-step-value value step

¬-step-values : ∀ {m n size} {ts : Vector (Term m n) size} {t'}
  → All Value ts
  → ∀ {i}
  → ¬ (lookup ts i ⟶ t')
¬-step-values (v ∷ vs) {i = zero} step = ¬-step-value v step
¬-step-values (v ∷ vs) {i = succ i} step = ¬-step-values vs step

deterministic : ∀ {m n} {t t₁ t₂ : Term m n}
  → t ⟶ t₁
  → t ⟶ t₂
  → t₁ ≡ t₂

update-deterministic : ∀ {m n size} {ts : Vector (Term m n) size} {i₁ i₂ : Fin size} {t' t''}
  → All Value (take i₁ ts)
  → All Value (take i₂ ts)
  → lookup ts i₁ ⟶ t'
  → lookup ts i₂ ⟶ t''
  → update i₁ t' ts ≡ update i₂ t'' ts

deterministic (app₁ step₁) (app₁ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (app₁ step₁) (app₂ v₂ step₂) = absurd (¬-step-value v₂ step₁)
deterministic (app₂ v₁ step₁) (app₁ step₂) = absurd (¬-step-value v₁ step₂)
deterministic (app₂ v₁ step₁) (app₂ v₂ step₂) rewrite deterministic step₁ step₂ = refl
deterministic (app₂ v₁ step₁) (lam-app v₂) = absurd (¬-step-value v₂ step₁)
deterministic (lam-app v₁) (app₂ v₂ step₂) = absurd (¬-step-value v₁ step₂)
deterministic (lam-app _) (lam-app _) = refl
deterministic (tapp step₁) (tapp step₂) rewrite deterministic step₁ step₂ = refl
deterministic tlam-tapp tlam-tapp = refl
deterministic (pack step₁) (pack step₂) rewrite deterministic step₁ step₂ = refl
deterministic (unpack step₁) (unpack step₂) rewrite deterministic step₁ step₂ = refl
deterministic (unpack (pack step₁)) (unpack-pack v₂) = absurd (¬-step-value v₂ step₁)
deterministic (unpack-pack v₁) (unpack (pack step₂)) = absurd (¬-step-value v₁ step₂)
deterministic (unpack-pack v₁) (unpack-pack v₂) = refl
deterministic (proj step₁) (proj step₂) rewrite deterministic step₁ step₂ = refl
deterministic (proj (record- vs₁ step₁)) (proj-record vs₂) = absurd (¬-step-values vs₂ step₁)
deterministic (record- vs₁ step₁) (record- vs₂ step₂) rewrite update-deterministic vs₁ vs₂ step₁ step₂ = refl
deterministic (proj-record vs₁) (proj (record- vs₂ step₂)) = absurd (¬-step-values vs₁ step₂)
deterministic (proj-record vs₁) (proj-record vs₂) = refl
deterministic (variant step₁) (variant step₂) rewrite deterministic step₁ step₂ = refl
deterministic (match step₁) (match step₂) rewrite deterministic step₁ step₂ = refl
deterministic (match (variant step₁)) (match-variant v₂) = absurd (¬-step-value v₂ step₁)
deterministic (match-variant v₁) (match (variant step₂)) = absurd (¬-step-value v₁ step₂)
deterministic (match-variant v₁) (match-variant v₂) = refl

update-deterministic {i₁ = zero} {i₂ = zero} vs₁ vs₂ step₁ step₂ rewrite deterministic step₁ step₂ = refl
update-deterministic {ts = t ∷ ts} {i₁ = zero} {i₂ = succ i₂} vs₁ (v₂ ∷ vs₂) step₁ step₂ = absurd (¬-step-value v₂ step₁)
update-deterministic {ts = t ∷ ts} {i₁ = succ i₁} {i₂ = zero} (v₁ ∷ vs₁) vs₂ step₁ step₂ = absurd (¬-step-value v₁ step₂)
update-deterministic {ts = t ∷ ts} {i₁ = succ i₁} {i₂ = succ i₂} (_ ∷ vs₁) (_ ∷ vs₂) step₁ step₂ = cong (_∷_ t) (update-deterministic vs₁ vs₂ step₁ step₂)