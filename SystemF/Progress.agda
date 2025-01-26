module SystemF.Progress where

open import Prelude
open import SystemF.Semantics
open import SystemF.Syntax
open import SystemF.Typing
import SystemF.TypeReduction as TypeReduction

module CanonicalForms where
  arrow-lam : ∀ {m Δ τ τ₁ τ₂} {t : Term m 0}
    → Value t
    → Δ ⹁ [] ⊢ t ∶ τ
    → τ ≡ₜ arrow τ₁ τ₂
    → Σ (Type m × Term m 1) λ (τ₁' , t') → t ≡ lam τ₁' t'
  arrow-lam lam _ eq = _ , refl
  arrow-lam tlam (tlam d) eq = absurd (TypeReduction.¬-all-≡ₜ-arrow eq)
  arrow-lam tlam (type-eq d eq') eq = arrow-lam tlam d (ttrans eq' eq)
  arrow-lam (pack v) (pack d x) eq = absurd (TypeReduction.¬-exists-≡ₜ-arrow eq)
  arrow-lam (pack v) (type-eq d eq') eq = arrow-lam (pack v) d (ttrans eq' eq)
  arrow-lam (prod v v') (prod d d') eq = absurd (TypeReduction.¬-prod-≡ₜ-arrow eq)
  arrow-lam (prod v v') (type-eq d x) eq = arrow-lam (prod v v') d (ttrans x eq)
  arrow-lam (left v) (left d) eq = absurd (TypeReduction.¬-sum-≡ₜ-arrow eq)
  arrow-lam (left v) (type-eq d eq') eq = arrow-lam (left v) d (ttrans eq' eq)
  arrow-lam (right v) (right d) eq = absurd (TypeReduction.¬-sum-≡ₜ-arrow eq)
  arrow-lam (right v) (type-eq d eq') eq = arrow-lam (right v) d (ttrans eq' eq)

  all-tlam : ∀ {m Δ κ τ τ'} {t : Term m 0}
    → Value t
    → Δ ⹁ [] ⊢ t ∶ τ
    → τ ≡ₜ all κ τ'
    → Σ (Kind × Term (succ m) 0) λ (κ' , t') → t ≡ tlam κ' t'
  all-tlam lam (lam d) eq = absurd (TypeReduction.¬-all-≡ₜ-arrow (tsym eq))
  all-tlam lam (type-eq d eq') eq = all-tlam lam d (ttrans eq' eq)
  all-tlam tlam _ eq = _ , refl
  all-tlam (pack v) (pack d d') eq = absurd (TypeReduction.¬-exists-≡ₜ-all eq)
  all-tlam (pack v) (type-eq d eq') eq = all-tlam (pack v) d (ttrans eq' eq)
  all-tlam (prod v v₁) (prod d d') eq = absurd (TypeReduction.¬-prod-≡ₜ-all eq)
  all-tlam (prod v v₁) (type-eq d eq') eq = all-tlam (prod v v₁) d (ttrans eq' eq)
  all-tlam (left v) (left d) eq = absurd (TypeReduction.¬-sum-≡ₜ-all eq)
  all-tlam (left v) (type-eq d eq') eq = all-tlam (left v) d (ttrans eq' eq)
  all-tlam (right v) (right d) eq = absurd (TypeReduction.¬-sum-≡ₜ-all eq)
  all-tlam (right v) (type-eq d eq') eq = all-tlam (right v) d (ttrans eq' eq)

  exists-pack : ∀ {m Δ κ τ τ'} {t : Term m 0}
    → Value t
    → Δ ⹁ [] ⊢ t ∶ τ
    → τ ≡ₜ exists κ τ'
    → Σ (Type _ × Term _ _ × Kind × Type _) λ (τ₁ , t' , κ' , τ₂) → Value t' × (t ≡ pack τ₁ t' (exists κ' τ₂))
  exists-pack lam (lam d) eq = absurd (TypeReduction.¬-exists-≡ₜ-arrow (tsym eq))
  exists-pack lam (type-eq d eq') eq = exists-pack lam d (ttrans eq' eq)
  exists-pack tlam (tlam d) eq = absurd (TypeReduction.¬-exists-≡ₜ-all (tsym eq))
  exists-pack tlam (type-eq d eq') eq = exists-pack tlam d (ttrans eq' eq)
  exists-pack (pack v) (pack d d') eq = _ , v , refl
  exists-pack (pack v) (type-eq d eq') eq = exists-pack (pack v) d (ttrans eq' eq)
  exists-pack (prod v v') (prod d d') eq = absurd (TypeReduction.¬-prod-≡ₜ-exists eq)
  exists-pack (prod v v') (type-eq d eq') eq = exists-pack (prod v v') d (ttrans eq' eq)
  exists-pack (left v) (left d) eq = absurd (TypeReduction.¬-sum-≡ₜ-exists eq)
  exists-pack (left v) (type-eq d eq') eq = exists-pack (left v) d (ttrans eq' eq)
  exists-pack (right v) (right d) eq = absurd (TypeReduction.¬-sum-≡ₜ-exists eq)
  exists-pack (right v) (type-eq d eq') eq = exists-pack (right v) d (ttrans eq' eq)

  prod-prod : ∀ {m Δ τ τ₁ τ₂} {t : Term m 0}
    → Value t
    → Δ ⹁ [] ⊢ t ∶ τ
    → τ ≡ₜ prod τ₁ τ₂
    → Σ (Term _ _ × Term _ _) λ (t₁ , t₂) → Value t₁ × Value t₂ × (t ≡ prod t₁ t₂)
  prod-prod lam (lam d) eq = absurd (TypeReduction.¬-prod-≡ₜ-arrow (tsym eq))
  prod-prod lam (type-eq d eq') eq = prod-prod lam d (ttrans eq' eq)
  prod-prod tlam (tlam d) eq = absurd (TypeReduction.¬-prod-≡ₜ-all (tsym eq))
  prod-prod tlam (type-eq d eq') eq = prod-prod tlam d (ttrans eq' eq)
  prod-prod (pack v) (pack d d') eq = absurd (TypeReduction.¬-prod-≡ₜ-exists (tsym eq))
  prod-prod (pack v) (type-eq d eq') eq = prod-prod (pack v) d (ttrans eq' eq)
  prod-prod (prod v v') (prod d d') eq = _ , v , v' , refl
  prod-prod (prod v v') (type-eq d eq') eq = prod-prod (prod v v') d (ttrans eq' eq)
  prod-prod (left v) (left d) eq = absurd (TypeReduction.¬-prod-≡ₜ-sum (tsym eq))
  prod-prod (left v) (type-eq d eq') eq = prod-prod (left v) d (ttrans eq' eq)
  prod-prod (right v) (right d) eq = absurd (TypeReduction.¬-prod-≡ₜ-sum (tsym eq))
  prod-prod (right v) (type-eq d eq') eq = prod-prod (right v) d (ttrans eq' eq)

  sum-either : ∀ {m Δ τ τ₁ τ₂} {t : Term m 0}
    → Value t
    → Δ ⹁ [] ⊢ t ∶ τ
    → τ ≡ₜ sum τ₁ τ₂
    → Σ (Term _ _) λ t' → Value t' × ((t ≡ left t') ⊎ (t ≡ right t'))
  sum-either lam (lam d) eq = absurd (TypeReduction.¬-sum-≡ₜ-arrow (tsym eq))
  sum-either lam (type-eq d eq') eq = sum-either lam d (ttrans eq' eq)
  sum-either tlam (tlam d) eq = absurd (TypeReduction.¬-sum-≡ₜ-all (tsym eq))
  sum-either tlam (type-eq d eq') eq = sum-either tlam d (ttrans eq' eq)
  sum-either (pack v) (pack d d') eq = absurd (TypeReduction.¬-sum-≡ₜ-exists (tsym eq))
  sum-either (pack v) (type-eq d eq') eq = sum-either (pack v) d (ttrans eq' eq)
  sum-either (prod v v') (prod d d') eq = absurd (TypeReduction.¬-prod-≡ₜ-sum eq)
  sum-either (prod v v') (type-eq d eq') eq = sum-either (prod v v') d (ttrans eq' eq)
  sum-either (left v) (left d) eq = _ , v , inl refl
  sum-either (left v) (type-eq d eq') eq = _ , v , inl refl
  sum-either (right v) (right d) eq = _ , v , inr refl
  sum-either (right v) (type-eq d eq') eq = _ , v , inr refl

progress : ∀ {m Δ τ} (t : Term m zero)
  → Δ ⹁ [] ⊢ t ∶ τ
  → Value t ⊎ Σ (Term m zero) (λ t' → t ⟶ t')
progress (var ()) var
progress _ (lam _) = inl lam
progress (app t t') (app d d') with progress t d
... | inr (t , step) = inr (_ , app₁ step)
... | inl v with CanonicalForms.arrow-lam v d trefl | progress t' d'
...   | _ , refl | inr (t' , step) = inr (_ , app₂ lam step)
...   | _ , refl | inl v' = inr (_ , app-lam v')
progress _ (tlam _) = inl tlam
progress (tapp t τ) (tapp d _) with progress t d
... | inr (t , step) = inr (_ , tapp step)
... | inl v with CanonicalForms.all-tlam v d trefl
...   | _ , refl = inr (_ , tapp-tlam)
progress (pack τ t τ') (pack d d') with progress t d
... | inr (t , step) = inr (_ , pack step)
... | inl v = inl (pack v)
progress (unpack t t') (unpack d d') with progress t d
... | inr (t , step) = inr (_ , unpack step)
... | inl v with CanonicalForms.exists-pack v d trefl
...    | _ , v' , refl  = inr (_ , unpack-pack v')
progress (prod t t') (prod d d') with progress t d
... | inr (t , step) = inr (_ , prod₁ step )
... | inl v with progress t' d'
...   | inr (t' , step) = inr (_ , prod₂ v step)
...   | inl v' = inl (prod v v')
progress (proj₁ t) (proj₁ d) with progress t d
... | inr (t , step) = inr (_ , proj₁ step)
... | inl v with CanonicalForms.prod-prod v d trefl
...   | _ , v₁ , v₂ , refl = inr (_ , proj₁-prod v₁ v₂)
progress (proj₂ t) (proj₂ d) with progress t d
... | inr (t , step) = inr (_ , proj₂ step)
... | inl v with CanonicalForms.prod-prod v d trefl
...   | _ , v₁ , v₂ , refl = inr (_ , proj₂-prod v₁ v₂)
progress (left t) (left d) with progress t d
... | inr (t , step) = inr (_ , left step)
... | inl v = inl (left v)
progress (right t) (right d) with progress t d
... | inr (t , step) = inr (_ , right step)
... | inl v = inl (right v)
progress (match t t₁ t₂) (match d d₁ d₂) with progress t d
... | inr (t , step) = inr (_ , match step)
... | inl v with CanonicalForms.sum-either v d trefl
... | _ , v' , inl refl = inr (_ , match-left v')
... | _ , v' , inr refl = inr (_ , match-right v')
progress t (type-eq d eq) = progress t d