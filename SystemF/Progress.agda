module SystemF.Progress where

open import Prelude
open import SystemF.Semantics
open import SystemF.Syntax
open import SystemF.Typing

progress : ∀ {m Δ τ} (t : Term m zero)
  → Δ ⹁ [] ⊢ t ∶ τ
  → Value t ⊎ Σ (Term m zero) (λ t' → t ⟶ t')
progress-record : ∀ {size m Δ τs} (ts : Vector (Term m zero) size)
  → ZipWith (λ t τ → Δ ⹁ [] ⊢ t ∶ τ) ts τs
  → All Value ts ⊎
    Σ (Fin size × Term m zero)
      (λ (x , t') → All Value (take x ts) × (lookup ts x ⟶ t'))

progress (var ()) var
progress _ (lam _) = inl lam
progress (app t t') (app d d') with progress t d
... | inr (t , step) = inr (_ , app₁ step)
... | inl lam with progress t' d'
...   | inr (t' , step) = inr (_ , app₂ lam step)
...   | inl v = inr (_ , lam-app v)
progress _ (tlam _) = inl tlam
progress (tapp t τ) (tapp d _) with progress t d
... | inr (t , step) = inr (_ , tapp step)
... | inl tlam = inr (_ , tlam-tapp)
progress (pack τ t τ') (pack d d') with progress t d
... | inr (t , step) = inr (_ , pack step)
... | inl v = inl (pack v)
progress (unpack t t') (unpack d d') with progress t d
... | inr (t , step) = inr (_ , unpack step)
progress (unpack _ t') (unpack (pack d x) d') | inl (pack v) = inr (_ , unpack-pack v)
progress (record- ts) (record- ds) with progress-record ts ds
... | inl vs = inl (record- vs)
... | inr (_ , vs , step) = inr (_ , record- vs step)
progress (proj t x) (proj d) with progress t d
progress (proj t x) (proj (record- d)) | inl (record- vs) = inr (_ , proj-record vs)
... | inr (t , step) = inr (_ , proj step)
progress (variant x t) (variant d) with progress t d
... | inl v = inl (variant v)
... | inr (t , step) = inr (_ , variant step)

progress-record [] [] = inl []
progress-record (t ∷ ts) (d ∷ ds) with progress t d
... | inr (t' , step) = inr (((zero , t'), [] , step))
... | inl v with progress-record ts ds
...   | inl vs = inl (v ∷ vs)
...   | inr ((i , st') , vs , step) = inr ((succ i , st') , v ∷ vs , step)