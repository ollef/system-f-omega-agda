module SystemF.Substitution where

open import Prelude
import Prelude.Fin as Fin
open import Substitution

open import SystemF.Syntax

module SubstType {T} (hoist-t : Hoist T Type) where
  open Hoist hoist-t

  subst : ∀ {m m'} → Subst T m m' → Type m → Type m'
  substs : ∀ {m m' size} → Subst T m m' → Vector (Type m) size → Vector (Type m') size

  subst σ (var x) = hoist (lookup σ x)
  subst σ (arrow τ τ') = arrow (subst σ τ) (subst σ τ')
  subst σ (all κ τ) = all κ (subst (lift 1 σ) τ)
  subst σ (exists κ τ) = exists κ (subst (lift 1 σ) τ)
  subst σ (lam κ τ) = lam κ (subst (lift 1 σ) τ)
  subst σ (app τ τ') = app (subst σ τ) (subst σ τ')
  subst σ (prod τ τ') = prod (subst σ τ) (subst σ τ')
  subst σ (sum τ τ') = sum (subst σ τ) (subst σ τ')

  substs σ [] = []
  substs σ (τ ∷ τs) = subst σ τ ∷ substs σ τs

  substs-map : ∀ {size m m'} (σ : Subst T m m') (τs : Vector (Type m) size)
    → substs σ τs ≡ map (subst σ) τs
  substs-map σ [] = refl
  substs-map σ (τ ∷ τs) = cong (_∷_ (subst σ τ)) (substs-map σ τs)

substitute-type : ∀ {T} → Hoist T Type → Substitute T Type
substitute-type hoist-t = record
  { subst = SubstType.subst hoist-t
  }

hoist-fin-type : Hoist Fin Type
hoist-fin-type = record
  { super-var = var-fin
  ; hoist = var
  }

rename-type : Substitute Fin Type
rename-type = substitute-type hoist-fin-type

weaken-type : Weaken Type
weaken-type = record
  { weaken = subst weakening
  }
  where open Substitute rename-type
        open Var var-fin

var-type : Var Type
var-type = record
  { super-weaken = weaken-type
  ; var = var
  ; weaken-var = λ x → sym (cong Type.var (sym (lookup-weakening x)))
  }
  where open Var var-fin using (lookup-weakening)

hoist-type-type : Hoist Type Type
hoist-type-type = hoist-self var-type

substitute-type-type : Substitute Type Type
substitute-type-type = substitute-type hoist-type-type

instantiate-type : ∀ {T} (hoist : Hoist T Type) → Instantiate (Hoist.super-var hoist) (substitute-type hoist)
instantiate-type _ = record {}

instantiate-fin-type : Instantiate var-fin rename-type
instantiate-fin-type = instantiate-type hoist-fin-type

instantiate-type-type : Instantiate var-type substitute-type-type
instantiate-type-type = instantiate-type hoist-type-type

module SubstsVarExtTypeLemmas {T} (hoist-t : Hoist T Type) where
  open Hoist hoist-t
  open Substitute (substitute-type hoist-t)
  open SubstType hoist-t using (substs-map) renaming (substs to substs-types)

  arrow-lifts-substs : ∀ {m n} k {τ τ' : Type (k + m)} (σ : Substs T m n) →
    substs (lifts k σ) (arrow τ τ') ≡ arrow (substs (lifts k σ) τ) (substs (lifts k σ) τ')
  arrow-lifts-substs k [] = refl
  arrow-lifts-substs k (σ ∷ σs) = cong (subst _) (arrow-lifts-substs k σs)

  all-lifts-substs : ∀ {m n} k {κ : Kind} {τ : Type (succ (k + m))} (σ : Substs T m n) →
    substs (lifts k σ) (all κ τ) ≡ all κ (substs (lifts (succ k) σ) τ)
  all-lifts-substs k [] = refl
  all-lifts-substs k (σ ∷ σs) = cong (subst _) (all-lifts-substs k σs)

  exists-lifts-substs : ∀ {m n} k {κ : Kind} {τ : Type (succ (k + m))} (σ : Substs T m n) →
    substs (lifts k σ) (exists κ τ) ≡ exists κ (substs (lifts (succ k) σ) τ)
  exists-lifts-substs k [] = refl
  exists-lifts-substs k (σ ∷ σs) = cong (subst _) (exists-lifts-substs k σs)

  lam-lifts-substs : ∀ {m n} k {κ : Kind} {τ : Type (succ (k + m))} (σ : Substs T m n) →
    substs (lifts k σ) (lam κ τ) ≡ lam κ (substs (lifts (succ k) σ) τ)
  lam-lifts-substs k [] = refl
  lam-lifts-substs k (σ ∷ σs) = cong (subst _) (lam-lifts-substs k σs)

  app-lifts-substs : ∀ {m n} k {τ τ' : Type (k + m)} (σ : Substs T m n) →
    substs (lifts k σ) (app τ τ') ≡ app (substs (lifts k σ) τ) (substs (lifts k σ) τ')
  app-lifts-substs k [] = refl
  app-lifts-substs k (σ ∷ σs) = cong (subst _) (app-lifts-substs k σs)

  prod-lifts-substs : ∀ {m n} k {τ τ' : Type (k + m)} (σ : Substs T m n) →
    substs (lifts k σ) (prod τ τ') ≡ prod (substs (lifts k σ) τ) (substs (lifts k σ) τ')
  prod-lifts-substs k [] = refl
  prod-lifts-substs k (σ ∷ σs) = cong (subst _) (prod-lifts-substs k σs)

  sum-lifts-substs : ∀ {m n} k {τ τ' : Type (k + m)} (σ : Substs T m n) →
    substs (lifts k σ) (sum τ τ') ≡ sum (substs (lifts k σ) τ) (substs (lifts k σ) τ')
  sum-lifts-substs k [] = refl
  sum-lifts-substs k (σ ∷ σs) = cong (subst _) (sum-lifts-substs k σs)

module SubstsVarExtType {T₁ T₂} (hoist₁ : Hoist T₁ Type) (hoist₂ : Hoist T₂ Type) where
  module T₁ = Instantiate (make-instantiate (Hoist.super-var hoist₁) (substitute-type hoist₁))
  module T₂ = Instantiate (make-instantiate (Hoist.super-var hoist₂) (substitute-type hoist₂))
  module LemmaT₁ = SubstsVarExtTypeLemmas hoist₁
  module LemmaT₂ = SubstsVarExtTypeLemmas hoist₂

  substs-var-ext
    : ∀ {m n} (σ₁ : Substs T₁ m n) (σ₂ : Substs T₂ m n)
    → (∀ k (x : Fin (k + m)) → T₁.substs (T₁.lifts k σ₁) (Type.var x) ≡ T₂.substs (T₂.lifts k σ₂) (Type.var x))
    → ∀ k (t : Type (k + m)) → T₁.substs (T₁.lifts k σ₁) t ≡ T₂.substs (T₂.lifts k σ₂) t
  substs-var-ext σ₁ σ₂ h k (var x) = h k x
  substs-var-ext σ₁ σ₂ h k (arrow τ τ') =
    T₁.substs (T₁.lifts k σ₁) (arrow τ τ')
      ≡⟨ LemmaT₁.arrow-lifts-substs k σ₁ ⟩
    arrow (T₁.substs (T₁.lifts k σ₁) τ) (T₁.substs (T₁.lifts k σ₁) τ')
      ≡⟨ cong₂ arrow (substs-var-ext σ₁ σ₂ h k τ) (substs-var-ext σ₁ σ₂ h k τ') ⟩
    arrow (T₂.substs (T₂.lifts k σ₂) τ) (T₂.substs (T₂.lifts k σ₂) τ')
      ≡⟨ sym (LemmaT₂.arrow-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (arrow τ τ')
      ∎
  substs-var-ext σ₁ σ₂ h k (all κ τ) =
    T₁.substs (T₁.lifts k σ₁) (all κ τ)
      ≡⟨ LemmaT₁.all-lifts-substs k σ₁ ⟩
    all κ (T₁.substs (T₁.lifts (succ k) σ₁) τ)
      ≡⟨ cong (all κ) (substs-var-ext σ₁ σ₂ h (succ k) τ) ⟩
    all κ (T₂.substs (T₂.lifts (succ k) σ₂) τ)
      ≡⟨ sym (LemmaT₂.all-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (all κ τ)
      ∎
  substs-var-ext σ₁ σ₂ h k (exists κ τ) =
    T₁.substs (T₁.lifts k σ₁) (exists κ τ)
      ≡⟨ LemmaT₁.exists-lifts-substs k σ₁ ⟩
    exists κ (T₁.substs (T₁.lifts (succ k) σ₁) τ)
      ≡⟨ cong (exists κ) (substs-var-ext σ₁ σ₂ h (succ k) τ) ⟩
    exists κ (T₂.substs (T₂.lifts (succ k) σ₂) τ)
      ≡⟨ sym (LemmaT₂.exists-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (exists κ τ)
      ∎
  substs-var-ext σ₁ σ₂ h k (lam κ τ) =
    T₁.substs (T₁.lifts k σ₁) (lam κ τ)
      ≡⟨ LemmaT₁.lam-lifts-substs k σ₁ ⟩
    lam κ (T₁.substs (T₁.lifts (succ k) σ₁) τ)
      ≡⟨ cong (lam κ) (substs-var-ext σ₁ σ₂ h (succ k) τ) ⟩
    lam κ (T₂.substs (T₂.lifts (succ k) σ₂) τ)
      ≡⟨ sym (LemmaT₂.lam-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (lam κ τ)
      ∎
  substs-var-ext σ₁ σ₂ h k (app τ τ') =
    T₁.substs (T₁.lifts k σ₁) (app τ τ')
      ≡⟨ LemmaT₁.app-lifts-substs k σ₁ ⟩
    app (T₁.substs (T₁.lifts k σ₁) τ) (T₁.substs (T₁.lifts k σ₁) τ')
      ≡⟨ cong₂ app (substs-var-ext σ₁ σ₂ h k τ) (substs-var-ext σ₁ σ₂ h k τ') ⟩
    app (T₂.substs (T₂.lifts k σ₂) τ) (T₂.substs (T₂.lifts k σ₂) τ')
      ≡⟨ sym (LemmaT₂.app-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (app τ τ')
      ∎
  substs-var-ext σ₁ σ₂ h k (prod τ τ') =
    T₁.substs (T₁.lifts k σ₁) (prod τ τ')
      ≡⟨ LemmaT₁.prod-lifts-substs k σ₁ ⟩
    prod (T₁.substs (T₁.lifts k σ₁) τ) (T₁.substs (T₁.lifts k σ₁) τ')
      ≡⟨ cong₂ prod (substs-var-ext σ₁ σ₂ h k τ) (substs-var-ext σ₁ σ₂ h k τ') ⟩
    prod (T₂.substs (T₂.lifts k σ₂) τ) (T₂.substs (T₂.lifts k σ₂) τ')
      ≡⟨ sym (LemmaT₂.prod-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (prod τ τ')
      ∎
  substs-var-ext σ₁ σ₂ h k (sum τ τ') =
    T₁.substs (T₁.lifts k σ₁) (sum τ τ')
      ≡⟨ LemmaT₁.sum-lifts-substs k σ₁ ⟩
    sum (T₁.substs (T₁.lifts k σ₁) τ) (T₁.substs (T₁.lifts k σ₁) τ')
      ≡⟨ cong₂ sum (substs-var-ext σ₁ σ₂ h k τ) (substs-var-ext σ₁ σ₂ h k τ') ⟩
    sum (T₂.substs (T₂.lifts k σ₂) τ) (T₂.substs (T₂.lifts k σ₂) τ')
      ≡⟨ sym (LemmaT₂.sum-lifts-substs k σ₂) ⟩
    T₂.substs (T₂.lifts k σ₂) (sum τ τ')
      ∎

substitute-self-type : SubstituteSelf Type
substitute-self-type = record
  { super-var = var-type
  ; substitute = substitute-type
  ; subst-var-hoist = λ _ → refl
  ; substs-var-ext = SubstsVarExtType.substs-var-ext
  ; weaken-rename = refl
  }

module SubstTermType {T} (hoist-t : Hoist T Type) where
  open Hoist hoist-t
  module ST = SubstType hoist-t

  subst : ∀ {m m' n} → Subst T m m' → Term m n → Term m' n
  subst σ (var x) = Term.var x
  subst σ (lam τ t) = lam (ST.subst σ τ) (subst σ t)
  subst σ (app t t') = app (subst σ t) (subst σ t')
  subst σ (tlam κ t) = tlam κ (subst (lift 1 σ) t)
  subst σ (tapp t τ) = tapp (subst σ t) (ST.subst σ τ)
  subst σ (pack τ t τ') = pack (ST.subst σ τ) (subst σ t) (ST.subst σ τ')
  subst σ (unpack t t') = unpack (subst σ t) (subst (lift 1 σ) t')
  subst σ (prod t t') = prod (subst σ t) (subst σ t')
  subst σ (proj₁ t) = proj₁ (subst σ t)
  subst σ (proj₂ t) = proj₂ (subst σ t)
  subst σ (left t) = left (subst σ t)
  subst σ (right t) = right (subst σ t)
  subst σ (match t t' t'') = match (subst σ t) (subst σ t') (subst σ t'')

Flip : ∀ {A B : Set} → (A → B → Set) → B → A → Set
Flip f b a = f a b

substitute-term-type : ∀ {T n} → Hoist T Type → Substitute T (Flip Term n)
substitute-term-type hoist-t = record
  { subst = subst
  }
  where open SubstTermType hoist-t

rename-term-type : ∀ {n} → Substitute Fin (Flip Term n)
rename-term-type = substitute-term-type hoist-fin-type

substitute-term-type-type : ∀ {n} → Substitute Type (Flip Term n)
substitute-term-type-type = substitute-term-type hoist-type-type

instantiate-term-type : ∀ {T n} (hoist : Hoist T Type) → Instantiate (Hoist.super-var hoist) (substitute-term-type {n = n} hoist)
instantiate-term-type _ = record {}

instantiate-fin-term-type : ∀ {n} → Instantiate var-fin (rename-term-type {n = n})
instantiate-fin-term-type = instantiate-term-type hoist-fin-type

instantiate-type-term-type : ∀ {n} → Instantiate var-type (substitute-term-type {n = n} hoist-type-type)
instantiate-type-term-type = instantiate-term-type hoist-type-type

weaken-term-type : ∀ {n} → Weaken (Flip Term n)
weaken-term-type = record
  { weaken = subst weakening
  }
  where open Substitute rename-term-type
        open Var var-fin

module SubstTerm {T : ℕ → ℕ → Set} (weaken-t : ∀ {n} → Weaken (Flip T n)) (hoist-t : ∀ {m} → Hoist (T m) (Term m)) where
  subst : ∀ {m n n'} → Subst (T m) n n' → Term m n → Term m n'
  subst σ (var x) = Hoist.hoist hoist-t (lookup σ x)
  subst σ (lam τ t) = lam τ (subst (Hoist.lift hoist-t 1 σ) t)
  subst σ (app t t') = app (subst σ t) (subst σ t')
  subst σ (tlam κ t) = tlam κ (subst (map (Weaken.weaken weaken-t) σ) t)
  subst σ (tapp t τ) = tapp (subst σ t) τ
  subst σ (pack τ t τ') = pack τ (subst σ t) τ'
  subst σ (unpack t t') = unpack (subst σ t) (subst (Hoist.lift hoist-t 1 (map (Weaken.weaken weaken-t) σ)) t')
  subst σ (prod t t') = prod (subst σ t) (subst σ t')
  subst σ (proj₁ t) = proj₁ (subst σ t)
  subst σ (proj₂ t) = proj₂ (subst σ t)
  subst σ (left t) = left (subst σ t)
  subst σ (right t) = right (subst σ t)
  subst σ (match t t' t'') = match (subst σ t) (subst (Hoist.lift hoist-t 1 σ) t') (subst (Hoist.lift hoist-t 1 σ) t'')

substitute-term : ∀ {T : ℕ → ℕ → Set} {m} → (∀ {n} → Weaken (Flip T n)) → (∀ {m} → Hoist (T m) (Term m)) → Substitute (T m) (Term m)
substitute-term weaken-t hoist-t = record
  { subst = subst
  }
  where open SubstTerm weaken-t hoist-t

weaken-const-fin : ∀ {n} → Weaken (λ _ → Fin n)
weaken-const-fin = record
  { weaken = λ x → x
  }

hoist-fin-term : ∀ {m} → Hoist Fin (Term m)
hoist-fin-term = record
  { super-var = var-fin
  ; hoist = var
  }

rename-term : ∀ {m} → Substitute Fin (Term m)
rename-term = substitute-term weaken-const-fin hoist-fin-term

instantiate-term : ∀ {T : ℕ → ℕ → Set} {m} (weaken : ∀ {n} → Weaken (Flip T n)) (hoist : ∀ {m} → Hoist (T m) (Term m))
  → Instantiate (Hoist.super-var (hoist {m = m})) (substitute-term weaken hoist)
instantiate-term weaken-t hoist-t = record {}

instantiate-fin-term : ∀ {m} → Instantiate var-fin (rename-term {m = m})
instantiate-fin-term = instantiate-term weaken-const-fin hoist-fin-term

weaken-term : ∀ {m} → Weaken (Term m)
weaken-term = record
  { weaken = subst weakening
  }
  where open Substitute rename-term
        open Var var-fin

var-term : ∀ {m} → Var (Term m)
var-term = record
  { super-weaken = weaken-term
  ; var = var
  ; weaken-var = λ x → sym (cong Term.var (sym (lookup-weakening x)))
  }
  where open Var var-fin using (lookup-weakening)

hoist-term-term : ∀ {m} → Hoist (Term m) (Term m)
hoist-term-term = hoist-self var-term

substitute-term-term : ∀ {m} → Substitute (Term m) (Term m)
substitute-term-term = substitute-term weaken-term-type hoist-term-term

instantiate-term-term : ∀ {m} → Instantiate (var-term {m = m}) substitute-term-term
instantiate-term-term = instantiate-term weaken-term-type hoist-term-term
