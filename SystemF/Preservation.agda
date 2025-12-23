module SystemF.Preservation where

open import Prelude
import Prelude.Fin as Fin
import Prelude.PropositionalEquality as Eq
open import Substitution
open import SystemF.Syntax
open import SystemF.Semantics
import SystemF.Substitution
open import SystemF.Typing
import SystemF.TypeReduction as TypeReduction

module TypeRenaming where
  open Instantiate SystemF.Substitution.instantiate-fin-type hiding (var; weaken) public
  open Instantiate SystemF.Substitution.instantiate-type-type using (weaken) public
  module Tp = SubstituteSelf SystemF.Substitution.substitute-self-type

  _∶_⇒_ : ∀ {m m'} (σ : Subst Fin m m') (Δ : TypeContext m) (Δ' : TypeContext m') → Set
  σ ∶ Δ ⇒ Δ' = ZipWith (λ x κ → Δ' ⊢ var x ∶ κ) σ Δ

  infix 3 _∶_⇒_

  weaken-⊢ :
    ∀ {m x κ κ'} {Δ : TypeContext m}
    → Δ ⊢ var x ∶ κ
    → (κ' ∷ Δ) ⊢ var (succ x) ∶ κ
  weaken-⊢ var = var

  weaken-⇒ : ∀ {m m' κ} {σ : Subst Fin m m'} {Δ : TypeContext m} {Δ' : TypeContext m'}
    → σ ∶ Δ ⇒ Δ'
    → map succ σ ∶ Δ ⇒ (κ ∷ Δ')
  weaken-⇒ [] = []
  weaken-⇒ (d ∷ ds) = weaken-⊢ d ∷ weaken-⇒ ds

  id-⇒ : ∀ {m} {Δ : TypeContext m} → id ∶ Δ ⇒ Δ
  id-⇒ {Δ = []} = []
  id-⇒ {Δ = κ ∷ Δ} = var ∷ weaken-⇒ id-⇒

  lift-⇒ : ∀ {k m m'} {σ : Subst Fin m m'} (Δ₁ : TypeContext k) {Δ : TypeContext m} {Δ' : TypeContext m'}
    → σ ∶ Δ ⇒ Δ'
    → lift k σ ∶ (Δ₁ ++ Δ) ⇒ (Δ₁ ++ Δ')
  lift-⇒ [] ds = ds
  lift-⇒ (κ ∷ Δ₁) ds = var ∷ weaken-⇒ (lift-⇒ Δ₁ ds)

  weakening-⇒ : ∀ {m κ} {Δ : TypeContext m} → weakening ∶ Δ ⇒ (κ ∷ Δ)
  weakening-⇒ = weaken-⇒ id-⇒

  lookup-⇒ : ∀ {m m'} {σ : Subst Fin m m'} {Δ : TypeContext m} {Δ' : TypeContext m'} (v : Fin m)
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⊢ var (lookup σ v) ∶ lookup Δ v
  lookup-⇒ zero (d ∷ _) = d
  lookup-⇒ (succ v) (_ ∷ ds) = lookup-⇒ v ds

  preserves-kind : ∀ {m m' Δ Δ' κ τ} (σ : Subst Fin m m')
    → Δ ⊢ τ ∶ κ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⊢ subst σ τ ∶ κ
  preserves-kind σ var h = lookup-⇒ _ h
  preserves-kind σ (arrow d d') h = arrow (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (all d) h = all (preserves-kind (lift 1 σ) d (lift-⇒ (_ ∷ []) h))
  preserves-kind σ (exists d) h = exists (preserves-kind (lift 1 σ) d (lift-⇒ (_ ∷ []) h))
  preserves-kind σ (lam d) h = lam (preserves-kind (lift 1 σ) d (lift-⇒ (_ ∷ []) h))
  preserves-kind σ (app d d') h = app (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (prod d d') h = prod (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (sum d d') h = sum (preserves-kind σ d h) (preserves-kind σ d' h)

  map-weaken-renaming-commutes : ∀ {m m' n} {σ : Subst Fin m m'} {Γ : TermContext m n}
    → map weaken (map (subst σ) Γ)
    ≡ map (subst (lift 1 σ)) (map weaken Γ)
  map-weaken-renaming-commutes {σ = σ} {Γ = Γ} =
    map weaken (map (subst σ) Γ)
      ≡⟨ map-map weaken (subst σ) Γ ⟩
    map (λ τ → weaken (subst σ τ)) Γ
      ≡⟨ map-ext _ _ Γ Tp.weaken-renaming-commutes ⟩
    map (λ τ → subst (lift 1 σ) (weaken τ)) Γ
      ≡⟨ sym (map-map (subst (lift 1 σ)) weaken Γ) ⟩
    map (subst (lift 1 σ)) (map weaken Γ)
      ∎

module TypeSubst where
  open Instantiate SystemF.Substitution.instantiate-type-type hiding (var) public
  module Tp = SubstituteSelf SystemF.Substitution.substitute-self-type

  _∶_⇒_ : ∀ {m m'} (σ : Subst Type m m') (Δ : TypeContext m) (Δ' : TypeContext m') → Set
  σ ∶ Δ ⇒ Δ' = ZipWith (λ τ κ → Δ' ⊢ τ ∶ κ) σ Δ

  infix 3 _∶_⇒_

  weaken-⊢ :
    ∀ {m} {Δ : TypeContext m} {κ κ'} {τ}
    → Δ ⊢ τ ∶ κ
    → (κ' ∷ Δ) ⊢ weaken τ ∶ κ
  weaken-⊢ d = TypeRenaming.preserves-kind TypeRenaming.weakening d TypeRenaming.weakening-⇒

  weaken-⇒ : ∀ {m m'} {σ : Subst Type m m'} {Δ : TypeContext m} {Δ' : TypeContext m'} {κ}
    → σ ∶ Δ ⇒ Δ'
    → map weaken σ ∶ Δ ⇒ (κ ∷ Δ')
  weaken-⇒ [] = []
  weaken-⇒ (d ∷ ds) = weaken-⊢ d ∷ weaken-⇒ ds

  id-⇒ : ∀ {m} {Δ : TypeContext m} → id ∶ Δ ⇒ Δ
  id-⇒ {Δ = []} = []
  id-⇒ {Δ = x ∷ Δ} = var ∷ weaken-⇒ id-⇒

  weakening-⇒ : ∀ {m} {κ} {Δ : TypeContext m} → weakening ∶ Δ ⇒ (κ ∷ Δ)
  weakening-⇒ = weaken-⇒ id-⇒

  lift-⇒ : ∀ {m m'} {σ : Subst Type m m'} {Δ : TypeContext m} {Δ' : TypeContext m'} {κ}
    → σ ∶ Δ ⇒ Δ'
    → lift 1 σ ∶ (κ ∷ Δ) ⇒ (κ ∷ Δ')
  lift-⇒ ds = var ∷ weaken-⇒ ds

  lookup-⇒ : ∀ {m m'} {σ : Subst Type m m'} {Δ : TypeContext m} {Δ' : TypeContext m'} (v : Fin m)
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⊢ lookup σ v ∶ lookup Δ v
  lookup-⇒ zero (d ∷ _) = d
  lookup-⇒ (succ v) (_ ∷ ds) = lookup-⇒ v ds

  preserves-kind : ∀ {m m' Δ Δ' κ τ} (σ : Subst Type m m')
    → Δ ⊢ τ ∶ κ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⊢ subst σ τ ∶ κ

  preserves-kind σ var h = lookup-⇒ _ h
  preserves-kind σ (arrow d d') h = arrow (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (all d) h = all (preserves-kind (lift 1 σ) d (lift-⇒ h))
  preserves-kind σ (exists d) h = exists (preserves-kind (lift 1 σ) d (lift-⇒ h))
  preserves-kind σ (lam d) h = lam (preserves-kind (lift 1 σ) d (lift-⇒ h))
  preserves-kind σ (app d d') h = app (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (prod d d') h = prod (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (sum d d') h = sum (preserves-kind σ d h) (preserves-kind σ d' h)

  preserves-equality : ∀ {m m' τ τ'} (σ : Subst Type m m')
    → τ ≡ₜ τ'
    → subst σ τ ≡ₜ subst σ τ'
  preserves-equality σ trefl = trefl
  preserves-equality σ (tsym eq) = tsym (preserves-equality σ eq)
  preserves-equality σ (ttrans eq eq') = ttrans (preserves-equality σ eq) (preserves-equality σ eq')
  preserves-equality σ (arrow eq eq') = arrow (preserves-equality σ eq) (preserves-equality σ eq')
  preserves-equality σ (all eq) = all (preserves-equality (lift 1 σ) eq)
  preserves-equality σ (exists eq) = exists (preserves-equality (lift 1 σ) eq)
  preserves-equality σ (lam eq) = lam (preserves-equality (lift 1 σ) eq)
  preserves-equality σ (app eq eq') = app (preserves-equality σ eq) (preserves-equality σ eq')
  preserves-equality σ (app-lam {τ = τ} {τ' = τ'}) = Eq.subst (_≡ₜ_ _) (sym (Tp.subst-instantiate τ τ')) app-lam
  preserves-equality σ (prod eq eq') = prod (preserves-equality σ eq) (preserves-equality σ eq')
  preserves-equality σ (sum eq eq') = sum (preserves-equality σ eq) (preserves-equality σ eq')

  map-weaken-subst-commutes : ∀ {m m' n} {σ : Subst Type m m'} {Γ : TermContext m n}
    → map weaken (map (subst σ) Γ)
    ≡ map (subst (lift 1 σ)) (map weaken Γ)
  map-weaken-subst-commutes {σ = σ} {Γ = Γ} =
    map weaken (map (subst σ) Γ)
      ≡⟨ map-map weaken (subst σ) Γ ⟩
    map (λ τ → weaken (subst σ τ)) Γ
      ≡⟨ map-ext _ _ Γ Tp.weaken-commutes ⟩
    map (λ τ → subst (lift 1 σ) (weaken τ)) Γ
      ≡⟨ sym (map-map (subst (lift 1 σ)) weaken Γ) ⟩
    map (subst (lift 1 σ)) (map weaken Γ)
      ∎

module TermTypeRenaming where
  open TypeRenaming using (_∶_⇒_; lift-⇒; preserves-kind; module Tp) public
  module _ {n : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-fin-term-type {n = n}) hiding (var) public

  preserves-type : ∀ {m m' n Δ Δ' t τ} {Γ : TermContext m n} (σ : Subst Fin m m')
    → Δ ⹁ Γ ⊢ t ∶ τ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⹁ map (TypeRenaming.subst σ) Γ ⊢ subst σ t ∶ TypeRenaming.subst σ τ
  preserves-type {Γ = Γ} σ var h =
    Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p) (lookup-map (TypeRenaming.subst σ) Γ _) var
  preserves-type σ (lam d) h =
    lam (preserves-type σ d h)
  preserves-type σ (app d d') h =
    app (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (tlam d) h =
    tlam (Eq.subst (λ p → _ ⹁ p ⊢ _ ∶ _) (sym TypeRenaming.map-weaken-renaming-commutes) (preserves-type (TypeRenaming.lift 1 σ) d (lift-⇒ (_ ∷ []) h)))
  preserves-type σ (tapp {τ = τ} {τ' = τ'} d d') h =
    Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p) (sym (Tp.rename-instantiate τ τ')) (tapp (preserves-type σ d h) (preserves-kind σ d' h))
  preserves-type σ (pack {τ = τ} {τ' = τ'} d d') h =
    pack (Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p) (Tp.rename-instantiate τ τ' ) (preserves-type σ d h)) (preserves-kind σ d' h)
  preserves-type {Δ' = Δ'} {Γ} σ (unpack {κ = κ} {τ' = τ'} {t = t} {t' = t'} d d') h =
    unpack
      (preserves-type  σ d h)
      (subst₂
        (λ p q → κ ∷ Δ' ⹁ p ⊢ subst (TypeRenaming.lift 1 σ) t' ∶ q)
        (cong (_∷_ _) (sym TypeRenaming.map-weaken-renaming-commutes))
        (sym (Tp.weaken-renaming-commutes τ'))
        (preserves-type (TypeRenaming.lift 1 σ) d' (lift-⇒ (κ ∷ []) h))
      )
  preserves-type σ (prod d d') h = prod (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (proj₁ d) h = proj₁ (preserves-type σ d h)
  preserves-type σ (proj₂ d) h = proj₂ (preserves-type σ d h)
  preserves-type σ (left d) h = left (preserves-type σ d h)
  preserves-type σ (right d) h = right (preserves-type σ d h)
  preserves-type σ (match d d₁ d₂) h = match (preserves-type σ d h) (preserves-type σ d₁ h) (preserves-type σ d₂ h)
  preserves-type σ (type-eq d eq) h = type-eq (preserves-type σ d h) (TypeReduction.renaming-≡ₜ eq)

module TermTypeSubst where
  open TypeSubst using (_∶_⇒_; lift-⇒; preserves-kind; module Tp) public
  module _ {n : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-type-term-type {n = n}) using (subst; instantiate) public
    open Weaken (SystemF.Substitution.weaken-term-type {n = n}) public

  preserves-type : ∀ {m m' n Δ Δ' t τ} {Γ : TermContext m n} (σ : Subst Type m m')
    → Δ ⹁ Γ ⊢ t ∶ τ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⹁ map (TypeSubst.subst σ) Γ ⊢ subst σ t ∶ TypeSubst.subst σ τ
  preserves-type {Γ = Γ} σ var h =
    Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p) (lookup-map (TypeSubst.subst σ) Γ _) var
  preserves-type σ (lam d) h =
    lam (preserves-type σ d h)
  preserves-type σ (app d d') h =
    app (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (tlam d) h =
    tlam (Eq.subst (λ p → _ ⹁ p ⊢ _ ∶ _) (sym TypeSubst.map-weaken-subst-commutes) (preserves-type (TypeSubst.lift 1 σ) d (lift-⇒ h)))
  preserves-type σ (tapp {τ = τ} {τ' = τ'} d d') h =
    Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p) (sym (Tp.subst-instantiate τ τ')) (tapp (preserves-type σ d h) (preserves-kind σ d' h))
  preserves-type σ (pack {τ = τ} {τ' = τ'} d d') h =
    pack (Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p) (Tp.subst-instantiate τ τ' ) (preserves-type σ d h)) (preserves-kind σ d' h)
  preserves-type {Δ' = Δ'} {Γ} σ (unpack {κ = κ} {τ' = τ'} {t = t} {t' = t'} d d') h =
    unpack
      (preserves-type  σ d h)
      (subst₂
        (λ p q → κ ∷ Δ' ⹁ p ⊢ subst (TypeSubst.lift 1 σ) t' ∶ q)
        (cong (_∷_ _) (sym TypeSubst.map-weaken-subst-commutes))
        (sym (Tp.weaken-commutes τ'))
        (preserves-type (TypeSubst.lift 1 σ) d' (lift-⇒ h))
      )
  preserves-type σ (prod d d') h = prod (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (proj₁ d) h = proj₁ (preserves-type σ d h)
  preserves-type σ (proj₂ d) h = proj₂ (preserves-type σ d h)
  preserves-type σ (left d) h = left (preserves-type σ d h)
  preserves-type σ (right d) h = right (preserves-type σ d h)
  preserves-type σ (match d d₁ d₂) h = match (preserves-type σ d h) (preserves-type σ d₁ h) (preserves-type σ d₂ h)
  preserves-type σ (type-eq d eq) h =
    type-eq (preserves-type σ d h) (TypeSubst.preserves-equality σ eq)

  map-instantiate-map-weaken : ∀ {m n τ} {Γ : TermContext m n}
    → map (TypeSubst.instantiate τ) (map TypeSubst.weaken Γ) ≡ Γ
  map-instantiate-map-weaken {τ = τ}{Γ = Γ} =
    map (TypeSubst.instantiate τ) (map TypeSubst.weaken Γ)
      ≡⟨ map-map (TypeSubst.instantiate τ) TypeSubst.weaken Γ ⟩
    map (λ x → TypeSubst.instantiate τ (TypeSubst.weaken x)) Γ
      ≡⟨ map-ext _ _ Γ (λ x → TypeSubst.Tp.instantiate-weaken) ⟩
    map (λ x → x) Γ
      ≡⟨ map-id Γ ⟩
    Γ
      ∎

  instantiate-preserves-type : ∀ {m n Δ t τ τ' κ} {Γ : TermContext m n}
    → (κ ∷ Δ) ⹁ map TypeSubst.weaken Γ ⊢ t ∶ τ
    → Δ ⊢ τ' ∶ κ
    → Δ ⹁ Γ ⊢ instantiate τ' t ∶ TypeSubst.instantiate τ' τ
  instantiate-preserves-type {τ' = τ'} {Γ = Γ} d d' =
    Eq.subst (λ p → _ ⹁ p ⊢ _ ∶ _) map-instantiate-map-weaken (preserves-type (τ' ∷ TypeSubst.id) d (d' ∷ TypeSubst.id-⇒))


module TermRenaming where
  module _ {m : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-fin-term {m = m}) hiding (var; lift; weaken) public
  open Var var-fin hiding (var; id; weakening)

  _⊢_∶_⇒_ : ∀ {m n n'} (Δ : TypeContext m) (σ : Subst Fin n n') (Γ : TermContext m n) (Γ' : TermContext m n') → Set
  Δ ⊢ σ ∶ Γ ⇒ Γ' = ZipWith (λ x τ → Δ ⹁ Γ' ⊢ var x ∶ τ) σ Γ

  infix 3 _⊢_∶_⇒_

  weaken-⊢ : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ τ' x}
    → Δ ⹁ Γ ⊢ var x ∶ τ
    → Δ ⹁ (τ' ∷ Γ) ⊢ var (weaken x) ∶ τ
  weaken-⊢ var = var
  weaken-⊢ (type-eq d eq) = type-eq (weaken-⊢ d) eq

  weaken-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst Fin n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} {τ}
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⊢ map weaken σ ∶ Γ ⇒ (τ ∷ Γ')
  weaken-⇒ [] = []
  weaken-⇒ (d ∷ ds) = weaken-⊢ d ∷ weaken-⇒ ds

  id-⇒ : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} → Δ ⊢ id {m = m} ∶ Γ ⇒ Γ
  id-⇒ {Γ = []} = []
  id-⇒ {Γ = τ ∷ Δ} = var ∷ weaken-⇒ id-⇒

  weakening-⇒ : ∀ {m n τ} {Δ : TypeContext m} {Γ : TermContext m n} → Δ ⊢ weakening {m = m} ∶ Γ ⇒ (τ ∷ Γ)
  weakening-⇒ = weaken-⇒ id-⇒

  lift-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst Fin n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} {τ}
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⊢ lift 1 σ ∶ (τ ∷ Γ) ⇒ (τ ∷ Γ')
  lift-⇒ d = var ∷ weaken-⇒ d

  lift-type-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst Fin n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} {κ}
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → (κ ∷ Δ) ⊢ map (λ x → x) σ ∶ map TypeSubst.weaken Γ ⇒ map TypeSubst.weaken Γ'
  lift-type-⇒ [] = []
  lift-type-⇒ (d ∷ ds) = TermTypeRenaming.preserves-type TypeRenaming.weakening d TypeRenaming.weakening-⇒ ∷ lift-type-⇒ ds

  lookup-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst Fin n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} (v : Fin n)
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⹁ Γ' ⊢ var (lookup σ v) ∶ lookup Γ v
  lookup-⇒ zero (d ∷ _) = d
  lookup-⇒ (succ v) (_ ∷ ds) = lookup-⇒ v ds

  preserves-type : ∀ {m n n'} (σ : Subst Fin n n') {Δ} {Γ : TermContext m n} {Γ' : TermContext m n'} {τ : Type m} {t : Term m n}
    → Δ ⹁ Γ ⊢ t ∶ τ
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⹁ Γ' ⊢ subst σ t ∶ τ
  preserves-type σ var h = lookup-⇒ _ h
  preserves-type σ (lam d) h = lam (preserves-type (lift 1 σ) d (lift-⇒ h))
  preserves-type σ (app d d') h = app (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (tlam d) h = tlam (preserves-type (map (λ x → x) σ) d (lift-type-⇒ h))
  preserves-type σ (tapp d d') h = tapp (preserves-type σ d h) d'
  preserves-type σ (pack d d') h = pack (preserves-type σ d h) d'
  preserves-type σ (unpack d d') h = unpack (preserves-type σ d h) (preserves-type (lift 1 (map (λ x → x) σ)) d' (lift-⇒ (lift-type-⇒ h)))
  preserves-type σ (prod d d') h = prod (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (proj₁ d) h = proj₁ (preserves-type σ d h)
  preserves-type σ (proj₂ d) h = proj₂ (preserves-type σ d h)
  preserves-type σ (left d) h = left (preserves-type σ d h)
  preserves-type σ (right d) h = right (preserves-type σ d h)
  preserves-type σ (match d d₁ d₂) h = match (preserves-type σ d h) (preserves-type (lift 1 σ) d₁ (lift-⇒ h)) (preserves-type (lift 1 σ) d₂ (lift-⇒ h))
  preserves-type σ (type-eq d eq) h = type-eq (preserves-type σ d h) eq

module TermSubst where
  module _ {m : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-term-term {m = m}) hiding (var) public

  _⊢_∶_⇒_ : ∀ {m n n'} (Δ : TypeContext m) (σ : Subst (Term m) n n') (Γ : TermContext m n) (Γ' : TermContext m n') → Set
  Δ ⊢ σ ∶ Γ ⇒ Γ' = ZipWith (λ t τ → Δ ⹁ Γ' ⊢ t ∶ τ) σ Γ

  infix 3 _⊢_∶_⇒_

  weaken-⊢ : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ τ' t}
    → Δ ⹁ Γ ⊢ t ∶ τ
    → Δ ⹁ (τ' ∷ Γ) ⊢ weaken t ∶ τ
  weaken-⊢ {m = m} d = TermRenaming.preserves-type (TermRenaming.weakening {m = m}) d TermRenaming.weakening-⇒

  weaken-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst (Term m) n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} {τ}
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⊢ map weaken σ ∶ Γ ⇒ (τ ∷ Γ')
  weaken-⇒ [] = []
  weaken-⇒ (d ∷ ds) = weaken-⊢ d ∷ weaken-⇒ ds

  id-⇒ : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} → Δ ⊢ id {m = m} ∶ Γ ⇒ Γ
  id-⇒ {Γ = []} = []
  id-⇒ {Γ = τ ∷ Δ} = var ∷ weaken-⇒ id-⇒

  lift-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst (Term m) n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} {τ}
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⊢ lift 1 σ ∶ (τ ∷ Γ) ⇒ (τ ∷ Γ')
  lift-⇒ d = var ∷ weaken-⇒ d

  lift-type-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst (Term m) n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} {κ}
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → (κ ∷ Δ) ⊢ map TermTypeSubst.weaken σ ∶ map TypeSubst.weaken Γ ⇒ map TypeSubst.weaken Γ'
  lift-type-⇒ [] = []
  lift-type-⇒ (d ∷ ds) = TermTypeRenaming.preserves-type TypeRenaming.weakening d TypeRenaming.weakening-⇒ ∷ lift-type-⇒ ds

  lookup-⇒ : ∀ {m n n'} {Δ : TypeContext m} {σ : Subst (Term m) n n'} {Γ : TermContext m n} {Γ' : TermContext m n'} (v : Fin n)
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⹁ Γ' ⊢ lookup σ v ∶ lookup Γ v
  lookup-⇒ zero (d ∷ _) = d
  lookup-⇒ (succ v) (_ ∷ ds) = lookup-⇒ v ds

  preserves-type : ∀ {m n n'} (σ : Subst (Term m) n n') {Δ} {Γ : TermContext m n} {Γ' : TermContext m n'} {τ : Type m} {t : Term m n}
    → Δ ⹁ Γ ⊢ t ∶ τ
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → Δ ⹁ Γ' ⊢ subst σ t ∶ τ
  preserves-type σ var h = lookup-⇒ _ h
  preserves-type σ (lam d) h = lam (preserves-type (lift 1 σ) d (lift-⇒ h))
  preserves-type σ (app d d') h = app (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (tlam d) h = tlam (preserves-type (map TermTypeSubst.weaken σ) d (lift-type-⇒ h))
  preserves-type σ (tapp d d') h = tapp (preserves-type σ d h) d'
  preserves-type σ (pack d d') h = pack (preserves-type σ d h) d'
  preserves-type σ (unpack d d') h = unpack (preserves-type σ d h) (preserves-type (lift 1 (map TermTypeSubst.weaken σ)) d' (lift-⇒ (lift-type-⇒ h)))
  preserves-type σ (prod d d') h = prod (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (proj₁ d) h = proj₁ (preserves-type σ d h)
  preserves-type σ (proj₂ d) h = proj₂ (preserves-type σ d h)
  preserves-type σ (left d) h = left (preserves-type σ d h)
  preserves-type σ (right d) h = right (preserves-type σ d h)
  preserves-type σ (match d d₁ d₂) h = match (preserves-type σ d h) (preserves-type (lift 1 σ) d₁ (lift-⇒ h)) (preserves-type (lift 1 σ) d₂ (lift-⇒ h))
  preserves-type σ (type-eq d eq) h = type-eq (preserves-type σ d h) eq

preservation : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {t t' τ}
  → Δ ⹁ Γ ⊢ t ∶ τ
  → t ⟶ t'
  → Δ ⹁ Γ ⊢ t' ∶ τ
preservation (app d d') (app₁ step) = app (preservation d step) d'
preservation (app d d') (app₂ v step) = app d (preservation d' step)
preservation (app d d') (app-lam v) =
  let eq , d'' = TypeReduction.lam-inversion d trefl
  in TermSubst.preserves-type (TermSubst.instantiation _) d'' (type-eq d' (tsym eq) ∷ TermSubst.id-⇒)
preservation (tapp d d') (tapp step) = tapp (preservation d step) d'
preservation (tapp d d') tapp-tlam with TypeReduction.tlam-inversion d trefl
... | refl , d'' = TermTypeSubst.instantiate-preserves-type d'' d'
preservation (pack d d') (pack step) = pack (preservation d step) d'
preservation (unpack d d') (unpack step) = unpack (preservation d step) d'
preservation (unpack d d') (unpack-pack v) with TypeReduction.pack-inversion d trefl
... | refl , eq , d'' , d''' =
  TermSubst.preserves-type
    (TermSubst.instantiation _)
    (Eq.subst₂
      (λ p q → _ ⹁ (_ ∷ p) ⊢ _ ∶ q)
      TermTypeSubst.map-instantiate-map-weaken
      TypeSubst.Tp.instantiate-weaken
      (TermTypeSubst.preserves-type (TypeSubst.instantiation _) d' (d''' ∷ TypeSubst.id-⇒)))
    (type-eq d'' (TypeReduction.subst-≡ₜ eq) ∷ TermSubst.id-⇒)
preservation (prod d d') (prod₁ step) = prod (preservation d step) d'
preservation (prod d d') (prod₂ v step) = prod d (preservation d' step)
preservation (proj₁ d) (proj₁ step) = proj₁ (preservation d step)
preservation (proj₁ d) (proj₁-prod v v') = TypeReduction.prod-inversion d trefl .fst
preservation (proj₂ d) (proj₂ step) = proj₂ (preservation d step)
preservation (proj₂ d) (proj₂-prod v v') = TypeReduction.prod-inversion d trefl .snd
preservation (left d) (left step) = left (preservation d step)
preservation (right d) (right step) = right (preservation d step)
preservation (match d d₁ d₂) (match step) = match (preservation d step) d₁ d₂
preservation (match d d₁ d₂) (match-left v) =
  TermSubst.preserves-type (TermSubst.instantiation _) d₁ (TypeReduction.left-inversion d trefl ∷ TermSubst.id-⇒)
preservation (match d d₁ d₂) (match-right v) =
  TermSubst.preserves-type (TermSubst.instantiation _) d₂ (TypeReduction.right-inversion d trefl ∷ TermSubst.id-⇒)
preservation (type-eq d eq) step = type-eq (preservation d step) eq