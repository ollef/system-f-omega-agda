module SystemF.Preservation where

open import Prelude
import Prelude.Fin as Fin
import Prelude.PropositionalEquality as Eq
open import Substitution
open import SystemF.Syntax
open import SystemF.Semantics
import SystemF.Substitution
open import SystemF.Typing

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

  renames-map : ∀ {size m m'} (σ : Subst Fin m m') (τs : Vector (Type m) size)
    → SystemF.Substitution.SubstType.substs SystemF.Substitution.hoist-fin-type σ τs ≡ map (subst σ) τs
  renames-map = SystemF.Substitution.SubstType.substs-map SystemF.Substitution.hoist-fin-type

  preserves-kind : ∀ {m m' Δ Δ' κ τ} (σ : Subst Fin m m')
    → Δ ⊢ τ ∶ κ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⊢ subst σ τ ∶ κ

  preserves-kinds : ∀ {size m m' Δ Δ'} {τs : Vector (Type m) size} (σ : Subst Fin m m')
    → All (λ τ → Δ ⊢ τ ∶ star) τs
    → σ ∶ Δ ⇒ Δ'
    → All (λ τ → Δ' ⊢ τ ∶ star) (map (subst σ) τs)

  preserves-kind σ var h = lookup-⇒ _ h
  preserves-kind σ (arrow d d') h = arrow (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (all d) h = all (preserves-kind (lift 1 σ) d (lift-⇒ (_ ∷ []) h))
  preserves-kind σ (exists d) h = exists (preserves-kind (lift 1 σ) d (lift-⇒ (_ ∷ []) h))
  preserves-kind σ (lam d) h = lam (preserves-kind (lift 1 σ) d (lift-⇒ (_ ∷ []) h))
  preserves-kind σ (app d d') h = app (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (record- ds) h =
    record- (Eq.subst (All _) (sym (renames-map σ _)) (preserves-kinds σ ds h))
  preserves-kind σ (variant ds) h =
    variant (Eq.subst (All _) (sym (renames-map σ _)) (preserves-kinds σ ds h))

  preserves-kinds σ [] h = []
  preserves-kinds σ (d ∷ ds) h = preserves-kind σ d h ∷ preserves-kinds σ ds h

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

  substs-map : ∀ {size m m'} (σ : Subst Type m m') (τs : Vector (Type m) size)
    → SystemF.Substitution.SubstType.substs SystemF.Substitution.hoist-type-type σ τs ≡ map (subst σ) τs
  substs-map = SystemF.Substitution.SubstType.substs-map SystemF.Substitution.hoist-type-type

  preserves-kind : ∀ {m m' Δ Δ' κ τ} (σ : Subst Type m m')
    → Δ ⊢ τ ∶ κ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⊢ subst σ τ ∶ κ

  preserves-kinds : ∀ {size m m' Δ Δ'} {τs : Vector (Type m) size} (σ : Subst Type m m')
    → All (λ τ → Δ ⊢ τ ∶ star) τs
    → σ ∶ Δ ⇒ Δ'
    → All (λ τ → Δ' ⊢ τ ∶ star) (map (subst σ) τs)

  preserves-kind σ var h = lookup-⇒ _ h
  preserves-kind σ (arrow d d') h = arrow (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (all d) h = all (preserves-kind (lift 1 σ) d (lift-⇒ h))
  preserves-kind σ (exists d) h = exists (preserves-kind (lift 1 σ) d (lift-⇒ h))
  preserves-kind σ (lam d) h = lam (preserves-kind (lift 1 σ) d (lift-⇒ h))
  preserves-kind σ (app d d') h = app (preserves-kind σ d h) (preserves-kind σ d' h)
  preserves-kind σ (record- ds) h =
    record- (Eq.subst (All _) (sym (substs-map σ _)) (preserves-kinds σ ds h))
  preserves-kind σ (variant ds) h =
    variant (Eq.subst (All _) (sym (substs-map σ _)) (preserves-kinds σ ds h))

  preserves-kinds σ [] h = []
  preserves-kinds σ (d ∷ ds) h = preserves-kind σ d h ∷ preserves-kinds σ ds h

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

  renames-map : ∀ {size m m' n} (σ : Subst Fin m m') (ts : Vector (Term m n) size)
    → SystemF.Substitution.SubstTermType.substs SystemF.Substitution.hoist-fin-type σ ts ≡ map (subst σ) ts
  renames-map = SystemF.Substitution.SubstTermType.substs-map SystemF.Substitution.hoist-fin-type

  preserves-type : ∀ {m m' n Δ Δ' t τ} {Γ : TermContext m n} (σ : Subst Fin m m')
    → Δ ⹁ Γ ⊢ t ∶ τ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⹁ map (TypeRenaming.subst σ) Γ ⊢ subst σ t ∶ TypeRenaming.subst σ τ

  preserves-types : ∀ {m m' size n Δ Δ'} {ts : Vector _ size} {τs} {Γ : TermContext m n} (σ : Subst Fin m m')
    → ZipWith (λ t τ → Δ ⹁ Γ ⊢ t ∶ τ) ts τs
    → σ ∶ Δ ⇒ Δ'
    → ZipWith (λ t τ → Δ' ⹁ map (TypeRenaming.subst σ) Γ ⊢ t ∶ τ) (map (subst σ) ts) (map (TypeRenaming.subst σ) τs)

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
  preserves-type σ (record- {τs = τs} {ts = ts} ds) h =
    record-
      (subst₂
        (λ p q → ZipWith _ p q)
        (sym (renames-map σ ts))
        (sym (TypeRenaming.renames-map σ τs))
        (preserves-types σ ds h))
  preserves-type σ (proj {τs = τs} {x = x} d) h =
    Eq.subst
      (λ p → _ ⹁ _ ⊢ _ ∶ p)
      (trans (cong (λ p → lookup p x) (TypeRenaming.renames-map σ τs)) (lookup-map (TypeRenaming.subst σ) τs x))
      (proj (preserves-type σ d h))
  preserves-type σ (variant {τs = τs} {x = x} d) h =
    variant
      (Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p)
        (trans (sym (lookup-map (TypeRenaming.subst σ) τs _)) (cong (λ p → lookup p x) (sym (TypeRenaming.renames-map σ τs))))
        (preserves-type σ d h))

  preserves-types σ [] _ = []
  preserves-types σ (d ∷ ds) l = preserves-type σ d l ∷ preserves-types σ ds l

module TermTypeSubst where
  open TypeSubst using (_∶_⇒_; lift-⇒; preserves-kind; module Tp) public
  module _ {n : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-type-term-type {n = n}) using (subst) public
    open Weaken (SystemF.Substitution.weaken-term-type {n = n}) public

  substs-map : ∀ {size m m' n} (σ : Subst Type m m') (ts : Vector (Term m n) size)
    → SystemF.Substitution.SubstTermType.substs SystemF.Substitution.hoist-type-type σ ts ≡ map (subst σ) ts
  substs-map = SystemF.Substitution.SubstTermType.substs-map SystemF.Substitution.hoist-type-type

  preserves-type : ∀ {m m' n Δ Δ' t τ} {Γ : TermContext m n} (σ : Subst Type m m')
    → Δ ⹁ Γ ⊢ t ∶ τ
    → σ ∶ Δ ⇒ Δ'
    → Δ' ⹁ map (TypeSubst.subst σ) Γ ⊢ subst σ t ∶ TypeSubst.subst σ τ

  preserves-types : ∀ {m m' size n Δ Δ'} {ts : Vector _ size} {τs} {Γ : TermContext m n} (σ : Subst Type m m')
    → ZipWith (λ t τ → Δ ⹁ Γ ⊢ t ∶ τ) ts τs
    → σ ∶ Δ ⇒ Δ'
    → ZipWith (λ t τ → Δ' ⹁ map (TypeSubst.subst σ) Γ ⊢ t ∶ τ) (map (subst σ) ts) (map (TypeSubst.subst σ) τs)

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
  preserves-type σ (record- {τs = τs} {ts = ts} ds) h =
    record-
      (subst₂
        (λ p q → ZipWith _ p q)
        (sym (substs-map σ ts))
        (sym (TypeSubst.substs-map σ τs))
        (preserves-types σ ds h))
  preserves-type σ (proj {τs = τs} {x = x} d) h =
    Eq.subst
      (λ p → _ ⹁ _ ⊢ _ ∶ p)
      (trans (cong (λ p → lookup p x) (TypeSubst.substs-map σ τs)) (lookup-map (TypeSubst.subst σ) τs x))
      (proj (preserves-type σ d h))
  preserves-type σ (variant {τs = τs} {x = x} d) h =
    variant
      (Eq.subst (λ p → _ ⹁ _ ⊢ _ ∶ p)
        (trans (sym (lookup-map (TypeSubst.subst σ) τs _)) (cong (λ p → lookup p x) (sym (TypeSubst.substs-map σ τs))))
        (preserves-type σ d h))

  preserves-types σ [] _ = []
  preserves-types σ (d ∷ ds) l = preserves-type σ d l ∷ preserves-types σ ds l

module TermRenaming where
  module _ {m : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-fin-term {m = m}) hiding (var; lift; weaken) public
  open Var var-fin hiding (var; id; weakening)

  renames-map : ∀ {size m n n'} (σ : Subst Fin n n') (ts : Vector (Term m n) size)
    → SystemF.Substitution.SubstTerm.substs SystemF.Substitution.weaken-const-fin SystemF.Substitution.hoist-fin-term σ ts ≡ map (subst σ) ts
  renames-map = SystemF.Substitution.SubstTerm.substs-map SystemF.Substitution.weaken-const-fin SystemF.Substitution.hoist-fin-term

  _⊢_∶_⇒_ : ∀ {m n n'} (Δ : TypeContext m) (σ : Subst Fin n n') (Γ : TermContext m n) (Γ' : TermContext m n') → Set
  Δ ⊢ σ ∶ Γ ⇒ Γ' = ZipWith (λ x τ → Δ ⹁ Γ' ⊢ var x ∶ τ) σ Γ

  infix 3 _⊢_∶_⇒_

  weaken-⊢ : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ τ' x}
    → Δ ⹁ Γ ⊢ var x ∶ τ
    → Δ ⹁ (τ' ∷ Γ) ⊢ var (weaken x) ∶ τ
  weaken-⊢ var = var

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
  preserves-types : ∀ {m n n' len} (σ : Subst Fin n n'){Δ} {Γ : TermContext m n} {Γ' : TermContext m n'} {τs : Vector (Type m) len} {ts : Vector (Term m n) len}
    → ZipWith (λ t τ → Δ ⹁ Γ ⊢ t ∶ τ) ts τs
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → ZipWith (λ t τ → Δ ⹁ Γ' ⊢ t ∶ τ) (map (subst σ) ts) τs

  preserves-type σ var h = lookup-⇒ _ h
  preserves-type σ (lam d) h = lam (preserves-type (lift 1 σ) d (lift-⇒ h))
  preserves-type σ (app d d') h = app (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (tlam d) h = tlam (preserves-type (map (λ x → x) σ) d (lift-type-⇒ h))
  preserves-type σ (tapp d d') h = tapp (preserves-type σ d h) d'
  preserves-type σ (pack d d') h = pack (preserves-type σ d h) d'
  preserves-type σ (unpack d d') h = unpack (preserves-type σ d h) (preserves-type (lift 1 (map (λ x → x) σ)) d' (lift-⇒ (lift-type-⇒ h)))
  preserves-type σ (record- ds) h = record- (Eq.subst (λ p → ZipWith _ p _) (sym (renames-map σ _)) (preserves-types σ ds h))
  preserves-type σ (proj d) h = proj (preserves-type σ d h)
  preserves-type σ (variant d) h = variant (preserves-type σ d h)

  preserves-types σ [] _ = []
  preserves-types σ (d ∷ ds) l = preserves-type σ d l ∷ preserves-types σ ds l

module TermSubst where
  module _ {m : ℕ} where
    open Instantiate (SystemF.Substitution.instantiate-term-term {m = m}) hiding (var) public

  substs-map : ∀ {size m n n'} (σ : Subst (Term m) n n') (ts : Vector (Term m n) size)
    → SystemF.Substitution.SubstTerm.substs SystemF.Substitution.weaken-term-type SystemF.Substitution.hoist-term-term σ ts ≡ map (subst σ) ts
  substs-map = SystemF.Substitution.SubstTerm.substs-map SystemF.Substitution.weaken-term-type SystemF.Substitution.hoist-term-term

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
  preserves-types : ∀ {m n n' len} (σ : Subst (Term m) n n'){Δ} {Γ : TermContext m n} {Γ' : TermContext m n'} {τs : Vector (Type m) len} {ts : Vector (Term m n) len}
    → ZipWith (λ t τ → Δ ⹁ Γ ⊢ t ∶ τ) ts τs
    → Δ ⊢ σ ∶ Γ ⇒ Γ'
    → ZipWith (λ t τ → Δ ⹁ Γ' ⊢ t ∶ τ) (map (subst σ) ts) τs

  preserves-type σ var h = lookup-⇒ _ h
  preserves-type σ (lam d) h = lam (preserves-type (lift 1 σ) d (lift-⇒ h))
  preserves-type σ (app d d') h = app (preserves-type σ d h) (preserves-type σ d' h)
  preserves-type σ (tlam d) h = tlam (preserves-type (map TermTypeSubst.weaken σ) d (lift-type-⇒ h))
  preserves-type σ (tapp d d') h = tapp (preserves-type σ d h) d'
  preserves-type σ (pack d d') h = pack (preserves-type σ d h) d'
  preserves-type σ (unpack d d') h = unpack (preserves-type σ d h) (preserves-type (lift 1 (map TermTypeSubst.weaken σ)) d' (lift-⇒ (lift-type-⇒ h)))
  preserves-type σ (record- ds) h = record- (Eq.subst (λ p → ZipWith _ p _) (sym (substs-map σ _)) (preserves-types σ ds h))
  preserves-type σ (proj d) h = proj (preserves-type σ d h)
  preserves-type σ (variant d) h = variant (preserves-type σ d h)

  preserves-types σ [] _ = []
  preserves-types σ (d ∷ ds) l = preserves-type σ d l ∷ preserves-types σ ds l

preservation : ∀ {t t' τ}
  → [] ⹁ [] ⊢ t ∶ τ
  → t ⟶ t'
  → [] ⹁ [] ⊢ t' ∶ τ
preservation var ()
preservation (lam d) ()
preservation (app d d') (app₁ step) = app (preservation d step) d'
preservation (app d d') (app₂ x step) = app d (preservation d' step)
preservation (app (lam d) d') (lam-app x) = TermSubst.preserves-type (TermSubst.instantiation _) d (d' ∷ [])
preservation (tlam d) ()
preservation (tapp d d') (tapp step) = tapp (preservation d step) d'
preservation (tapp (tlam d) d') tlam-tapp = TermTypeSubst.preserves-type (TypeSubst.instantiation _) d (d' ∷ [])
preservation (pack d d') (pack step) = pack (preservation d step) d'
preservation (unpack d d') (unpack step) = unpack (preservation d step) d'
preservation (unpack (pack d d') d'') (unpack-pack {τ = τ} {τ' = τ'} x) =
  TermSubst.preserves-type
    (TermSubst.instantiation _)
    (Eq.subst
      (λ p → _ ⹁ _ ⊢ _ ∶ p)
      TypeSubst.Tp.instantiate-weaken
      (TermTypeSubst.preserves-type (TypeSubst.instantiation τ) d'' (d' ∷ []))) (d ∷ [])
preservation (record- ds) (record- {i = i} vs step) = record- (lemma ds i step)
  where
    lemma : ∀ {n ts τs t'}
      → ZipWith (λ t τ → [] ⹁ [] ⊢ t ∶ τ) ts τs
      → (i : Fin n)
      → lookup ts i ⟶ t'
      → ZipWith (λ t τ → [] ⹁ [] ⊢ t ∶ τ) (update i t' ts) τs
    lemma (d ∷ ds) zero step = preservation d step ∷ ds
    lemma (d ∷ ds) (succ i) step = d ∷ lemma ds i step
preservation (proj d) (proj step) = proj (preservation d step)
preservation (proj (record- ds)) (proj-record {i = i} vs) = lookup-zip-with ds i
preservation (variant d) (variant step) = variant (preservation d step)