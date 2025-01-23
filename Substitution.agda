-- An adaptation of Data.Fin.Substitution from Agda's standard library.
open import Prelude
import Prelude.Fin as Fin

Subst : (ℕ → Set) → ℕ → ℕ → Set
Subst T m n = Vector (T n) m

data Substs (T : ℕ → Set) : ℕ → ℕ → Set where
  [] : ∀ {n} → Substs T n n
  _∷_ : ∀ {m n o} → Subst T n o → Substs T m n → Substs T m o

infixr 5 _∷_

extensionality : ∀ {T m n} {σ₁ σ₂ : Subst T m n} →
  (∀ i → lookup σ₁ i ≡ lookup σ₂ i) → σ₁ ≡ σ₂
extensionality = lookup-ext _ _

record Weaken (T : ℕ → Set) : Set where
  field
    weaken : ∀ {n} → T n → T (succ n)

weaken-fin : Weaken Fin
weaken-fin = record
  { weaken = succ
  }

record Var (T : ℕ → Set) : Set where
  field
    super-weaken : Weaken T
    var : ∀ {n} → Fin n → T n

  open Weaken super-weaken public

  field
    weaken-var : ∀ {n} (x : Fin n) → weaken (var x) ≡ var (succ x)

  lift : ∀ {m n} k → Subst T m n → Subst T (k + m) (k + n)
  lift zero σ = σ
  lift (succ k) σ = var zero ∷ map weaken (lift k σ)

  lifts : ∀ {m n} k → Substs T m n → Substs T (k + m) (k + n)
  lifts k [] = []
  lifts k (σ ∷ σs) = lift k σ ∷ lifts k σs

  id : ∀ {n} → Subst T n n
  id {n = zero} = []
  id {n = succ n} = lift 1 id

  weakening : ∀ {n} → Subst T n (succ n)
  weakening = map weaken id

  instantiation : ∀ {n} → T n → Subst T (succ n) n
  instantiation t = t ∷ id

  lift-id : ∀ {n} k → lift k (id {n = n}) ≡ id
  lift-id zero = refl
  lift-id (succ k) = cong₂ _∷_ refl (cong (map weaken) (lift-id k))

  lookup-map-weaken : ∀ {m n} {σ : Subst T m n} x {y}
    → lookup σ x ≡ var y
    → lookup (map weaken σ) x ≡ var (succ y)
  lookup-map-weaken {σ = σ} x {y = y} l =
    lookup (map weaken σ) x
      ≡⟨ lookup-map weaken σ x ⟩
    weaken (lookup σ x)
      ≡⟨ cong weaken l ⟩
    weaken (var y)
      ≡⟨ weaken-var y ⟩
    var (succ y)
      ∎

  lookup-id : ∀ {n} (x : Fin n) → lookup id x ≡ var x
  lookup-weakening : ∀ {n} (x : Fin n) → lookup weakening x ≡ var (succ x)

  lookup-id zero = refl
  lookup-id (succ x) = lookup-weakening x

  lookup-weakening x = lookup-map-weaken {σ = id} x (lookup-id x)

  lookup-lift : ∀ {m n σ} (f : Fin m → Fin n)
    → (∀ x → lookup σ x ≡ var (f x))
    → ∀ k x → lookup (lift k σ) x ≡ var (Fin.lift k f x)
  lookup-lift f l zero x = l x
  lookup-lift f l (succ k) zero = refl
  lookup-lift {σ = σ} f l (succ k) (succ x) =
    lookup-map-weaken {σ = lift k σ} x (lookup-lift f l k x)

  lookup-lift-lift : ∀ {m n σ} (f : Fin m → Fin n)
    → (∀ x → lookup σ (f x) ≡ var x)
    → ∀ k x → lookup (lift k σ) (Fin.lift k f x) ≡ var x
  lookup-lift-lift f l zero x = l x
  lookup-lift-lift f l (succ k) zero = refl
  lookup-lift-lift {σ = σ} f l (succ k) (succ x) =
    lookup-map-weaken {σ = lift k σ} (Fin.lift k f x) (lookup-lift-lift f l k x)

  lookup-lift-weakening : ∀ {n} k (x : Fin (k + n))
    → lookup (lift k weakening) x ≡ var (Fin.lift k succ x)
  lookup-lift-weakening k x = lookup-lift succ lookup-weakening k x

  lookup-lift-lift-weakening : ∀ {n} k l (x : Fin (k + (l + n)))
    → lookup (lift k (lift l weakening)) x ≡ var (Fin.lift k (Fin.lift l succ) x)
  lookup-lift-lift-weakening k l = lookup-lift (Fin.lift l succ) (lookup-lift-weakening l) k

  lookup-lift-instantiation : ∀ {n t} k (x : Fin (k + n))
    → lookup (lift k (instantiation t)) (Fin.lift k succ x) ≡ var x
  lookup-lift-instantiation = lookup-lift-lift succ lookup-id

  lookup-lift-map-weaken : ∀ {m n} {σ : Subst T m n} k x
    → lookup (lift k (map weaken σ)) x ≡ lookup (lift k (lift 1 σ)) (Fin.lift k succ x)
  lookup-lift-map-weaken zero x = refl
  lookup-lift-map-weaken (succ k) zero = refl
  lookup-lift-map-weaken {σ = σ} (succ k) (succ x) =
    lookup (map weaken (lift k (map weaken σ))) x
      ≡⟨ lookup-map weaken (lift k (map weaken σ)) x ⟩
    weaken (lookup (lift k (map weaken σ)) x)
      ≡⟨ cong weaken (lookup-lift-map-weaken k x) ⟩
    weaken (lookup (lift k (lift 1 σ)) (Fin.lift k succ x))
      ≡⟨ sym (lookup-map weaken (lift k (lift 1 σ)) (Fin.lift k succ x)) ⟩
    lookup (map weaken (lift k (lift 1 σ))) (Fin.lift k succ x)
      ∎

var-fin : Var Fin
var-fin = record
  { super-weaken = weaken-fin
  ; var = λ x → x
  ; weaken-var = λ x → refl
  }

record Hoist (S T : ℕ → Set) : Set where
  field
    super-var : Var S
    hoist : ∀ {n} → S n → T n

  open Var super-var public

hoist-fin : ∀ {T} → Var T → Hoist Fin T
hoist-fin var-t = record
  { super-var = var-fin
  ; hoist = var
  }
  where open Var var-t

hoist-self : ∀ {T} → Var T → Hoist T T
hoist-self var-t = record
  { super-var = var-t
  ; hoist = λ t → t
  }

record Substitute (S T : ℕ → Set) : Set where
  field
    subst : ∀ {m n} → Subst S m n → T m → T n

  substs : ∀ {m n} → Substs S m n → T m → T n
  substs [] t = t
  substs (σ ∷ σs) t = subst σ (substs σs t)

  compose : ∀ {m n o} → Subst T m n → Subst S n o → Subst T m o
  compose σ₁ σ₂ = map (subst σ₂) σ₁

record Instantiate {S T : ℕ → Set} (var : Var S) (substitute : Substitute S T) : Set where
  open Substitute substitute public
  open Var var public

  instantiate : ∀ {n} → S n → T (succ n) → T n
  instantiate s = subst (instantiation s)

make-instantiate : ∀ {S T} (var : Var S) (substitute : Substitute S T) → Instantiate var substitute
make-instantiate _ _ = record {}

record SubstituteSelf (T : ℕ → Set) : Set₁ where
  field
    super-var : Var T
    substitute : ∀ {S} → Hoist S T → Substitute S T

  open Instantiate (make-instantiate super-var (substitute (hoist-self super-var))) public
  module Renaming = Instantiate (make-instantiate var-fin (substitute (hoist-fin super-var)))

  field
    subst-var-hoist : ∀ {S} (hoist : Hoist S T) {n n' x} {σ : Subst S n n'}
      → let module SS = Substitute (substitute hoist)
            module H = Hoist hoist
        in SS.subst σ (var x) ≡ H.hoist (lookup σ x)
    substs-var-ext : ∀ {S₁ S₂} (hoist₁ : Hoist S₁ T) (hoist₂ : Hoist S₂ T)
      → ∀ {m n} (σ₁ : Substs S₁ m n) (σ₂ : Substs S₂ m n)
      → let
        module SS₁ = Instantiate (make-instantiate (Hoist.super-var hoist₁) (substitute hoist₁))
        module SS₂ = Instantiate (make-instantiate (Hoist.super-var hoist₂) (substitute hoist₂))
      in (∀ k (x : Fin (k + m)) → SS₁.substs (SS₁.lifts k σ₁) (var x) ≡ SS₂.substs (SS₂.lifts k σ₂) (var x))
      → ∀ k (t : T (k + m)) → SS₁.substs (SS₁.lifts k σ₁) t ≡ SS₂.substs (SS₂.lifts k σ₂) t
    weaken-rename : ∀ {n} {t : T n} → weaken t ≡ Renaming.subst Renaming.weakening t

  subst-var : ∀ {n n' x} {σ : Subst T n n'} → subst σ (var x) ≡ lookup σ x
  subst-var = subst-var-hoist (hoist-self super-var)

  substs-var-ext-self : ∀ {m n} (σ₁ : Substs T m n) (σ₂ : Substs T m n)
    → (∀ k (x : Fin (k + m)) → substs (lifts k σ₁) (var x) ≡ substs (lifts k σ₂) (var x))
    → ∀ k (t : T (k + m)) → substs (lifts k σ₁) t ≡ substs (lifts k σ₂) t
  substs-var-ext-self = substs-var-ext (hoist-self super-var) (hoist-self super-var)

  composes : ∀ {m n} → Substs T m n → Subst T m n
  composes [] = id
  composes (σ ∷ []) = σ
  composes (σ₁ ∷ σ₂ ∷ σs) = compose (composes (σ₂ ∷ σs)) σ₁

  lookup-compose : ∀ {m n o} {σ₁ : Subst T m n} {σ₂ : Subst T n o} x
    → lookup (compose σ₁ σ₂) x ≡ subst σ₂ (lookup σ₁ x)
  lookup-compose {σ₁ = σ₁} {σ₂ = σ₂} x = lookup-map (subst σ₂) σ₁ x

  lookup-composes : ∀ {m n} (σs : Substs T m n) x
    → lookup (composes σs) x ≡ substs σs (var x)
  lookup-composes [] x = lookup-id x
  lookup-composes (σ ∷ []) x = sym subst-var
  lookup-composes (σ ∷ σ' ∷ σs) x =
    lookup (compose (composes (σ' ∷ σs)) σ) x
      ≡⟨ lookup-compose {σ₁ = composes (σ' ∷ σs)} x ⟩
    subst σ (lookup (composes (σ' ∷ σs)) x)
      ≡⟨ cong (subst σ) (lookup-composes (σ' ∷ σs) x) ⟩
    subst σ (substs (σ' ∷ σs) (var x))
      ≡⟨⟩
    substs (σ ∷ σ' ∷ σs) (var x)
      ∎

  substs-ext : ∀ {m n} (σ₁ : Substs T m n) (σ₂ : Substs T m n)
    → (∀ k → composes (lifts k σ₁) ≡ composes (lifts k σ₂))
    → ∀ k (t : T (k + m)) → substs (lifts k σ₁) t ≡ substs (lifts k σ₂) t
  substs-ext σ₁ σ₂ h = substs-var-ext-self σ₁ σ₂ λ k x →
    substs (lifts k σ₁) (var x)
      ≡⟨ sym (lookup-composes (lifts k σ₁) x) ⟩
    lookup (composes (lifts k σ₁)) x
      ≡⟨ cong (λ p → lookup p x) (h k) ⟩
    lookup (composes (lifts k σ₂)) x
      ≡⟨ lookup-composes (lifts k σ₂) x ⟩
    substs (lifts k σ₂) (var x)
      ∎

  subst-id : ∀ {n} (t : T n) → subst id t ≡ t
  subst-id = substs-ext (id ∷ []) [] lift-id 0

  compose-id₂ : ∀ {m n} {σ : Subst T m n} → compose σ id ≡ σ
  compose-id₂ {σ = σ} =
    map (subst id) σ
      ≡⟨ map-ext (subst id) (λ t → t) σ subst-id ⟩
    map (λ t → t) σ
      ≡⟨ map-id σ ⟩
    σ
      ∎

  compose-id₁ : ∀ {m n} {σ : Subst T m n} → compose id σ ≡ σ
  compose-id₁ {σ = σ} = extensionality {T = T} λ x →
    lookup (compose id σ) x
      ≡⟨ lookup-compose {σ₁ = id} x ⟩
    subst σ (lookup id x)
      ≡⟨ cong (subst σ) (lookup-id x) ⟩
    subst σ (var x)
      ≡⟨ subst-var ⟩
    lookup σ x
      ∎

  lookup-compose-lift-weakening : ∀ {m n} k {x} {σ : Subst T (k + succ m) n}
    → lookup (compose (lift k weakening) σ) x ≡ lookup σ (Fin.lift k succ x)
  lookup-compose-lift-weakening k {x = x} {σ = σ} =
    lookup (compose (lift k weakening) σ) x
      ≡⟨ lookup-compose {σ₁ = lift k weakening} x ⟩
    subst σ (lookup (lift k weakening) x)
      ≡⟨ cong (subst σ) (lookup-lift-weakening k x) ⟩
    subst σ (var (Fin.lift k succ x))
      ≡⟨ subst-var ⟩
    lookup σ (Fin.lift k succ x)
      ∎

  compose-lift-lift-weakening : ∀ {n} k l
    → compose (lift l (lift k (weakening {n = n}))) (lift l weakening)
    ≡ compose (lift l weakening) (lift l (lift (succ k) weakening))
  compose-lift-lift-weakening k l = extensionality {T = T} λ x →
    lookup (compose (lift l (lift k weakening)) (lift l weakening)) x
      ≡⟨ lookup-compose {σ₁ = lift l (lift k weakening)} x ⟩
    subst (lift l weakening) (lookup (lift l (lift k weakening)) x)
      ≡⟨ cong (subst _) (lookup-lift-lift-weakening l k x) ⟩
    subst (lift l weakening) (var (Fin.lift l (Fin.lift k succ) x))
      ≡⟨ subst-var ⟩
    lookup (lift l weakening) (Fin.lift l (Fin.lift k succ) x)
      ≡⟨ lookup-lift-weakening l (Fin.lift l (Fin.lift k succ) x) ⟩
    var (Fin.lift l succ (Fin.lift l (Fin.lift k succ) x))
      ≡⟨ cong var (lift-commutes k l x) ⟩
    var (Fin.lift l (Fin.lift (succ k) succ) (Fin.lift l succ x))
      ≡⟨ sym (lookup-lift-lift-weakening l (succ k) (Fin.lift l succ x)) ⟩
    lookup (lift l (lift (succ k) weakening)) (Fin.lift l succ x)
      ≡⟨ sym subst-var ⟩
    subst (lift l (lift (succ k) weakening)) (var (Fin.lift l succ x))
      ≡⟨ cong (subst _) (sym (lookup-lift-weakening l x)) ⟩
    subst (lift l (lift (succ k) weakening)) (lookup (lift l weakening) x)
      ≡⟨ sym (lookup-compose {σ₁ = lift l weakening} x) ⟩
    lookup (compose (lift l weakening) (lift l (lift (succ k) weakening))) x
      ∎

  compose-lift-weakening-instantiation : ∀ {n} {t : T n} k
    → compose (lift k weakening) (lift k (instantiation t)) ≡ id
  compose-lift-weakening-instantiation {t = t} k = extensionality {T = T} λ x →
    lookup (compose (lift k weakening) (lift k (instantiation t))) x
      ≡⟨ lookup-compose-lift-weakening k ⟩
    lookup (lift k (instantiation t)) (Fin.lift k succ x)
      ≡⟨ lookup-lift-instantiation k x ⟩
    var x
      ≡⟨ sym (lookup-id x) ⟩
    lookup id x
      ∎

  compose-weakening-instantiation : ∀ {n} {t : T n}
    → compose weakening (instantiation t) ≡ id
  compose-weakening-instantiation = compose-lift-weakening-instantiation 0

  renaming-subst : ∀ {m m'} {σ : Subst Fin m m'} {t}
    → Renaming.subst σ t ≡ subst (map var σ) t
  renaming-subst {σ = σ} {t = t} =
    substs-var-ext (hoist-fin super-var) (hoist-self super-var) (σ ∷ []) (map var σ ∷ [])
    (λ k x →
      Renaming.subst (Renaming.lift k σ) (var x)
        ≡⟨ subst-var-hoist (hoist-fin super-var) ⟩
      var (lookup (Renaming.lift k σ) x)
        ≡⟨ cong var (Renaming.lookup-lift (lookup σ) (λ _ → refl) k x) ⟩
      var (Fin.lift k (lookup σ) x)
        ≡⟨ sym (lookup-lift (lookup σ) (lookup-map var σ) k x) ⟩
      lookup (lift k (map var σ)) x
        ≡⟨ sym subst-var ⟩
      subst (lift k (map var σ)) (var x)
        ∎
    )
    0 t

  map-var-renaming-id : ∀ {n} → map var (Renaming.id {n = n}) ≡ id
  map-var-renaming-id {n = zero} = refl
  map-var-renaming-id {n = succ n} = cong (_∷_ (var zero)) (
    map var (map succ Renaming.id)
      ≡⟨ map-map var succ Renaming.id ⟩
    map (λ x → var (succ x)) Renaming.id
      ≡⟨ map-ext (λ x → var (succ x)) (λ x → weaken (var x)) Renaming.id (λ x → sym (weaken-var x)) ⟩
    map (λ x → weaken (var x)) Renaming.id
      ≡⟨ sym (map-map weaken var Renaming.id) ⟩
    map weaken (map var Renaming.id)
      ≡⟨ cong (map weaken) map-var-renaming-id ⟩
    map weaken id
      ∎
    )

  map-var-renaming-weakening : ∀ {n} → map var (Renaming.weakening {n = n}) ≡ weakening
  map-var-renaming-weakening =
    map var (map Renaming.weaken Renaming.id)
      ≡⟨ map-map var Renaming.weaken Renaming.id ⟩
    map (λ x → var (succ x)) Renaming.id
      ≡⟨ map-ext (λ x → var (succ x)) (λ x → weaken (var x)) Renaming.id (λ x → sym (weaken-var x)) ⟩
    map (λ x → weaken (var x)) Renaming.id
      ≡⟨ sym (map-map weaken var Renaming.id) ⟩
    map weaken (map var Renaming.id)
      ≡⟨ cong (map weaken) map-var-renaming-id ⟩
    map weaken id
      ∎

  weaken-subst : ∀ {n} {t : T n} → weaken t ≡ subst weakening t
  weaken-subst {t = t} =
    weaken t
      ≡⟨ weaken-rename ⟩
    Renaming.subst Renaming.weakening t
      ≡⟨ renaming-subst ⟩
    subst (map var Renaming.weakening) t
      ≡⟨ cong (λ p → subst p t) map-var-renaming-weakening ⟩
    subst weakening t
      ∎

  map-var-renaming-lift : ∀ {m n} {σ : Subst Fin m n} k → map var (Renaming.lift k σ) ≡ lift k (map var σ)
  map-var-renaming-lift zero = refl
  map-var-renaming-lift {σ = σ} (succ k) = cong (_∷_ (var zero)) (
    map var (map succ (Renaming.lift k σ))
      ≡⟨ map-map var succ (Renaming.lift k σ) ⟩
    map (λ x → var (succ x)) (Renaming.lift k σ)
      ≡⟨ map-ext (λ x → var (succ x)) (λ x → weaken (var x)) (Renaming.lift k σ) (λ x → sym (weaken-var x)) ⟩
    map (λ x → weaken (var x)) (Renaming.lift k σ)
      ≡⟨ sym (map-map weaken var (Renaming.lift k σ)) ⟩
    map weaken (map var (Renaming.lift k σ))
      ≡⟨ cong (map weaken) (map-var-renaming-lift k) ⟩
    map weaken (lift k (map var σ))
      ∎
    )

  private
    lift-1-distributes : ∀ {m n o} {σ₁ : Subst T m n} {σ₂ : Subst T n o}
      → (∀ t → weaken (subst σ₂ t) ≡ subst (lift 1 σ₂) (weaken t))
      → lift 1 (compose σ₁ σ₂) ≡ compose (lift 1 σ₁) (lift 1 σ₂)
    lift-1-distributes {σ₁ = σ₁} {σ₂ = σ₂} h =
      lift 1 (compose σ₁ σ₂)
        ≡⟨⟩
      var zero ∷ map weaken (compose σ₁ σ₂)
        ≡⟨ cong₂ _∷_ (sym subst-var) lemma ⟩
      subst (lift 1 σ₂) (var zero) ∷ compose (map weaken σ₁) (lift 1 σ₂)
        ≡⟨⟩
      compose (lift 1 σ₁) (lift 1 σ₂)
        ∎
      where
        lemma =
          map weaken (compose σ₁ σ₂)
            ≡⟨ map-map weaken (subst σ₂) σ₁ ⟩
          map (λ t → weaken (subst σ₂ t)) σ₁
            ≡⟨ map-ext (λ t → weaken (subst σ₂ t)) (λ t → subst (lift 1 σ₂) (weaken t)) σ₁ h ⟩
          map (λ t → subst (lift 1 σ₂) (weaken t)) σ₁
            ≡⟨ sym (map-map (subst (lift 1 σ₂)) weaken σ₁) ⟩
          compose (map weaken σ₁) (var zero ∷ map weaken σ₂)
            ∎

    lift-distributes' : ∀ {m n o} {σ₁ : Subst T m n} {σ₂ : Subst T n o}
      → (∀ k t → weaken (subst (lift k σ₂) t) ≡ subst (lift (succ k) σ₂) (weaken t))
      → ∀ k → lift k (compose σ₁ σ₂) ≡ compose (lift k σ₁) (lift k σ₂)
    lift-distributes' {σ₁ = σ₁} {σ₂ = σ₂} h zero = refl
    lift-distributes' {σ₁ = σ₁} {σ₂ = σ₂} h (succ k) =
      lift (succ k) (compose σ₁ σ₂)
        ≡⟨ cong (lift 1) (lift-distributes' h k) ⟩
      lift 1 (compose (lift k σ₁) (lift k σ₂))
        ≡⟨ lift-1-distributes (h k) ⟩
      compose (lift (succ k) σ₁) (lift (succ k) σ₂)
        ∎

  map-weaken : ∀ {m n} {σ : Subst T m n} → map weaken σ ≡ compose σ weakening
  map-weaken {σ = σ} =
    map weaken σ
      ≡⟨ map-ext weaken (subst weakening) σ (λ _ → weaken-subst) ⟩
    compose σ weakening
      ∎

  compose-lift-weakening : ∀ {m n} {σ : Subst T m n} k
    → compose (lift k σ) (lift k weakening) ≡ compose (lift k weakening) (lift k (lift 1 σ))
  compose-lift-weakening {σ = σ} k =
    compose (lift k σ) (lift k weakening)
      ≡⟨ sym (lift-distributes' lemma₁ k) ⟩
    lift k (compose σ weakening)
      ≡⟨ cong (lift k) (sym (map-weaken)) ⟩
    lift k (map weaken σ)
      ≡⟨ sym lemma₂ ⟩
    compose (lift k weakening) (lift k (lift 1 σ))
    ∎
    where
      lemma₁ : ∀ k t → weaken (subst (lift k weakening) t) ≡ subst (lift (succ k) weakening) (weaken t)
      lemma₁ k t =
        weaken (subst (lift k weakening) t)
          ≡⟨ weaken-subst ⟩
        subst weakening (subst (lift k weakening) t)
          ≡⟨ substs-ext (weakening ∷ lift k weakening ∷ []) (lift (succ k) weakening ∷ weakening ∷ []) (λ l →  compose-lift-lift-weakening k l) 0 t ⟩
        subst (lift (succ k) weakening) (subst weakening t)
          ≡⟨ cong (subst _) (sym weaken-subst) ⟩
        subst (lift (succ k) weakening) (weaken t)
          ∎
      lemma₂ = extensionality {T = T} λ x →
        lookup (compose (lift k weakening) (lift k (lift 1 σ))) x
          ≡⟨ lookup-compose-lift-weakening k ⟩
        lookup (lift k (lift 1 σ)) (Fin.lift k succ x)
          ≡⟨ sym (lookup-lift-map-weaken k x) ⟩
        lookup (lift k (map weaken σ)) x
          ∎

  compose-weakening : ∀ {m n} {σ : Subst T m n} → compose σ weakening ≡ compose weakening (lift 1 σ)
  compose-weakening = compose-lift-weakening 0

  weakening-commutes : ∀ {m n} {σ : Subst T m n} t
    → subst weakening (subst σ t) ≡ subst (lift 1 σ) (subst weakening t)
  weakening-commutes {σ = σ} =
    substs-ext (weakening ∷ σ ∷ []) (lift 1 σ ∷ weakening ∷ []) compose-lift-weakening 0

  weaken-commutes : ∀ {m n} {σ : Subst T m n} t
    → weaken (subst σ t) ≡ subst (lift 1 σ) (weaken t)
  weaken-commutes {σ = σ} t =
    weaken (subst σ t)
      ≡⟨ weaken-subst ⟩
    subst weakening (subst σ t)
      ≡⟨ weakening-commutes t ⟩
    subst (lift 1 σ) (subst weakening t)
      ≡⟨ cong (subst _) (sym weaken-subst) ⟩
    subst (lift 1 σ) (weaken t)
      ∎

  weaken-renaming-commutes : ∀ {m n} {σ : Subst Fin m n} t
    → weaken (Renaming.subst σ t) ≡ Renaming.subst (Renaming.lift 1 σ) (weaken t)
  weaken-renaming-commutes {σ = σ} t =
    weaken (Renaming.subst σ t)
      ≡⟨ cong weaken renaming-subst ⟩
    weaken (subst (map var σ) t)
      ≡⟨ weaken-commutes t ⟩
    subst (lift 1 (map var σ)) (weaken t)
      ≡⟨ cong (λ p → subst p (weaken t)) (sym (map-var-renaming-lift 1)) ⟩
    subst (map var (Renaming.lift 1 σ)) (weaken t)
      ≡⟨ sym renaming-subst ⟩
    Renaming.subst (Renaming.lift 1 σ) (weaken t)
      ∎

  lift-distributes : ∀ {m n o} {σ₁ : Subst T m n} {σ₂ : Subst T n o} k
    → lift k (compose σ₁ σ₂) ≡ compose (lift k σ₁) (lift k σ₂)
  lift-distributes = lift-distributes' λ k → weaken-commutes

  subst-compose : ∀ {m n o} {σ₁ : Subst T m n} {σ₂ : Subst T n o} t
    → subst (compose σ₁ σ₂) t ≡ subst σ₂ (subst σ₁ t)
  subst-compose {σ₁ = σ₁} {σ₂ = σ₂} = substs-ext (compose σ₁ σ₂ ∷ []) (σ₂ ∷ σ₁ ∷ []) lift-distributes 0

  compose-associative : ∀ {m n o p} {σ₁ : Subst T m n} {σ₂ : Subst T n o} {σ₃ : Subst T o p}
    → compose (compose σ₁ σ₂) σ₃ ≡ compose σ₁ (compose σ₂ σ₃)
  compose-associative {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} =
    map (subst σ₃) (map (subst σ₂) σ₁)
      ≡⟨ map-map (subst σ₃) (subst σ₂) σ₁ ⟩
    map (λ t → subst σ₃ (subst σ₂ t)) σ₁
      ≡⟨ map-ext (λ t → subst σ₃ (subst σ₂ t)) (subst (compose σ₂ σ₃)) σ₁ (λ t → sym (subst-compose t)) ⟩
    map (subst (compose σ₂ σ₃)) σ₁
      ∎

  compose-map-weaken-instantiation : ∀ {m n} {σ : Subst T m n} t
    → compose (map weaken σ) (instantiation t) ≡ σ
  compose-map-weaken-instantiation {σ = σ} t =
    compose (map weaken σ) (instantiation t)
      ≡⟨ cong (λ p → compose p _) (map-weaken) ⟩
    compose (compose σ weakening) (instantiation t)
      ≡⟨ compose-associative ⟩
    compose σ (compose weakening (instantiation t))
      ≡⟨ cong (compose σ) compose-weakening-instantiation ⟩
    compose σ id
      ≡⟨ compose-id₂ ⟩
    σ
      ∎

  instantiate-weaken : ∀ {n} {t t' : T n} → instantiate t' (weaken t) ≡ t
  instantiate-weaken {t = t} {t' = t'} =
    instantiate t' (weaken t)
      ≡⟨ cong (instantiate t') weaken-subst ⟩
    subst (instantiation t') (subst weakening t)
      ≡⟨ sym (subst-compose t) ⟩
    subst (compose weakening (instantiation t')) t
      ≡⟨ cong (λ p → subst p t) compose-weakening-instantiation ⟩
    subst id t
      ≡⟨ subst-id t ⟩
    t
      ∎

  compose-instantiation : ∀ {m n} {σ : Subst T m n} t
    → compose (instantiation t) σ ≡ compose (lift 1 σ) (instantiation (subst σ t))
  compose-instantiation {σ = σ} t =
    compose (instantiation t) σ
      ≡⟨⟩
    subst σ t ∷ compose id σ
      ≡⟨ cong (_∷_ _) compose-id₁ ⟩
    subst σ t ∷ σ
      ≡⟨ cong (_∷_ _) (sym (compose-map-weaken-instantiation (subst σ t))) ⟩
    subst σ t ∷ compose (map weaken σ) (instantiation (subst σ t))
      ≡⟨ cong (λ p → p ∷ compose (map weaken σ) (instantiation (subst σ t))) (sym subst-var) ⟩
    compose (lift 1 σ) (instantiation (subst σ t))
      ∎

  subst-instantiate : ∀ {m n} {σ : Subst T m n} t t'
    → subst σ (instantiate t' t) ≡ instantiate (subst σ t') (subst (lift 1 σ) t)
  subst-instantiate {σ = σ} t t' =
    subst σ (subst (instantiation t') t)
      ≡⟨ sym (subst-compose t) ⟩
    subst (compose (instantiation t') σ) t
      ≡⟨ cong (λ p → subst p t) (compose-instantiation t') ⟩
    subst (compose (lift 1 σ) (instantiation (subst σ t'))) t
      ≡⟨ subst-compose t ⟩
    subst (instantiation (subst σ t')) (subst (lift 1 σ) t)
      ∎

  rename-instantiate : ∀ {m n} {σ : Subst Fin m n} t t'
    → Renaming.subst σ (instantiate t' t) ≡ instantiate (Renaming.subst σ t') (Renaming.subst (Renaming.lift 1 σ) t)
  rename-instantiate {σ = σ} t t' =
    Renaming.subst σ (instantiate t' t)
      ≡⟨ renaming-subst ⟩
    subst (map var σ) (instantiate t' t)
      ≡⟨ subst-instantiate t t' ⟩
    instantiate (subst (map var σ) t') (subst (lift 1 (map var σ)) t)
      ≡⟨ cong₂ (λ p q → instantiate p (subst q t)) (sym renaming-subst) (sym (map-var-renaming-lift 1)) ⟩
    instantiate (Renaming.subst σ t') (subst (map var (Renaming.lift 1 σ)) t)
      ≡⟨ cong (instantiate _) (sym renaming-subst) ⟩
    instantiate (Renaming.subst σ t') (Renaming.subst (Renaming.lift 1 σ) t)
      ∎