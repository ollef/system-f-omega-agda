module SystemF.TypeReduction where

open import Prelude
import Prelude.PropositionalEquality as Eq
open import SystemF.Syntax
open import SystemF.Typing
open import SystemF.Substitution
open import Substitution

open SubstituteSelf SystemF.Substitution.substitute-self-type

data _⇛_ {m} : Type m → Type m → Set where
  trefl : ∀ {τ} → τ ⇛ τ
  arrow : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ⇛ τ₁' → τ₂ ⇛ τ₂' → arrow τ₁ τ₂ ⇛ arrow τ₁' τ₂'
  all : ∀ {κ τ τ'} → τ ⇛ τ' → all κ τ ⇛ all κ τ'
  exists : ∀ {κ τ τ'} → τ ⇛ τ' → exists κ τ ⇛ exists κ τ'
  lam : ∀ {κ τ τ'} → τ ⇛ τ' → lam κ τ ⇛ lam κ τ'
  app : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ⇛ τ₁' → τ₂ ⇛ τ₂' → app τ₁ τ₂ ⇛ app τ₁' τ₂'
  app-lam : ∀ {κ τ₁ τ₁' τ₂ τ₂'} → τ₁ ⇛ τ₁' → τ₂ ⇛ τ₂' → app (lam κ τ₁) τ₂ ⇛ instantiate τ₂' τ₁'
  prod : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ⇛ τ₁' → τ₂ ⇛ τ₂' → prod τ₁ τ₂ ⇛ prod τ₁' τ₂'
  sum : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ⇛ τ₁' → τ₂ ⇛ τ₂' → sum τ₁ τ₂ ⇛ sum τ₁' τ₂'

infix 3 _⇛_

data _⇛*_ {m} : Type m → Type m → Set where
  [] : ∀ {τ} → τ ⇛* τ
  _∷_ : ∀ {τ₁ τ₂ τ₃} → τ₁ ⇛ τ₂ → τ₂ ⇛* τ₃ → τ₁ ⇛* τ₃

infix 3 _⇛*_
infix 5 _∷_

_++⇛*_ : ∀ {m} {τ₁ τ₂ τ₃ : Type m} → τ₁ ⇛* τ₂ → τ₂ ⇛* τ₃ → τ₁ ⇛* τ₃
[] ++⇛* steps' = steps'
(step ∷ steps) ++⇛* steps' = step ∷ (steps ++⇛* steps')

infix 4 _++⇛*_

data _⇔*_ {m} : Type m → Type m → Set where
  base : ∀ {τ τ'} → τ ⇛ τ' → τ ⇔* τ'
  tsym : ∀ {τ τ'} → τ ⇔* τ' → τ' ⇔* τ
  ttrans : ∀ {τ₁ τ₂ τ₃} → τ₁ ⇔* τ₂ → τ₂ ⇔* τ₃ → τ₁ ⇔* τ₃

infix 3 _⇔*_

data _≡flat_ {m} : Type m → Type m → Set where
  [] : ∀ {τ} → τ ≡flat τ
  _∷_ : ∀ {τ₁ τ₂ τ₃} → τ₁ ⇛ τ₂ → τ₂ ≡flat τ₃ → τ₁ ≡flat τ₃
  _∷sym_ : ∀ {τ₁ τ₂ τ₃} → τ₂ ⇛ τ₁ → τ₂ ≡flat τ₃ → τ₁ ≡flat τ₃

infix 3 _≡flat_
infix 5 _∷sym_

flat-snoc : ∀ {m} {τ₁ τ₂ τ₃ : Type m} → τ₁ ≡flat τ₂ → τ₂ ⇛ τ₃ → τ₁ ≡flat τ₃
flat-snoc [] step = step ∷ []
flat-snoc (step' ∷ eq) step = step' ∷ flat-snoc eq step
flat-snoc (step' ∷sym eq) step = step' ∷sym flat-snoc eq step

flat-snoc-sym : ∀ {m} {τ₁ τ₂ τ₃ : Type m} → τ₁ ≡flat τ₂ → τ₃ ⇛ τ₂ → τ₁ ≡flat τ₃
flat-snoc-sym [] step = step ∷sym []
flat-snoc-sym (step' ∷ eq) step = step' ∷ flat-snoc-sym eq step
flat-snoc-sym (step' ∷sym eq) step = step' ∷sym flat-snoc-sym eq step

flat-sym : ∀ {m} {τ τ' : Type m} → τ ≡flat τ' → τ' ≡flat τ
flat-sym [] = []
flat-sym (step ∷ eq) = flat-snoc-sym (flat-sym eq) step
flat-sym (step ∷sym eq) = flat-snoc (flat-sym eq) step

flat-trans : ∀ {m} {τ₁ τ₂ τ₃ : Type m} → τ₁ ≡flat τ₂ → τ₂ ≡flat τ₃ → τ₁ ≡flat τ₃
flat-trans [] eq' = eq'
flat-trans (step ∷ eq) eq' = step ∷ flat-trans eq eq'
flat-trans (step ∷sym eq) eq' = step ∷sym flat-trans eq eq'

flat-arrow : ∀ {m} {τ₁ τ₁' τ₂ τ₂' : Type m} → τ₁ ≡flat τ₁' → τ₂ ≡flat τ₂' → arrow τ₁ τ₂ ≡flat arrow τ₁' τ₂'
flat-arrow [] [] = []
flat-arrow [] (step ∷ eq') = arrow trefl step ∷ flat-arrow [] eq'
flat-arrow [] (step ∷sym eq') = arrow trefl step ∷sym flat-arrow [] eq'
flat-arrow (step ∷ eq) eq' = arrow step trefl ∷ flat-arrow eq eq'
flat-arrow (step ∷sym eq) eq' = arrow step trefl ∷sym flat-arrow eq eq'

flat-all : ∀ {m} {κ} {τ τ' : Type (succ m)} → τ ≡flat τ' → all κ τ ≡flat all κ τ'
flat-all [] = []
flat-all (step ∷ eq) = all step ∷ flat-all eq
flat-all (step ∷sym eq) = all step ∷sym flat-all eq

flat-exists : ∀ {m} {κ} {τ τ' : Type (succ m)} → τ ≡flat τ' → exists κ τ ≡flat exists κ τ'
flat-exists [] = []
flat-exists (step ∷ eq) = exists step ∷ flat-exists eq
flat-exists (step ∷sym eq) = exists step ∷sym flat-exists eq

flat-lam : ∀ {m} {κ} {τ τ' : Type (succ m)} → τ ≡flat τ' → lam κ τ ≡flat lam κ τ'
flat-lam [] = []
flat-lam (step ∷ eq) = lam step ∷ flat-lam eq
flat-lam (step ∷sym eq) = lam step ∷sym flat-lam eq

flat-app : ∀ {m} {τ₁ τ₁' τ₂ τ₂' : Type m} → τ₁ ≡flat τ₁' → τ₂ ≡flat τ₂' → app τ₁ τ₂ ≡flat app τ₁' τ₂'
flat-app [] [] = []
flat-app [] (step ∷ eq') = app trefl step ∷ flat-app [] eq'
flat-app [] (step ∷sym eq') = app trefl step ∷sym flat-app [] eq'
flat-app (step ∷ eq) eq' = app step trefl ∷ flat-app eq eq'
flat-app (step ∷sym eq) eq' = app step trefl ∷sym flat-app eq eq'

flat-prod : ∀ {m} {τ₁ τ₁' τ₂ τ₂' : Type m} → τ₁ ≡flat τ₁' → τ₂ ≡flat τ₂' → prod τ₁ τ₂ ≡flat prod τ₁' τ₂'
flat-prod [] [] = []
flat-prod [] (step ∷ eq') = prod trefl step ∷ flat-prod [] eq'
flat-prod [] (step ∷sym eq') = prod trefl step ∷sym flat-prod [] eq'
flat-prod (step ∷ eq) eq' = prod step trefl ∷ flat-prod eq eq'
flat-prod (step ∷sym eq) eq' = prod step trefl ∷sym flat-prod eq eq'

flat-sum : ∀ {m} {τ₁ τ₁' τ₂ τ₂' : Type m} → τ₁ ≡flat τ₁' → τ₂ ≡flat τ₂' → sum τ₁ τ₂ ≡flat sum τ₁' τ₂'
flat-sum [] [] = []
flat-sum [] (step ∷ eq') = sum trefl step ∷ flat-sum [] eq'
flat-sum [] (step ∷sym eq') = sum trefl step ∷sym flat-sum [] eq'
flat-sum (step ∷ eq) eq' = sum step trefl ∷ flat-sum eq eq'
flat-sum (step ∷sym eq) eq' = sum step trefl ∷sym flat-sum eq eq'

flatten : ∀ {m} {τ τ' : Type m} → τ ≡ₜ τ' → τ ≡flat τ'
flatten trefl = []
flatten (tsym eq) = flat-sym (flatten eq)
flatten (ttrans eq eq') = flat-trans (flatten eq) (flatten eq')
flatten (arrow eq eq') = flat-arrow (flatten eq) (flatten eq')
flatten (all eq) = flat-all (flatten eq)
flatten (exists eq) = flat-exists (flatten eq)
flatten (lam eq) = flat-lam (flatten eq)
flatten (app eq eq') = flat-app (flatten eq) (flatten eq')
flatten app-lam = app-lam trefl trefl ∷ []
flatten (prod eq eq') = flat-prod (flatten eq) (flatten eq')
flatten (sum eq eq') = flat-sum (flatten eq) (flatten eq')

flat-reduction : ∀ {m} {τ τ' : Type m} → τ ≡flat τ' → τ ⇔* τ'
flat-reduction [] = base trefl
flat-reduction (step ∷ eq) = ttrans (base step) (flat-reduction eq)
flat-reduction (step ∷sym eq) = ttrans (tsym (base step)) (flat-reduction eq)

type-equality-reduction : ∀ {m} {τ τ' : Type m} → τ ≡ₜ τ' → τ ⇔* τ'
type-equality-reduction eq = flat-reduction (flatten eq)

type-reduction-equality : ∀ {m} {τ τ' : Type m} → τ ⇛ τ' → τ ≡ₜ τ'
type-reduction-equality trefl = trefl
type-reduction-equality (arrow step step') = arrow (type-reduction-equality step) (type-reduction-equality step')
type-reduction-equality (all step) = all (type-reduction-equality step)
type-reduction-equality (exists step) = exists (type-reduction-equality step)
type-reduction-equality (lam step) = lam (type-reduction-equality step)
type-reduction-equality (app step step') = app (type-reduction-equality step) (type-reduction-equality step')
type-reduction-equality (app-lam step step') = ttrans (app (lam (type-reduction-equality step)) (type-reduction-equality step')) app-lam
type-reduction-equality (prod step step') = prod (type-reduction-equality step) (type-reduction-equality step')
type-reduction-equality (sum step step') = sum (type-reduction-equality step) (type-reduction-equality step')

type-reductions-closure-equality : ∀ {m} {τ τ' : Type m} → τ ⇔* τ' → τ ≡ₜ τ'
type-reductions-closure-equality (base step) = type-reduction-equality step
type-reductions-closure-equality (tsym step) = tsym (type-reductions-closure-equality step)
type-reductions-closure-equality (ttrans step step') = ttrans (type-reductions-closure-equality step) (type-reductions-closure-equality step')

type-reductions-equality : ∀ {m} {τ τ' : Type m} → τ ⇛* τ' → τ ≡ₜ τ'
type-reductions-equality [] = trefl
type-reductions-equality (step ∷ steps) = ttrans (type-reduction-equality step) (type-reductions-equality steps)

_⇛subst_ : ∀ {m m'} (σ σ' : Subst Type m m') → Set
σ ⇛subst σ' = ZipWith _⇛_ σ σ'

infix 3 _⇛subst_

renaming-⇛ : ∀ {m m'} {τ τ'} {σ : Subst Fin m m'} → τ ⇛ τ' → Renaming.subst σ τ ⇛ Renaming.subst σ τ'
renaming-⇛ trefl = trefl
renaming-⇛ (arrow step step') = arrow (renaming-⇛ step) (renaming-⇛ step')
renaming-⇛ (all step) = all (renaming-⇛ step)
renaming-⇛ (exists step) = exists (renaming-⇛ step)
renaming-⇛ (lam step) = lam (renaming-⇛ step)
renaming-⇛ (app step step') = app (renaming-⇛ step) (renaming-⇛ step')
renaming-⇛ {σ = σ} (app-lam {κ = κ} {τ₁ = τ₁} {τ₁' = τ₁'} {τ₂ = τ₂} {τ₂' = τ₂'} step step') =
  Eq.subst (λ p → Renaming.subst σ (app (lam κ τ₁) τ₂) ⇛ p) (sym (rename-instantiate τ₁' τ₂')) (app-lam (renaming-⇛ step) (renaming-⇛ step'))
renaming-⇛ (prod step step') = prod (renaming-⇛ step) (renaming-⇛ step')
renaming-⇛ (sum step step') = sum (renaming-⇛ step) (renaming-⇛ step')

renaming-⇛* : ∀ {m m'} {τ τ'} {σ : Subst Fin m m'} → τ ⇛* τ' → Renaming.subst σ τ ⇛* Renaming.subst σ τ'
renaming-⇛* []  = []
renaming-⇛* (step ∷ steps) = renaming-⇛ step ∷ renaming-⇛* steps

lookup-⇛ : ∀ {m m'} {σ σ' : Subst Type m m'} → σ ⇛subst σ' → ∀ x → lookup σ x ⇛ lookup σ' x
lookup-⇛ (step ∷ σ) zero = step
lookup-⇛ (_ ∷ σ) (succ x) = lookup-⇛ σ x

weaken-⇛ : ∀ {m m'} {σ σ' : Subst Type m m'} → σ ⇛subst σ' → map weaken σ ⇛subst map weaken σ'
weaken-⇛ [] = []
weaken-⇛ (step ∷ steps) = renaming-⇛ step ∷ weaken-⇛ steps

lift-⇛ : ∀ {m m'} {σ σ' : Subst Type m m'} → σ ⇛subst σ' → lift 1 σ ⇛subst lift 1 σ'
lift-⇛ σ = trefl ∷  weaken-⇛ σ

id-⇛ : ∀ {m} → id {n = m} ⇛subst id
id-⇛ {m = zero} = []
id-⇛ {m = succ m} = trefl ∷ weaken-⇛ id-⇛

refl-⇛subst : ∀ {m m'} {σ : Subst Type m m'} → σ ⇛subst σ
refl-⇛subst {σ = []} = []
refl-⇛subst {σ = _ ∷ σ} = trefl ∷ refl-⇛subst

instantiation-⇛ : ∀ {m} {τ τ' : Type m} → τ ⇛ τ' → instantiation τ ⇛subst instantiation τ'
instantiation-⇛ step = step ∷ id-⇛

subst-⇛ : ∀ {m m'} {σ σ' : Subst Type m m'} → σ ⇛subst σ' → ∀ τ → subst σ τ ⇛ subst σ' τ
subst-⇛ σ (var x) = lookup-⇛ σ x
subst-⇛ σ (arrow τ τ') = arrow (subst-⇛ σ τ) (subst-⇛ σ τ')
subst-⇛ σ (all x τ) = all (subst-⇛ (lift-⇛ σ) τ)
subst-⇛ σ (exists x τ) = exists (subst-⇛ (lift-⇛ σ) τ)
subst-⇛ σ (lam x τ) = lam (subst-⇛ (lift-⇛ σ) τ)
subst-⇛ σ (app τ τ') = app (subst-⇛ σ τ) (subst-⇛ σ τ')
subst-⇛ σ (prod τ τ') = prod (subst-⇛ σ τ) (subst-⇛ σ τ')
subst-⇛ σ (sum τ τ') = sum (subst-⇛ σ τ) (subst-⇛ σ τ')

subst-⇛-⇛ : ∀ {m m'} {σ σ' : Subst Type m m'} {τ τ'} → τ ⇛ τ' → σ ⇛subst σ' → subst σ τ ⇛ subst σ' τ'
subst-⇛-⇛ (trefl {τ = τ}) σ = subst-⇛ σ τ
subst-⇛-⇛ (arrow step step') σ = arrow (subst-⇛-⇛ step σ) (subst-⇛-⇛ step' σ)
subst-⇛-⇛ (all step) σ = all (subst-⇛-⇛ step (lift-⇛ σ))
subst-⇛-⇛ (exists step) σ = exists (subst-⇛-⇛ step (lift-⇛ σ))
subst-⇛-⇛ (lam step) σ = lam (subst-⇛-⇛ step (lift-⇛ σ))
subst-⇛-⇛ (app step step') σ = app (subst-⇛-⇛ step σ) (subst-⇛-⇛ step' σ)
subst-⇛-⇛ {σ = σ} {σ' = σ'} (app-lam {κ = κ} {τ₁ = τ₁} {τ₁' = τ₁'} {τ₂ = τ₂} {τ₂' = τ₂'} step step') σr =
  Eq.subst (λ p → subst σ (app (lam κ τ₁) τ₂) ⇛ p) (sym (subst-instantiate τ₁' τ₂')) (app-lam (subst-⇛-⇛ step (lift-⇛ σr)) (subst-⇛-⇛ step' σr))
subst-⇛-⇛ (prod step step') σ = prod (subst-⇛-⇛ step σ) (subst-⇛-⇛ step' σ)
subst-⇛-⇛ (sum step step') σ = sum (subst-⇛-⇛ step σ) (subst-⇛-⇛ step' σ)

subst-⇛* : ∀ {m m'} {σ : Subst Type m m'} {τ τ' : Type m} → τ ⇛* τ' → subst σ τ ⇛* subst σ τ'
subst-⇛* [] = []
subst-⇛* (step ∷ steps) = subst-⇛-⇛ step refl-⇛subst ∷ subst-⇛* steps

diamond : ∀ {m} {τ τ₁ τ₂ : Type m} → τ ⇛ τ₁ → τ ⇛ τ₂ → Σ (Type m) λ τ' → τ₁ ⇛ τ' × τ₂ ⇛ τ'
{-# CATCHALL #-}
diamond trefl step₂ = _ , step₂ , trefl
{-# CATCHALL #-}
diamond step₁ trefl = _ , trefl , step₁
diamond (arrow step₁ step₁') (arrow step₂ step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , arrow step₁ step₁' , arrow step₂ step₂'
diamond (all step₁) (all step₂) =
  let (_ , step₁ , step₂) = diamond step₁ step₂
  in _ , all step₁ , all step₂
diamond (exists step₁) (exists step₂) =
  let (_ , step₁ , step₂) = diamond step₁ step₂
  in _ , exists step₁ , exists step₂
diamond (lam step₁) (lam step₂) =
  let (_ , step₁ , step₂) = diamond step₁ step₂
  in _ , lam step₁ , lam step₂
diamond (app step₁ step₁') (app step₂ step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , app step₁ step₁' , app step₂ step₂'
diamond (app trefl step₁') (app-lam {τ₁' = τ₁'} step₂ step₂') =
  let (_ , step₁' , step₂') = diamond step₁' step₂'
  in
  _ , app-lam step₂ step₁' , subst-⇛ (instantiation-⇛ step₂') τ₁'
diamond (app (lam step₁) step₁') (app-lam step₂ step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , app-lam step₁ step₁' , subst-⇛-⇛ step₂ (instantiation-⇛ step₂')
diamond (app-lam {τ₁' = τ₁'} step₁ step₁') (app trefl step₂') =
  let (_ , step₁' , step₂') = diamond step₁' step₂'
  in
  _ , subst-⇛ (instantiation-⇛ step₁') τ₁' , app-lam step₁ step₂'
diamond (app-lam step₁ step₁') (app (lam step₂) step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , subst-⇛-⇛ step₁ (instantiation-⇛ step₁') , app-lam step₂ step₂'
diamond (app-lam step₁ step₁') (app-lam step₂ step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , subst-⇛-⇛ step₁ (instantiation-⇛ step₁') , subst-⇛-⇛ step₂ (instantiation-⇛ step₂')
diamond (prod step₁ step₁') (prod step₂ step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , prod step₁ step₁' , prod step₂ step₂'
diamond (sum step₁ step₁') (sum step₂ step₂') =
  let (_ , step₁ , step₂) = diamond step₁ step₂
      (_ , step₁' , step₂') = diamond step₁' step₂'
  in _ , sum step₁ step₁' , sum step₂ step₂'

strip : ∀ {m} {τ τ₁ τ₂ : Type m} →  τ ⇛ τ₁ → τ ⇛* τ₂ → Σ (Type m) λ τ' → τ₁ ⇛* τ' × τ₂ ⇛ τ'
strip step [] = _ , [] , step
strip step₁₂ (step₁₃ ∷ steps₃₅) =
  let _ , step₂₄ , step₃₄ = diamond step₁₂ step₁₃
      _ , steps₄₆ , step₅₆ = strip step₃₄ steps₃₅
  in _ , (step₂₄ ∷ steps₄₆) , step₅₆

confluence-⇛* : ∀ {m} {τ τ₁ τ₂ : Type m} → τ ⇛* τ₁ → τ ⇛* τ₂ → Σ (Type m) λ τ' → τ₁ ⇛* τ' × τ₂ ⇛* τ'
confluence-⇛* [] steps₂ = _ , steps₂ , []
confluence-⇛* (step₁₂ ∷ steps₂₃) steps₁₄ =
  let _ , steps₂₅ , step₄₅ = strip step₁₂ steps₁₄
      _ , steps₃₆ , steps₅₆ = confluence-⇛* steps₂₃ steps₂₅
  in _ , steps₃₆ , step₄₅ ∷ steps₅₆

confluence-⇔ : ∀ {m} {τ₁ τ₂ : Type m} → τ₁ ⇔* τ₂ → Σ (Type m) λ τ → τ₁ ⇛* τ × τ₂ ⇛* τ
confluence-⇔ (base step) = _ , (step ∷ []) , []
confluence-⇔ (tsym steps) =
  let (_ , steps , steps') = confluence-⇔ steps
  in _ , steps' , steps
confluence-⇔ (ttrans steps steps') =
  let (_ , steps₁ , steps₂) = confluence-⇔ steps
      (_ , steps₁' , steps₂') = confluence-⇔ steps'
      (_ , connect₁ , connect₂) = confluence-⇛* steps₂ steps₁'
  in _ , (steps₁ ++⇛* connect₁) , (steps₂' ++⇛* connect₂)

confluence-≡ₜ : ∀ {m} {τ τ' : Type m} → τ ≡ₜ τ' → Σ (Type m) λ τ'' → τ ⇛* τ'' × τ' ⇛* τ''
confluence-≡ₜ eq = confluence-⇔ (type-equality-reduction eq)

subst-≡ₜ : ∀ {m m'} {σ : Subst Type m m'} {τ τ' : Type m} → τ ≡ₜ τ' → subst σ τ ≡ₜ subst σ τ'
subst-≡ₜ eq with confluence-≡ₜ eq
... | _ , steps , steps' = ttrans (type-reductions-equality (subst-⇛* steps)) (tsym (type-reductions-equality (subst-⇛* steps')))

renaming-≡ₜ : ∀ {m m'} {τ τ' : Type m} {σ : Subst Fin m m'} → τ ≡ₜ τ' → Renaming.subst σ τ ≡ₜ Renaming.subst σ τ'
renaming-≡ₜ eq with confluence-≡ₜ eq
... | _ , steps , steps' = ttrans (type-reductions-equality (renaming-⇛* steps)) (tsym (type-reductions-equality (renaming-⇛* steps')))

arrow-preserved : ∀ {m} {τ₁ τ₂ τ : Type m}
  → arrow τ₁ τ₂ ⇛* τ
  → Σ (Type m × Type m) λ (τ₁' , τ₂') → (τ ≡ arrow τ₁' τ₂') × τ₁ ⇛* τ₁' × τ₂ ⇛* τ₂'
arrow-preserved [] = _ , refl , [] , []
arrow-preserved (trefl ∷ steps) = arrow-preserved steps
arrow-preserved (arrow step step' ∷ steps) =
  let _ , eq , steps₁ , steps₂ = arrow-preserved steps
  in _ , eq , step ∷ steps₁ , step' ∷ steps₂

all-preserved : ∀ {m} {κ τ₁} {τ : Type m}
  → all κ τ₁ ⇛* τ
  → Σ (Type (succ m)) λ τ₂ → (τ ≡ all κ τ₂) × τ₁ ⇛* τ₂
all-preserved [] = _ , refl , []
all-preserved (trefl ∷ steps) = all-preserved steps
all-preserved (all step ∷ steps) =
  let _ , eq , steps' = all-preserved steps
  in _ , eq , step ∷ steps'

prod-preserved : ∀ {m} {τ₁ τ₂ τ : Type m}
  → prod τ₁ τ₂ ⇛* τ
  → Σ (Type m × Type m) λ (τ₁' , τ₂') → (τ ≡ prod τ₁' τ₂') × τ₁ ⇛* τ₁' × τ₂ ⇛* τ₂'
prod-preserved [] = _ , refl , [] , []
prod-preserved (trefl ∷ steps) = prod-preserved steps
prod-preserved (prod step₁ step₂ ∷ steps) =
  let _ , eq , steps₁ , steps₂ = prod-preserved steps
  in _ , eq , step₁ ∷ steps₁ , step₂ ∷ steps₂

sum-preserved : ∀ {m} {τ₁ τ₂ τ : Type m}
  → sum τ₁ τ₂ ⇛* τ
  → Σ (Type m × Type m) λ (τ₁' , τ₂') → (τ ≡ sum τ₁' τ₂') × τ₁ ⇛* τ₁' × τ₂ ⇛* τ₂'
sum-preserved [] = _ , refl , [] , []
sum-preserved (trefl ∷ steps) = sum-preserved steps
sum-preserved (sum step₁ step₂ ∷ steps) =
  let _ , eq , steps₁ , steps₂ = sum-preserved steps
  in _ , eq , step₁ ∷ steps₁ , step₂ ∷ steps₂

exists-preserved : ∀ {m} {κ τ₁} {τ : Type m}
  → exists κ τ₁ ⇛* τ
  → Σ (Type (succ m)) λ τ₂ → (τ ≡ exists κ τ₂) × τ₁ ⇛* τ₂
exists-preserved [] = _ , refl , []
exists-preserved (trefl ∷ steps) = exists-preserved steps
exists-preserved (exists step ∷ steps) =
  let _ , eq , steps' = exists-preserved steps
  in _ , eq , step ∷ steps'

lam-inversion : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ₁ τ₁' τ τ₂ t}
  → Δ ⹁ Γ ⊢ lam τ₁ t ∶ τ
  → τ ≡ₜ arrow τ₁' τ₂
  → (τ₁ ≡ₜ τ₁') × (Δ ⹁ τ₁ ∷ Γ ⊢ t ∶ τ₂)
lam-inversion (lam d) eq with confluence-≡ₜ eq
... | _ , steps , steps' with arrow-preserved steps | arrow-preserved steps'
... | _ , refl , steps₁ , steps₂ | _ , refl , steps₁' , steps₂' =
  ttrans (type-reductions-equality steps₁) (tsym (type-reductions-equality steps₁')) ,
  type-eq d (ttrans (type-reductions-equality steps₂) (tsym (type-reductions-equality steps₂')))
lam-inversion (type-eq d eq) eq' = lam-inversion d (ttrans eq eq')

tlam-inversion : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {κ₁ κ₂ τ τ' t}
  → Δ ⹁ Γ ⊢ tlam κ₁ t ∶ τ
  → τ ≡ₜ all κ₂ τ'
  → (κ₁ ≡ κ₂) × (κ₁ ∷ Δ ⹁ map weaken Γ ⊢ t ∶ τ')
tlam-inversion (tlam d) eq with confluence-≡ₜ eq
... | _ , steps , steps' with all-preserved steps | all-preserved steps'
... | _ , refl , steps₁ | _ , refl , steps₁' =
  refl , type-eq d (ttrans (type-reductions-equality steps₁) (tsym (type-reductions-equality steps₁')))
tlam-inversion (type-eq d x) eq = tlam-inversion d (ttrans x eq)

prod-inversion : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ₁ τ₂ τ t₁ t₂}
  → Δ ⹁ Γ ⊢ prod t₁ t₂ ∶ τ
  → τ ≡ₜ prod τ₁ τ₂
  → (Δ ⹁ Γ ⊢ t₁ ∶ τ₁) × (Δ ⹁ Γ ⊢ t₂ ∶ τ₂)
prod-inversion (prod d d') eq with confluence-≡ₜ eq
... | _ , steps , steps' with prod-preserved steps | prod-preserved steps'
... | _ , refl , steps₁ , steps₂ | _ , refl , steps₁' , steps₂' =
  type-eq d (ttrans (type-reductions-equality steps₁) (tsym (type-reductions-equality steps₁'))) ,
  type-eq d' (ttrans (type-reductions-equality steps₂) (tsym (type-reductions-equality steps₂')))
prod-inversion (type-eq d x) eq = prod-inversion d (ttrans x eq)

left-inversion : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ₁ τ₂ τ t}
  → Δ ⹁ Γ ⊢ left t ∶ τ
  → τ ≡ₜ sum τ₁ τ₂
  → Δ ⹁ Γ ⊢ t ∶ τ₁
left-inversion (left d) eq with confluence-≡ₜ eq
... | _ , steps , steps' with sum-preserved steps | sum-preserved steps'
... | _ , refl , steps₁ , steps₂ | _ , refl , steps₁' , steps₂' =
  type-eq d (ttrans (type-reductions-equality steps₁) (tsym (type-reductions-equality steps₁')))
left-inversion (type-eq d x) eq = left-inversion d (ttrans x eq)

right-inversion : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {τ₁ τ₂ τ t}
  → Δ ⹁ Γ ⊢ right t ∶ τ
  → τ ≡ₜ sum τ₁ τ₂
  → Δ ⹁ Γ ⊢ t ∶ τ₂
right-inversion (right d) eq with confluence-≡ₜ eq
... | _ , steps , steps' with sum-preserved steps | sum-preserved steps'
... | _ , refl , steps₁ , steps₂ | _ , refl , steps₁' , steps₂' =
  type-eq d (ttrans (type-reductions-equality steps₂) (tsym (type-reductions-equality steps₂')))
right-inversion (type-eq d x) eq = right-inversion d (ttrans x eq)

pack-inversion : ∀ {m n} {Δ : TypeContext m} {Γ : TermContext m n} {κ₁ κ₂ τ₀ τ₁ τ₂ τ t}
  → Δ ⹁ Γ ⊢ pack τ₀ t (exists κ₁ τ₁) ∶ τ
  → τ ≡ₜ exists κ₂ τ₂
  → (κ₁ ≡ κ₂) × (τ₁ ≡ₜ τ₂) × (Δ ⹁ Γ ⊢ t ∶ instantiate τ₀ τ₁) × (Δ ⊢ τ₀ ∶ κ₁)
pack-inversion (pack d d') eq with confluence-≡ₜ eq
... | _ , steps , steps' with exists-preserved steps | exists-preserved steps'
... | _ , refl , steps₁ | _ , refl , steps₁' = refl , ttrans (type-reductions-equality steps₁) (tsym (type-reductions-equality steps₁')) , d , d'
pack-inversion (type-eq d x) eq = pack-inversion d (ttrans x eq)

data SameHeads {m} : Type m → Type m → Set where
  arrow : ∀ {τ₁ τ₂ τ₁' τ₂'} → SameHeads (arrow τ₁ τ₂) (arrow τ₁' τ₂')
  all : ∀ {κ τ τ'} → SameHeads (all κ τ) (all κ τ')
  exists : ∀ {κ τ τ'} → SameHeads (exists κ τ) (exists κ τ')
  lam : ∀ {κ τ τ'} → SameHeads (lam κ τ) (lam κ τ')
  app : ∀ {τ₁ τ₂ τ₁' τ₂'} → SameHeads (app τ₁ τ₂) (app τ₁' τ₂')
  prod : ∀ {τ₁ τ₂ τ₁' τ₂'} → SameHeads (prod τ₁ τ₂) (prod τ₁' τ₂')
  sum : ∀ {τ₁ τ₂ τ₁' τ₂'} → SameHeads (sum τ₁ τ₂) (sum τ₁' τ₂')

¬-all-≡ₜ-arrow : ∀ {m κ τ₁} {τ₂ τ₃ : Type m} → ¬ (all κ τ₁ ≡ₜ arrow τ₂ τ₃)
¬-all-≡ₜ-arrow eq with confluence-≡ₜ eq
... | _ , all-steps , arrow-steps with all-preserved all-steps | arrow-preserved arrow-steps
...   | _ , refl , _ | _ , () , _

¬-exists-≡ₜ-arrow : ∀ {m κ τ₁} {τ₂ τ₃ : Type m} → ¬ (exists κ τ₁ ≡ₜ arrow τ₂ τ₃)
¬-exists-≡ₜ-arrow eq with confluence-≡ₜ eq
... | _ , exists-steps , arrow-steps with exists-preserved exists-steps | arrow-preserved arrow-steps
...   | _ , refl , _ | _ , () , _

¬-prod-≡ₜ-arrow : ∀ {m} {τ₁ τ₂ τ₃ τ₄ : Type m} → ¬ (prod τ₁ τ₂ ≡ₜ arrow τ₃ τ₄)
¬-prod-≡ₜ-arrow eq with confluence-≡ₜ eq
... | _ , prod-steps , arrow-steps with prod-preserved prod-steps | arrow-preserved arrow-steps
...   | _ , refl , _ | _ , () , _

¬-sum-≡ₜ-arrow : ∀ {m} {τ₁ τ₂ τ₃ τ₄ : Type m} → ¬ (sum τ₁ τ₂ ≡ₜ arrow τ₃ τ₄)
¬-sum-≡ₜ-arrow eq with confluence-≡ₜ eq
... | _ , sum-steps , arrow-steps with sum-preserved sum-steps | arrow-preserved arrow-steps
...   | _ , refl , _ | _ , () , _

¬-exists-≡ₜ-all : ∀ {m κ₁ κ₂} {τ₁ τ₂ : Type (succ m)} → ¬ (exists κ₁ τ₁ ≡ₜ all κ₂ τ₂)
¬-exists-≡ₜ-all eq with confluence-≡ₜ eq
... | _ , exists-steps , all-steps with exists-preserved exists-steps | all-preserved all-steps
...   | _ , refl , _ | _ , () , _

¬-prod-≡ₜ-all : ∀ {m κ} {τ₁ τ₂ : Type m} {τ₃} → ¬ (prod τ₁ τ₂ ≡ₜ all κ τ₃)
¬-prod-≡ₜ-all eq with confluence-≡ₜ eq
... | _ , prod-steps , all-steps with prod-preserved prod-steps | all-preserved all-steps
...   | _ , refl , _ | _ , () , _

¬-sum-≡ₜ-all : ∀ {m κ} {τ₁ τ₂ : Type m} {τ₃} → ¬ (sum τ₁ τ₂ ≡ₜ all κ τ₃)
¬-sum-≡ₜ-all eq with confluence-≡ₜ eq
... | _ , sum-steps , all-steps with sum-preserved sum-steps | all-preserved all-steps
...   | _ , refl , _ | _ , () , _

¬-prod-≡ₜ-exists : ∀ {m κ} {τ₁ τ₂ : Type m} {τ₃} → ¬ (prod τ₁ τ₂ ≡ₜ exists κ τ₃)
¬-prod-≡ₜ-exists eq with confluence-≡ₜ eq
... | _ , prod-steps , exists-steps with prod-preserved prod-steps | exists-preserved exists-steps
...   | _ , refl , _ | _ , () , _

¬-sum-≡ₜ-exists : ∀ {m κ} {τ₁ τ₂ : Type m} {τ₃} → ¬ (sum τ₁ τ₂ ≡ₜ exists κ τ₃)
¬-sum-≡ₜ-exists eq with confluence-≡ₜ eq
... | _ , sum-steps , exists-steps with sum-preserved sum-steps | exists-preserved exists-steps
...   | _ , refl , _ | _ , () , _

¬-prod-≡ₜ-sum : ∀ {m} {τ₁ τ₂ τ₃ τ₄ : Type m} → ¬ (prod τ₁ τ₂ ≡ₜ sum τ₃ τ₄)
¬-prod-≡ₜ-sum eq with confluence-≡ₜ eq
... | _ , prod-steps , sum-steps with prod-preserved prod-steps | sum-preserved sum-steps
...   | _ , refl , _ | _ , () , _