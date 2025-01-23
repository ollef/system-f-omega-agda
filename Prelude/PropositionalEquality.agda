module Prelude.PropositionalEquality where

open import Agda.Builtin.Equality public

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : {A B C : Set} {x y : A} {x' y' : B} (f : A → B → C) → x ≡ y → x' ≡ y' → f x x' ≡ f y y'
cong₂ f refl refl = refl

subst : ∀ {l₁ l₂} {A : Set l₁} (P : A → Set l₂) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

subst₂ : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} (P : A → B → Set) {x y : A} {x' y' : B} → x ≡ y → x' ≡ y' → P x x' → P y y'
subst₂ P refl refl p = p

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ p = p

_≡⟨⟩_ : ∀ {A : Set} {y} (x : A) → x ≡ y → x ≡ y
x ≡⟨⟩ p = p

infixr 2 _≡⟨_⟩_
infixr 2 _≡⟨⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix 3 _∎