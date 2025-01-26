module Prelude.Vector where

open import Prelude.Fin
open import Prelude.Nat
open import Prelude.PropositionalEquality
open import Prelude.Sigma

data Vector (A : Set) : ℕ → Set where
  [] : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

infixr 5 _∷_

map : {A B : Set} → (A -> B) → {n : ℕ} → Vector A n → Vector B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

lookup : ∀ {A n} → Vector A n → Fin n → A
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (succ i) = lookup xs i

data All {A : Set} (P : A → Set) : {n : ℕ} → Vector A n → Set where
  [] : All P []
  _∷_ : ∀ {n x} {xs : Vector A n} → P x → All P xs → All P (x ∷ xs)

lookup-map : ∀ {n A B} (f : A → B) (xs : Vector A n) i → lookup (map f xs) i ≡ f (lookup xs i)
lookup-map f (x ∷ xs) zero = refl
lookup-map f (x ∷ xs) (succ i) = lookup-map f xs i

map-map : ∀ {n A B C} (f : B → C) (g : A → B) (xs : Vector A n) → map f (map g xs) ≡ map (λ x → f (g x)) xs
map-map f g [] = refl
map-map f g (x ∷ xs) rewrite map-map f g xs = refl

map-ext : ∀ {A B : Set} {n} (f g : A → B) (xs : Vector A n) → (∀ x → f x ≡ g x) → map f xs ≡ map g xs
map-ext f g [] p = refl
map-ext f g (x ∷ xs) p rewrite p x | map-ext f g xs p = refl

map-id : ∀ {A n} (xs : Vector A n) → map (λ x → x) xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong₂ _∷_ refl (map-id xs)

lookup-ext : ∀ {A n} (xs ys : Vector A n) → (∀ x → lookup xs x ≡ lookup ys x) → xs ≡ ys
lookup-ext [] [] p = refl
lookup-ext (x ∷ xs) (y ∷ ys) p = cong₂ _∷_ (p zero) (lookup-ext xs ys (λ x → p (succ x)))

data ZipWith {A B : Set} (f : A → B → Set) : {n : ℕ} → Vector A n → Vector B n → Set where
  [] : ZipWith f [] []
  _∷_ : ∀ {n a b} {as : Vector A n} {bs : Vector B n} → f a b → ZipWith f as bs → ZipWith f (a ∷ as) (b ∷ bs)

_++_ : ∀ {A m n} → Vector A m → Vector A n → Vector A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 4 _++_

take : ∀ {A m} (n : Fin m) → Vector A m → Vector A (toℕ n)
take zero (x ∷ xs) = []
take (succ n) (x ∷ xs) = x ∷ take n xs

update : ∀ {A m} (n : Fin m) → A → Vector A m → Vector A m
update zero y (x ∷ xs) = y ∷ xs
update (succ n) y (x ∷ xs) = x ∷ update n y xs

lookup-zip-with : ∀ {A B n} {f : A → B → Set} {xs : Vector A n} {ys : Vector B n} → ZipWith f xs ys → ∀ i → f (lookup xs i) (lookup ys i)
lookup-zip-with (x ∷ _) zero = x
lookup-zip-with (_ ∷ xs) (succ i) = lookup-zip-with xs i