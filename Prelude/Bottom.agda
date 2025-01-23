module Prelude.Bottom where

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

infix 9 ¬_

absurd : ∀ {A : Set} → ⊥ → A
absurd ()