module products where

open import Data.Product hiding (∃)
open import Data.Bool
open import Data.Nat

f : Bool → Set
f true = ℕ
f false = Bool

--S = Σ[ x ∶ Bool ] (f x)
S = Σ Bool f

x : S
x = (true , 1)

y : S
y = (false , false)

∃ : ∀ {A : Set} → (A → Set) → Set
∃ {A} f = Σ A f