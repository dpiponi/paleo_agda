module dan where

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

zero_is_zero : zero ≡ zero
zero_is_zero = refl

successors_are_equal : a ≡ b → suc a ≡ suc b