module lesson1 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

f : Nat → Nat
f zero = zero
f (suc y) = suc (suc y)

eq : Nat → Nat → Set
eq zero zero = Nat
eq zero (suc b) = Nat
eq (suc zero) b = Nat
eq (suc (suc a)) b = Nat

