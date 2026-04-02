module dan where

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

subst : {A : Set} -> {x y : A} -> (P : A -> Set) -> x ≡ y -> P x -> P y
subst P refl px = px 

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

zero_is_zero : zero ≡ zero
zero_is_zero = refl

successors_are_equal : {a b : Nat} → a ≡ b → suc a ≡ suc b
successors_are_equal refl = refl

_+_ : Nat → Nat → Nat
zero + b = b
suc a + b = suc (a + b)

adding_one_on_left_is_suc : {b : Nat} → (suc zero + b) ≡ suc b
adding_one_on_left_is_suc = refl

lemma1 : { a : Nat } → (a + zero) ≡ a → suc (a + zero) ≡ suc a
lemma1 sublemma = cong suc sublemma

lemma2 : { a : Nat } → (suc a + zero) ≡ suc (a + zero)
lemma2 = refl

lemma3 : { a : Nat } → a ≡ (a + zero) → suc a ≡ (suc a + zero)
lemma3 {a} sublemma = trans (sym (cong suc (sym sublemma))) (sym refl)

proof : {a : Nat} → a ≡ (a + zero)
proof {zero} = refl
proof {suc y} = lemma3 (proof {y})

