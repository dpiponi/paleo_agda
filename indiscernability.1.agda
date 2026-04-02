{-# OPTIONS --without-K --type-in-type #-}

module indiscernability where

module Paths where
 infix 3 _≡_

 data _≡_ {A : Set} : A → A → Set where
   refl : {a : A} → a ≡ a

 Paths : {A : Set} → A → A → Set
 Paths = _≡_

 id : {A : Set} → A → A
 id x = x

 f : {A : Set} (C : A → Set)
     → {M N : A} → (P : M ≡ N)
     → C M
     → C N
 f _ refl = id

 data ℕ : Set where
   zero : ℕ
   succ : ℕ → ℕ

 _+_ : ℕ → ℕ → ℕ
 zero + b = b
 succ a + b = succ (a + b)

 p : {a b : ℕ} → a ≡ b → succ a ≡ succ b
 p refl = refl

 p' : {a b : ℕ} → succ a ≡ succ b → a ≡ b
 p' refl = refl

 p'' : (C : ℕ → Set) → {N : ℕ} → C N → C (zero + N)
 p'' C = id
-- p'' C = f C refl

-- g : (C : ℕ → Set) → {M N : ℕ}
--     → C M → C N
-- g x = {!!}

-- To prove a property for all elements x, y and paths p: x ≡ y
-- we need only consider the case x, x with path refl.
 j : {A : Set} (C : (x y : A) → x ≡ y → Set)
     → {M N : A} → (P : M ≡ N)
     → ((x : A) → C x x refl)
     → C M N P
 j _ refl b = b _

 based : {A : Set} {a : A} (C : (x : A) → a ≡ x → Set)
          → C a refl
          → (x : A) → (P : a ≡ x)
          → C x P
 based _ b _ refl = b

 j₀ : {A : Set} (C : (x y : A) → x ≡ y → Set)
      → {M N : A} → (P : M ≡ N)
      → ((x : A) → C x x refl)
      → C M N P
 j₀ C refl c = based (C _) (c _) _ refl

 based₀ : {A : Set} {a : A} → (C : (x : A) → a ≡ x → Set)
        → C a refl
        → (x : A) → (P : a ≡ x)
        → C x P
 based₀ C c x p =
        let D : {A : Set} → (x : A) → (y : A) → x ≡ y → Set
            D x y p = (C : (z : _) → (p : x ≡ z) → Set) → C x refl → C y p
            d : {A : Set} (x : A) → D x x refl
            d = λ x → λ C → λ (c : C x refl) → c
            f = j D _ d
        in f C c