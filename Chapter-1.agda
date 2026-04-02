{-# OPTIONS --without-K --type-in-type #-}

module Chapter-1 where

open import Data.Nat

module Paths where
 infix 3 _≡_

 data _≡_ {A : Set} : A → A → Set where
   refl : {a : A} → a ≡ a

 Paths : {A : Set} → A → A → Set
 Paths = _≡_

 id : {A : Set} → A → A
 id x = x

 {-
 data ℕ : Set where
   zero : ℕ
   suc : ℕ → ℕ

 _+_ : ℕ → ℕ → ℕ
 zero + b = b
 suc a + b = suc (a + b)
 -}

 p : {a b : ℕ} → a ≡ b → suc a ≡ suc b
 p refl = refl

 p' : {a b : ℕ} → suc a ≡ suc b → a ≡ b
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

 {-
 j₀ family path_x_to_y points_over_diag = point_over_x_y
 -}
 j₀ : {A : Set} (C : (x y : A) → x ≡ y → Set)
      → {M N : A} → (P : M ≡ N)
      → ((x : A) → C x x refl)
      → C M N P
 j₀ C refl c = based (C _) (c _) _ refl

 {-
 based₀ family point_over_a x path_x_to_a = point_over_x
 -}
 based₀ : {A : Set} {a : A} → (C : (x : A) → a ≡ x → Set)
        → C a refl
        → (x : A) → (P : a ≡ x)
        → C x P
 based₀ C c x p =
        let D : {A : Set} (x y : A) → x ≡ y → Set
            D x y p = (C : (z : _) → (p : x ≡ z) → Set) → C x refl → C y p
            d : {A : Set} (x : A) → D x x refl
            d = λ x → λ C → λ (c : C x refl) → c
        in j D p d C c

 {- 1.1
    Q asks for judgmental equality but for fun this is propositional equality
 -}

 module ex1-1 where
   _○_ : {A B C : Set} → (B → C) → (A → B) → A → C
   g ○ f = λ x → g (f x)

   assoc : {A B C D : Set} (f : A → B) → (g : B → C) → (h : C → D) → h ○ (g ○ f) ≡ (h ○ g) ○ f
   assoc f g h = refl

 {- 1.2 -}

 module ex1-2a where
   data _×_ (A B : Set) : Set where
     _,_ : A → B → A × B

   pr₁ : {A B : Set} → (A × B) → A
   pr₁ (a , _) = a
   pr₂ : {A B : Set} → (A × B) → B
   pr₂ (_ , b) = b

   rec×₀ : {A B C : Set} → (A → B → C) → A × B → C
   rec×₀ f (a , b) = f a b

   rec×₁ : {A B C : Set} → (A → B → C) → A × B → C
   rec×₁ f x = f (pr₁ x) (pr₂ x)

 module ex1-2b where
   data ∑ (A : Set) (B : A → Set) : Set where
     _,_ : (a : A) → B a → ∑ A B

   pr₁ : {A : Set} {B : A → Set} → ∑ A B → A
   pr₁ (a , _) = a
   pr₂ : {A : Set} {B : A → Set} → (p : ∑ A B) → B (pr₁ p)
   pr₂ (_ , b) = b

   rec∑₀ : {A : Set} {B : A → Set} → {C : Set} → ((x : A) → B x → C) → (∑ A B) → C
   rec∑₀ f (a , b) = f a b

   rec∑₁ : {A : Set} {B : A → Set} → {C : Set} → ((x : A) → B x → C) → (∑ A B) → C
   rec∑₁ f x = f (pr₁ x) (pr₂ x)

 module ex1-4 where
   --data ℕ : Set where
     --zero : ℕ
     --suc : ℕ → ℕ
   data _×_ (A B : Set) : Set where
     _,_ : A → B → A × B

   pr₁ : {A B : Set} → (A × B) → A
   pr₁ (a , _) = a
   pr₂ : {A B : Set} → (A × B) → B
   pr₂ (_ , b) = b

   iter : {C : Set} → C → (C → C) → ℕ → C
   iter c0 cs zero = c0
   iter c0 cs (suc n) = cs (iter c0 cs n)

   recℕ₀ : {C : Set} → C → (ℕ → C → C) → ℕ → C
   recℕ₀ c0 cs zero = c0
   recℕ₀ c0 cs (suc n) = cs n (recℕ₀ c0 cs n)

   recℕ₁ : (C : Set) → C → (ℕ → C → C) → ℕ → C
   recℕ₁ C c0 cs n = pr₂ (iter (zero , c0) g n)
         where g : ℕ × C → ℕ × C
               g (m , x) = (suc m , cs m x)

 module ex1-10 where
   open ex1-4
   ack : ℕ → ℕ → ℕ
   ack 0 n = suc n
   ack (suc m) 0 = ack m 1
   ack (suc m) (suc n) = ack m (ack (suc m) n)

   a₀ : ℕ → ℕ
   a₀ = suc

   a₁ : ℕ → ℕ
   a₁ = recℕ₀ (a₀ 1) (λ n x → a₀ x)

   a₂ : ℕ → ℕ
   a₂ = recℕ₀ (a₁ 1) (λ n x → a₁ x)

   a : ℕ → ℕ → ℕ
   a = recℕ₀ a₀ (λ n f → recℕ₀ (f 1) (λ n x → f x))

 module ex1-11 where
   data False : Set where

   ¬ : Set → Set
   ¬ p = p → False

   proof : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
   proof p q = p (λ r → r q)

 module ex1-12 where
   open ex1-11
   open ex1-2a
   open ex1-1
   proof_i : {A B : Set} → A → (B → A)
   proof_i a _ = a

   proof_ii : {A : Set} → A → ¬ (¬ A)
   proof_ii a b = b a

   data _+'_ (A B : Set) : Set where
     inl : A → A +' B
     inr : B → A +' B

   proof_iii : {A B : Set} → ((¬ A) +' (¬ B)) → ¬ (A × B)
   proof_iii (inl f)  = f ○ pr₁
   proof_iii (inr g)  = g ○ pr₂

 module ex1-13 where
   open ex1-11
   open ex1-2a
   open ex1-1
   open ex1-12

   proof13 : {P : Set} → ¬ (¬ (P +' (¬ P)))
   proof13 p = p (inr (λ q → p (inl q)))

 module ex1-15 where
   indiscernability₀ : {A : Set} (C : A → Set)
                     → {M N : A} → (P : M ≡ N)
                     → C M
                     → C N
   indiscernability₀ _ refl = id


   {-
   j : {A : Set} (C : (x y : A) → x ≡ y → Set)
       → {M N : A} → (P : M ≡ N)
       → ((x : A) → C x x refl)
       → C M N P
   -}
   indiscernability₁ : {A : Set} (C : A → Set)
                     → {M N : A} → (P : M ≡ N)
                     → C M
                     → C N
   indiscernability₁ C path stalk = j D path diag stalk where
     D : (x y : _) → x ≡ y → Set
     D x y p = C x → C y
     diag : ((x : _) → D x x refl)
     diag x z = z

 module ex1-9 where
--   data Fin0 : Set where

--   Fin : ℕ → Set
--   Fin 0 = Fin0
--   Fin (suc n) = Fin0

   data Fin : ℕ → Set where
     fzero : {n : ℕ} → Fin (suc n)
     fsuc : {n : ℕ} → Fin n → Fin (suc n)

 open import IO
 open import Data.Nat.Show
 open import Data.String

 open ex1-4
 open ex1-10

 n : ℕ
 n = iter 0 (λ x → x + 2) 30

 --main = run (putStrLn (show (ack 3 4)))
 --main = run (putStrLn (show (a₂ 4)))
 main = run (putStrLn (show (a 3 4)))
