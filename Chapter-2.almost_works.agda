{-# OPTIONS --without-K --type-in-type #-}

module Chapter-2a where

open import Data.Nat

module Paths where
 infix 3 _≡_

 data _≡_ {A : Set} : A → A → Set where
   refl : {a : A} → a ≡ a

 Paths : {A : Set} → A → A → Set
 Paths = _≡_

 id : {A : Set} → A → A
 id x = x

 {- Flipped from chapter 1.
    My mistake I think.
 -}
 j : {A : Set} (C : (x y : A) → x ≡ y → Set)
     → ((x : A) → C x x refl)
     → {M N : A} → (P : M ≡ N)
     → C M N P
 j _ b refl = b _


 _⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
 p ⁻¹ = j D d p 
                 where D : (x y : _) → x ≡ y → Set
                       D x y p = y ≡ x
                       d : (x : _) → D x x refl
                       d x = refl

 {-
 x ≡ y → y ≡ z → x ≡ z
 Try deforming y to x:
 x ≡ y → y ≡ y → x ≡ z
 -}
 _■₀_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
 p ■₀ q = j D d p q
           where D : (x y : _) → x ≡ y → Set
                 D x y p = (y ≡ _) → (x ≡ _)
                 d : (x : _) → D x x refl
                 d _ = id

 _■₁_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
 p ■₁ q = j D d q p
           where D : (y z : _) → y ≡ z → Set
                 D y z p = (_ ≡ y) → (_ ≡ z)
                 d : (y : _) → D y y refl
                 d _ = id


 _■_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
 p ■ q = j D d p q
           where D : (x y : _) → (x ≡ y) → Set
                 D x y p = (y ≡ _) → (x ≡ _) -- convert x≡z → x≡z to y≡z → x≡z
                 d : (x : _) → D x x refl -- = (x : A) → (x ≡ z) → (x ≡ z)
                 E : (x z : _) → (x ≡ z) → Set
                 E x z q = x ≡ z
                 e : (x : _) → E x x refl -- = (x : A) → x ≡ x
                 e x = refl
                 d x p = j E e p -- : x ≡ z
{-
 _■_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
 p ■ q = {!r!}
         where D : (x y : _) → (p : x ≡ y) → Set
               D x y p = (x ≡ x) → (x ≡ y)
               d : (x : _) → (x ≡ x) → (x ≡ x)
               d _ = id
               h : _ ≡ _
               h = j D d p refl -- refl : x ≡ y
               E : (x y : _) → (p : x ≡ y) → Set
               E x y p = (y ≡ _) → (x ≡ _)
               e : (x : _) → (x ≡ _) → (x ≡ _)
               e _ = id
               r = j E e p h
-}

{-
 proof : {A : Set} {x y z : A} → (p : x ≡ x) → (q : x ≡ x) → (p ■₀ q) ≡ (p ■₁ q)
 proof p q =  {!refl!}
-}

{-
 j : {A : Set} (C : (x y : A) → x ≡ y → Set)
     → ((x : A) → C x x refl)
     → {M N : A} → (P : M ≡ N)
     → C M N P

           where D : (x y : _) → (p : x ≡ y) → Set
                 D x y p = (z : _) → (q : y ≡ z) → x ≡ z
                 E : (x z : _) → (q : x ≡ z) → Set
                 E x z q = x ≡ z
                 e : (x : _) → E x x refl
                 e x = refl
--                 d : (y : _) → D y y refl
                 d = j E e refl
-}