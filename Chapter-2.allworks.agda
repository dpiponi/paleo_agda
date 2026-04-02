{-# OPTIONS --without-K --type-in-type #-}

module Chapter-2 where

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
 p ■₀ q = j (λ x y p → (y ≡ _) → (x ≡ _))
            (λ x → id)
            p q

 _■₁_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
 p ■₁ q = j (λ y z p → (_ ≡ y) → (_ ≡ z))
            (λ y → id)
            q p


 _■_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
 p ■ q = j (λ x y _ → (y ≡ _) → (x ≡ _))
           d
           p q
           where 
                 d : (x : _) → (x ≡ _) → (x ≡ _)
                 d = λ x q → j (λ x z _ → x ≡ z)
                               (λ x → refl)
                               q
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
 ppp : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■₁ refl)
 ppp = refl

 ppp' : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■₀ p)
 ppp' = refl

-- ppp'' : {A : Set} → {x y : A} → {p : x ≡ y} → (refl ■ p) ≡ p
-- ppp'' = refl

 refl' : {A : Set} → (p : A) → p ≡ p
 refl' p = refl

 ppp''' : {A : Set} → {x : A} → refl ≡ (refl' x ■ refl)
 ppp''' = refl

-- ppp'''' : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■ refl)
-- ppp'''' = refl

-- ppp'' : refl ≡ (refl ■₀ refl)
-- ppp'' = refl

 lemma-2-1-4-i-a : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■ refl)
 lemma-2-1-4-i-a = j (λ x y p → p ≡ (p ■ refl))
                     (λ x → refl)
                     _

 lemma-2-1-4-i-b : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■ p)
 lemma-2-1-4-i-b = j (λ x y p → p ≡ (refl ■ p))
                     (λ x → refl)
                     _

 lemma-2-1-4-iii : {A : Set} → {x y : A} → {p : x ≡ y} → (p ⁻¹)⁻¹ ≡ p
 lemma-2-1-4-iii = j (λ x y p → (p ⁻¹)⁻¹ ≡ p)
                     (λ x → refl)
                     _

 d₄ : {A : Set} → (x : A) → refl' x ■ (refl' x ■ refl' x) ≡ (refl' x ■ refl' x) ■ refl' x
 d₄ x = refl

 d₃ : {A : Set} → (x w : A) → (r : x ≡ w) → refl' x ■ (refl' x ■ r) ≡ (refl' x ■ refl' x) ■ r
 d₃ x w r = j (λ x w (r : x ≡ w) → refl' x ■ (refl' x ■ r) ≡ (refl' x ■ refl' x) ■ r)
              (λ x → d₄ x)
              r
              

 d₂ : {A : Set} → {x z : A} → (q : x ≡ z) → (w : A) → (r : z ≡ w) → (refl' x ■ (q ■ r)) ≡ ((refl' x ■ q) ■ r)
 d₂ q = j (λ x z (q : x ≡ z) → (w : _) → (r : z ≡ w) → (refl' x ■ (q ■ r)) ≡ ((refl' x ■ q) ■ r))
              (λ x → d₃ x)
              q

 d₁ : {A : Set} → {x y : A} → (p : x ≡ y) → (z : A) → (q : y ≡ z) → (w : A) → (r : z ≡ w) → (p ■ (q ■ r)) ≡ ((p ■ q) ■ r)
 d₁ p = j (λ x y (p : x ≡ y) → (z : _) → (q : y ≡ z) → (w : _) → (r : z ≡ w) → (p ■ (q ■ r)) ≡ ((p ■ q) ■ r))
              (λ x → d₂ x)
              p
{-
 lemma-2-1-4-iv : {A : Set} → {x y z w : A} → {p : x ≡ y} → {q : y ≡ z} → {r : z ≡ w} → p ■ (q ■ r) ≡ (p ■ q) ■ r
 lemma-2-1-4-iv = j (λ y z q → _ ■ (q ■ _) ≡ (_ ■ q) ■ _)
                    (λ y → lemma)
                    _
-}