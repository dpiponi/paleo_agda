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
                     (λ _ → refl)
                     _

 lemma-2-1-4-i-b : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■ p)
 lemma-2-1-4-i-b = j (λ x y p → p ≡ (refl ■ p))
                     (λ _ → refl)
                     _

 lemma-2-1-4-iia : {A : Set} → {x y : A} → (p : x ≡ y) → (p ⁻¹ ■ p) ≡ refl
 lemma-2-1-4-iia p = j (λ x y p → (p ⁻¹ ■ p) ≡ refl)
                     (λ _ → refl)
                     p

 lemma-2-1-4-iib : {A : Set} → {x y : A} → (p : x ≡ y) → (p ■ p ⁻¹) ≡ refl
 lemma-2-1-4-iib p = j (λ x y p → (p ■ p ⁻¹) ≡ refl)
                     (λ _ → refl)
                     p

 lemma-2-1-4-iii : {A : Set} → {x y : A} → (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
 lemma-2-1-4-iii p = j (λ x y p → (p ⁻¹)⁻¹ ≡ p)
                     (λ _ → refl)
                     p

 d₄ : {A : Set} → (x : A) → refl ■ (refl ■ refl) ≡ (refl ■ refl) ■ refl' x
 d₄ _ = refl

 d₃ : {A : Set} → (x : A) → {w : A} → (r : x ≡ w) → refl ■ (refl ■ r) ≡ (refl ■ refl) ■ r
 d₃ _ r = j (λ x w (r : x ≡ w) → refl ■ (refl ■ r) ≡ (refl ■ refl) ■ r)
          d₄
          r
              

 d₂ : {A : Set} → (x : A) → {z : A} → (q : x ≡ z) → {w : A} → (r : z ≡ w) → (refl ■ (q ■ r)) ≡ ((refl ■ q) ■ r)
 d₂ _ q = j (λ x z (q : x ≡ z) → {w : _} → (r : z ≡ w) → (refl ■ (q ■ r)) ≡ ((refl ■ q) ■ r))
          d₃
          q

 lemma-2-1-4-iv : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → {w : A} → (r : z ≡ w)
                → (p ■ (q ■ r)) ≡ ((p ■ q) ■ r)
 lemma-2-1-4-iv p = j (λ x y (p : x ≡ y) → {z : _} → (q : y ≡ z) → {w : _} → (r : z ≡ w)
                                         → (p ■ (q ■ r)) ≡ ((p ■ q) ■ r))
          d₂
          p

 Ω² : (A : Set) → (a : A) → Set
 Ω² A a = refl' a ≡ refl' a

 head : {A : Set} → {x y : A} → (p : x ≡ y) → A
 head {A} {x} {y} p = x

 tail : {A : Set} → {x y : A} → (p : x ≡ y) → A
 tail {A} {x} {y} p = y

 right : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p ■ r) ≡ (q ■ r)
 right α r = j (λ p q α → (p ■ r) ≡ (q ■ r))
                  (λ α → refl)
                  α

 mylemma : {A : Set} → {a b : A} → {p q : a ≡ b}  → (α : p ≡ q) → (p ■ refl) ≡ (q ■ refl)
 mylemma α = ((lemma-2-1-4-i-a ⁻¹) ■ α) ■ lemma-2-1-4-i-a

 right' : {A : Set} → {b c : A} → (r : b ≡ c) → {a : A} → (p q : a ≡ b) → (α : p ≡ q) → (p ■ r) ≡ (q ■ r)
 right' r = j (λ b c r → {a : _} → (p q : a ≡ b) → (α : p ≡ q) → (p ■ r) ≡ (q ■ r))
                            (λ b → λ p q α → mylemma α)
                          r

 left : {A : Set} → {a b c : A} → {r s : b ≡ c} → (q : a ≡ b) → (β : r ≡ s) → (q ■ r) ≡ (q ■ s)
 left q β = j (λ r s β → (q ■ r) ≡ (q ■ s))
             (λ β → refl)
             β

 _·_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s)
                 → ((p ■ r) ≡ (q ■ s))
 α · β = right α r ■ left q β
         where
               q = tail α
               r = head β

 _⋆_ : {A : Set} → {a : A} → (p q : Ω² A a) → Ω² A a
 p ⋆ q = p · q -- differentiating two operators I think are conflated in book

 _·'_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s)
                  → ((p ■ r) ≡ (q ■ s))
 α ·' β = left p β ■ right α s
         where
               p = head α
               s = tail β

 _⋆'_ : {A : Set} → {a : A} → (p q : Ω² A a) → Ω² A a
 p ⋆' q = p ·' q

-- lemma1 : {A : Set} → {a : A} → {p q r : a ≡ a} → {α : p ≡ refl}
--                    → α ≡ right α refl
-- lemma1 = ?

 lemma1 : {A : Set} → {a : A} → {p s : a ≡ a} → (α : p ≡ refl' a) → (β : refl' a ≡ s)
                    → α · β ≡ (right α refl) ■ (left refl β)
 lemma1 α β = refl

{-
 lemma2 : {A : Set} → {a : A} → {p : a ≡ a} → (α : p ≡ refl' a)
                    → (right α refl) ≡ α
 lemma2 α = j (λ _ _ α → (α : _ ≡ refl) → (right α refl) ≡ α)
              (λ _ → ?)
              α
-}

{-
 plop1 : {A : Set} → {a b : A} → {p q : a ≡ b} → (p ≡ (q ■ refl)) → (p ≡ q)
 plop1 x = x ■ (lemma-2-1-4-i-a ⁻¹)

 plop2 : {A : Set} → {a b : A} → {p q : a ≡ b} → ((p ■ refl) ≡ (q ■ refl)) → (p ≡ q)
 plop2 x = plop1 x ■ (lemma-2-1-4-i-b)
-}

{-
 right : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p ■ r) ≡ (q ■ r)
 right α r = j (λ p q α → (p ■ r) ≡ (q ■ r))
                  (λ α → refl)
                  α
-}
{-
 right' : {A : Set} → {a b : A} → {p q : a ≡ b} → (α : p ≡ q) → (p ■ refl) ≡ (q ■ refl)
 right' α = j (λ p q α → (p ■ refl) ≡ (q ■ refl))
              (λ p → refl)
              α

 right'' : {A : Set} → {a : A} → (α : refl' a ≡ refl) → (refl ■ refl) ≡ (refl ■ refl)
 right'' α = j (λ p q α → (p ■ refl) ≡ (q ■ refl))
                   (λ α → refl)
                   α
-}
 lemma6 : {A : Set} → {a : A} → (α : refl ≡ refl) → (right α (refl' a) ≡ α)
 lemma6 = {!!}

{-
 lemma6' : {A : Set} → {a : A} → (α : refl' a ≡ refl' a) → (right'' α ≡ α)
 lemma6' α = {!!}
-}

{-
 lemma-2-1-4-i-a : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■ refl)
 lemma-2-1-4-i-b : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■ p)
-}
{- HERE!
 lemma5 : {A : Set} → {a : A} → (α : refl' a ≡ refl)
                    → right α refl ≡ α
 lemma5 α = j (λ _ _ α → right α refl ≡ α)
              (λ _ → right refl refl ≡ refl)
              _
-}
{-
 lemma4 : {A : Set} → {a : A} → (α : refl' a ≡ refl' a) → (β : refl' a ≡ refl' a)
                      -- p ■ refl ≡ refl ■ s           p ≡ s
                    → right α refl ■ left refl β
                      ≡ α ■ β
 lemma4 α β = {!!}
-}

{-
 lemma3 : {A : Set} → {a : A} → {p s : a ≡ a} → (α : p ≡ refl' a) → (β : refl' a ≡ s)
                      -- p ■ refl ≡ refl ■ s           p ≡ s
                    → (lemma-2-1-4-i-a ■ (((right α refl) ■ (left refl β)) ))
                      ≡ (α ■ β) ■ (lemma-2-1-4-i-b)
 lemma3 α β = {!!}
-}

-- lemma2 : {A : Set} → {a : A} → (α β : Ω² A a) → α ⋆ β ≡ α ■ β
-- lemma2 α β = refl

-- eckmann-hilton : {A : Set} → {a : A} → (p q : Ω² A a) → p ■ q ≡ q ■ p
-- eckmann-hilton = {!!}