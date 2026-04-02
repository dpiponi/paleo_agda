{-# OPTIONS --without-K --type-in-type #-}

module Chapter-2 where

open import Data.Nat

module Paths where
 infix 3 _≡_

 data _≡_ {A : Set} : A → A → Set where
   refl : {a : A} → a ≡ a

 refl' : {A : Set} → (p : A) → p ≡ p
 refl' {A} p = refl {A} {p}

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

 j₂ : {A : Set} (C : (x y z : A) → x ≡ y → y ≡ z → Set)
      → ((x : A) → C x x x refl refl)
      → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
      → C x y z p q
 j₂ {A} C s p q = (j (λ x y p → {z : A} → (q : y ≡ z) → C x y z p q)
                     (λ y → j (λ y z q → C y y z refl q) s)
                      p) q


 ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
 ap f p = j (λ x y p → f x ≡ f y)
            (λ x → refl)
            p

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


 _▻ : {A : Set} → (p : A) → p ≡ p
 p ▻ = refl

 _≡⟨_⟩_ : {A : Set} → {q r : A} → (p : A) → p ≡ q → q ≡ r → p ≡ r
 p ≡⟨ α ⟩ β = α ■ β


 infixr 2 _≡⟨_⟩_
 infix 3 _▻
 infixr 2 _→⟨_⟩_
 infix 3 _□

 lemma-2-1-4-i-a : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■ refl)
 lemma-2-1-4-i-a = j (λ _ _ p → p ≡ p ■ refl)
                     (λ _ → refl)
                     _
 p≡p■refl = lemma-2-1-4-i-a

 lemma-2-1-4-i-b : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■ p)
 lemma-2-1-4-i-b = j (λ _ _ p → p ≡ refl ■ p)
                     (λ _ → refl)
                     _
 p≡refl■p = lemma-2-1-4-i-b

 lemma-2-1-4-iia : {A : Set} → {x y : A} → (p : x ≡ y) → p ⁻¹ ■ p ≡ refl
 lemma-2-1-4-iia p = j (λ _ _ p → p ⁻¹ ■ p ≡ refl)
                     (λ _ → refl)
                     p
 p⁻¹■p≡refl = lemma-2-1-4-iia

 lemma-2-1-4-iib : {A : Set} → {x y : A} → (p : x ≡ y) → p ■ p ⁻¹ ≡ refl
 lemma-2-1-4-iib p = j (λ _ _ p → p ■ p ⁻¹ ≡ refl)
                     (λ _ → refl)
                     p
 p■p⁻¹≡refl = lemma-2-1-4-iib

 lemma-2-1-4-iii : {A : Set} → {x y : A} → (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
 lemma-2-1-4-iii p = j (λ _ _ p → (p ⁻¹)⁻¹ ≡ p)
                     (λ _ → refl)
                     p

 d₃ : {A : Set} → (x : A) → {w : A} → (r : x ≡ w) → refl ■ (refl ■ r) ≡ (refl ■ refl) ■ r
 d₃ _ r = j (λ x w (r : x ≡ w) → refl ■ (refl ■ r) ≡ (refl ■ refl) ■ r)
          (λ _ → refl)
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

 ■-assoc = lemma-2-1-4-iv
 ■-assoc' : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → {w : A} → (r : z ≡ w)
                → ((p ■ q) ■ r) ≡ (p ■ (q ■ r))
 ■-assoc' p q r = (lemma-2-1-4-iv p q r)⁻¹

 -- finished!
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

-- right' : {A : Set} → {b c : A} → (r : b ≡ c) → {a : A} → {p q : a ≡ b} → (α : p ≡ q) → (p ■ r) ≡ (q ■ r)

 left : {A : Set} → {a b c : A} → {r s : b ≡ c} → (q : a ≡ b) → (β : r ≡ s) → (q ■ r) ≡ (q ■ s)
 left q β = j (λ r s β → (q ■ r) ≡ (q ■ s))
             (λ β → refl)
             β


 _■r'_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p ■ r) ≡ (q ■ r)
 _■r'_ {A} {a} {b} {c} {p} {q} α r =
            j (λ b c r → {p q : a ≡ b} → (α : p ≡ q) → (p ■ r) ≡ (q ■ r))
              (λ b {p} {q} α → p ■ refl ≡⟨ lemma-2-1-4-i-a ⁻¹ ⟩
                           p        ≡⟨ α ⟩
                           q        ≡⟨ lemma-2-1-4-i-a ⟩
                           q ■ refl
                           ▻
              )
              r α


 _■r_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p ■ r) ≡ (q ■ r)
 α ■r r = j (λ b _ r → {a : _} → {p q : a ≡ b} → (α : p ≡ q) → (p ■ r) ≡ (q ■ r))
              (λ _ α → ((lemma-2-1-4-i-a ⁻¹) ■ (α ■ lemma-2-1-4-i-a)))
              r α

 _■l_ : {A : Set} → {a b c : A} → {r s : b ≡ c} → (q : a ≡ b) → (α : r ≡ s) → (q ■ r) ≡ (q ■ s)
 q ■l α = j (λ _ b q → {c : _} → {r s : b ≡ c} → (α : r ≡ s) → (q ■ r) ≡ (q ■ s))
              (λ _ α → ((lemma-2-1-4-i-b ⁻¹) ■ α) ■ lemma-2-1-4-i-b)
              q α

 _·_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s)
                 → ((p ■ r) ≡ (q ■ s))
 _·_ {_} {_} {_} {_} {_} {q} {r} {_} α β = (α ■r r) ■ (q ■l β)

-- Horizontal composition
 _⋆_ : {A : Set} → {a : A} → (p q : Ω² A a) → Ω² A a
 p ⋆ q = p · q

 _·'_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s)
                  → ((p ■ r) ≡ (q ■ s))
 _·'_ {A} {a} {b} {c} {p} {q} {r} {s} α β = (p ■l β) ■ (α ■r s)

 _⋆'_ : {A : Set} → {a : A} → (p q : Ω² A a) → Ω² A a
 p ⋆' q = p ·' q

 hor-comm0 : {A : Set} → {a b c : A} → (r : b ≡ c) → (p : a ≡ b)
                 → (refl' p · refl' r) ≡ (refl' p ·' refl' r)
 hor-comm0 r p = j₂ (λ a b c p r → (refl' p · refl' r) ≡ (refl' p ·' refl' r))
                    (λ x → refl)
                    p r

 hor-comm1 : {A : Set} → {a b c : A} → {p q : a ≡ b} → {r : b ≡ c} → (α : p ≡ q)
                 → (α · refl' r) ≡ (α ·' refl' r)
 hor-comm1 α = j (λ p q α → (α · refl) ≡ (α ·' refl))
                 (λ p → hor-comm0 _ p)
                 α 

 hor-comm2 : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → {r s : b ≡ c} → (β : r ≡ s)
                 → (α · β) ≡ (α ·' β)
 hor-comm2 α β = j (λ r s β → (α · β) ≡ (α ·' β))
                   (λ r → hor-comm1 α)
                   β

 u : {A : Set} → {a : A} → refl {A} {a} ≡ refl ■ refl
 u = lemma-2-1-4-i-a
 
 v : {A : Set} → {a : A} → refl {A} {a} ≡ refl ■ refl
 v = lemma-2-1-4-i-b

 eckmann-hilton : {A : Set} → {a : A} → (α β : Ω² A a) →  α ■ β ≡ β ■ α
 eckmann-hilton α β =
               α ■ β
                 ≡⟨ p≡p■refl ⟩
               (α ■ β) ■ refl
                 ≡⟨ ■-assoc (α ■ β) v (v ⁻¹)⟩
               ((α ■ β) ■ v) ■ v ⁻¹
                 ≡⟨ ap (λ Q → Q ■ v ⁻¹) (
                     (α ■ β) ■ v
                       ≡⟨ ■-assoc' α β v ⟩
                     (α ■ (β ■ v))
                       ≡⟨ p≡refl■p ⟩
                     refl ■ (α ■ (β ■ v))
                       ≡⟨ ■-assoc' u (u ⁻¹) (α ■ (β ■ v)) ⟩
                     u ■ (u ⁻¹ ■ (α ■ (β ■ v))) ≡⟨
                       ap (λ Q → u ■ Q) (
                         u ⁻¹ ■ (α ■ (β ■ v))
                            ≡⟨ ap (λ Q → u ⁻¹ ■ Q) (
                               α ■ (β ■ v) 
                                ≡⟨ ap (λ Q → (α ■ Q)) p≡refl■p ⟩
                               (α ■ ((u ■ v ⁻¹) ■ (β ■ v)))
                                 ≡⟨ ap (λ Q → (α ■ Q)) (■-assoc' u (v ⁻¹) (β ■ v)) ⟩
                               (α ■ (u ■ (v ⁻¹ ■ (β ■ v))))
                                 ≡⟨ ap (λ Q → (α ■ (u ■ Q))) (■-assoc (v ⁻¹) β v) ⟩
                               (α ■ (u ■ ((v ⁻¹ ■ β) ■ v)))
                                 ≡⟨ (■-assoc α u ((v ⁻¹ ■ β) ■ v)) ⟩
                               (α ■ u) ■ ((v ⁻¹ ■ β) ■ v)
                               ▻
                            ) ⟩
                         u ⁻¹ ■ ((α ■ u) ■ ((v ⁻¹ ■ β) ■ v))
                            ≡⟨ ■-assoc (u ⁻¹) ((α ■ u)) ((v ⁻¹ ■ β) ■ v) ⟩
                         α · β
                            ≡⟨ hor-comm2 α β ⟩
                         α ·' β
                            ≡⟨ ap (λ Q → Q ■ ((u ⁻¹ ■ (α ■ u)))) (■-assoc' (v ⁻¹) β v) ⟩
                         (v ⁻¹ ■ (β ■ v)) ■ ((u ⁻¹ ■ (α ■ u)))
                           ≡⟨ (■-assoc (v ⁻¹) (β ■ v) (u ⁻¹ ■ (α ■ u)))⁻¹ ⟩
                         v ⁻¹ ■ ((β ■ v) ■ (u ⁻¹ ■ (α ■ u)))
                           ≡⟨ ap (λ Q → v ⁻¹ ■ Q) (■-assoc' β v (u ⁻¹ ■ (α ■ u)))  ⟩
                         v ⁻¹ ■ (β ■ (v ■ (u ⁻¹ ■ (α ■ u))))
                           ≡⟨ ap (λ Q → v ⁻¹ ■ (β ■ Q)) (■-assoc v (u ⁻¹) (α ■ u)) ⟩
                         v ⁻¹ ■ (β ■ (refl ■ (α ■ u)))
                            ≡⟨ ap (λ Q → v ⁻¹ ■ (β ■ Q)) (p≡refl■p ⁻¹) ⟩
                         v ⁻¹ ■ (β ■ (α ■ u))
                         ▻) ⟩
                     u ■ (v ⁻¹ ■ (β ■ (α ■ u)))
                       ≡⟨ ■-assoc u (v ⁻¹) (β ■ (α ■ u))⟩
                     refl ■ (β ■ (α ■ u))
                       ≡⟨ p≡refl■p ⁻¹ ⟩
                     β ■ (α ■ u)
                     ▻ ) 
                 ⟩
               (β ■ (α ■ u)) ■ v ⁻¹
                 ≡⟨ ■-assoc' β (α ■ u) (v ⁻¹) ⟩
               β ■ ((α ■ u) ■ v ⁻¹)
                 ≡⟨ ap (λ Q → β ■ Q) (■-assoc' α u (v ⁻¹)) ⟩
               β ■ (α ■ refl)
                 ≡⟨ ap (λ Q → β ■ Q) (p≡p■refl ⁻¹)⟩
               β ■ α
               ▻

 lemma-2-2-2-i-0 : {A B : Set} → {z : A} → (f : A → B)
               → ap f (refl' z ■ refl' z) ≡ ap f (refl' z) ■ ap f (refl' z)
 lemma-2-2-2-i-0 f = refl

 lemma-2-2-2-i-1 : {A B : Set} → (f : A → B) → {y z : A} → {q : y ≡ z}
               → ap f (refl ■ q) ≡ ap f refl ■ ap f q
 lemma-2-2-2-i-1 {A} {B} f {y} {z} {q} =
                 j (λ y z q → ap f (refl' y ■ q) ≡ ap f (refl' y) ■ ap f q)
                 (λ y → lemma-2-2-2-i-0 {A} {B} {y} f)
                 q

 lemma-2-2-2-i : {A B : Set} → (f : A → B) → {x y z : A} → (p : x ≡ y) → {q : y ≡ z}
                  → ap f (p ■ q) ≡ ap f p ■ ap f q
 lemma-2-2-2-i f p {q} = j₂ (λ x y z p q → ap f (p ■ q) ≡ ap f p ■ ap f q)
                             (λ x → refl)
                             p q

 lemma-2-2-2-ii-0 : {A B : Set} → (f : A → B) → {y : A}
                  → ap f ((refl' y) ⁻¹) ≡ (ap f refl) ⁻¹
 lemma-2-2-2-ii-0 f = refl

 lemma-2-2-2-ii : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y)
                → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
 lemma-2-2-2-ii f p = j (λ x y p → ap f (p ⁻¹) ≡ (ap f p) ⁻¹)
                        (λ x → lemma-2-2-2-ii-0 f)
                        p

 -- composition
 _○_ : {A B C : Set} → (B → C) → (A → B) → A → C
 g ○ f = λ x → g (f x)


 _□ : (p : Set) → p → p
 p □ = id

 _→⟨_⟩_ : {q r : Set} → (p : Set) → (p → q) → (q → r) → (p → r)
 p →⟨ α ⟩ β = β ○ α

 lemma-2-2-iii-0 : {A B C : Set} → (f : A → B) → (g : B → C)
                → {x : A}
                → ap g (ap f (refl' x)) ≡ ap (g ○ f) (refl' x)
 lemma-2-2-iii-0 f g = refl

 lemma-2-2-iii : {A B C : Set} → (f : A → B) → (g : B → C)
                → {x y : A} → (p : x ≡ y)
                → ap g (ap f p) ≡ ap (g ○ f) p
 lemma-2-2-iii f g p = j (λ x y p → ap g (ap f p) ≡ ap (g ○ f) p)
                         (λ x → lemma-2-2-iii-0 f g)
                         p

-- id : {A : Set} → A → A
-- id x = x

 lemma-2-2-iv-0 : {A : Set} → {x : A} → ap id (refl' x) ≡ refl' x
 lemma-2-2-iv-0 = refl

 lemma-2-2-iv : {A : Set} → {x y : A} → (p : x ≡ y) → ap id p ≡ p
 lemma-2-2-iv p = j (λ x y p → ap id p ≡ p)
                    (λ x → lemma-2-2-iv-0)
                    p

 -- Lemma 2.3.1
 transport : {A : Set} → (P : A → Set) → {x y : A} → (p : x ≡ y) → P x → P y
 transport P p = j (λ x y p → P x → P y)
                 (λ x -> id)        
                 p

 _∗ : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → P x → P y
 p ∗ = transport _ p

 -- dependent product

 data ∑ (A : Set) (B : A → Set) : Set where
   _,_ : (a : A) → B a → ∑ A B

 infixr 4 _,_

 pr₁ : {A : Set} {B : A → Set} → ∑ A B → A
 pr₁ (a , _) = a
 pr₂ : {A : Set} {B : A → Set} → (p : ∑ A B) → B (pr₁ p)
 pr₂ (_ , b) = b

 rec∑₀ : {A : Set} {B : A → Set} → {C : Set} → ((x : A) → B x → C) → (∑ A B) → C
 rec∑₀ f (a , b) = f a b
                       
 rec∑₁ : {A : Set} {B : A → Set} → {C : Set} → ((x : A) → B x → C) → (∑ A B) → C
 rec∑₁ f x = f (pr₁ x) (pr₂ x)

 -- Path lifting property
 lift : {A : Set} → {P : A → Set} → {x y : A} → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , (p ∗) u)
 lift {A} {P} {x} {y} u p = (j (λ x y p → (u : P x) → (_,_ {_} {P} x u) ≡ (y , (p ∗) u))
                               (λ x u → refl)
                               p) u

 -- Lemma 2.3.4 (Dependent map)
 -- Generalisation of functoriality to dependent functions.
 apd : {A : Set} → {P : A → Set} → (f : (x : A) → P x) → {x y : A} → (p : x ≡ y) → (p ∗) (f x) ≡ f y
 apd f p = j (λ x y p → (p ∗) (f x) ≡ f y)
             (λ x → refl)
             p

 -- Lemma 2.3.5
 -- Transport does obvious thing with constant fibres.
 transportconst : {A : Set} → {x y : A} → (B : Set) → (p : x ≡ y) → (b : B)
                → transport (λ x → B) p b ≡ b
 transportconst B p b = j (λ x y p → transport (λ x → B) p b ≡ b)
                          (λ x → refl)
                          p

-- ap f p : f x ≡ f y
-- transportconst B p (f x) : transport (λ x → B) p (f x) ≡ f x
-- transportconst B p (f x) ■ ap f p : transport (λ x → B) p (f x) ■ f y
-- apd f p : transport _ p (f x) ≡ f y
-- Lift ends of p to f x and f y. Transport f x along p. You should get f y.
 lemma-2-3-8 : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y) → apd f p ≡ transportconst B p (f x) ■ ap f p
 lemma-2-3-8 f p = j (λ x y p → apd f p ≡ transportconst _ p (f x) ■ ap f p)
                     (λ x → refl)
                     p

 lemma-2-3-9-0 : {A : Set} → {P : A → Set} → (x y : A) → (p : x ≡ y)
               → (u : P x) → (transport P refl) ((p ∗) u) ≡ (transport P (p ■ refl)) u
 lemma-2-3-9-0 {A} {P} x y p = j (λ x y p → (u : P x) → (transport P refl) ((p ∗) u) ≡ (transport P (p ■ refl)) u)
                                 (λ x u → refl)
                                 p

{-
 lemma-2-3-9 : {A : Set} → {P : A → Set} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)
             → (u : P x) → (transport P q) ((p ∗) u) ≡ ((p ■ q)∗) u
 lemma-2-3-9 {A} {P} x y z p q = (j (λ y z q → (p : x ≡ y) → (u : P x) → (transport P q) ((p ∗) u) ≡ ((p ■ q)∗) u)
                         (λ y → lemma-2-3-9-0 {A} {P} x y)
                         q) p
-}

{-
 j₂ : {A : Set} (C : (x y z : A) → x ≡ y → y ≡ z → Set)
      → ((x : A) → C x x x refl refl)
      → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
      → C x y z p q
-}

 lemma-2-3-9 : {A : Set} → {P : A → Set} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)
             → (u : P x) → (transport P q) ((p ∗) u) ≡ ((p ■ q)∗) u
 lemma-2-3-9 {A} {P} x y z p q = j₂ (λ x y z p q → (u : P x) → (transport P q) ((p ∗) u) ≡ ((p ■ q)∗) u)
                                     (λ x₁ u → refl)
                                     p q

 lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                            → transport (P ○ f) p u ≡ transport P (ap f p) u
 lemma-2-3-10 f P p = j (λ x y p → (u : P (f x)) → transport (P ○ f) p u ≡ transport P (ap f p) u)
                        (λ x u → refl)
                        p
 lemma-2-3-11 : {A : Set} → (P Q : A → Set) → {x y : A} → (f : (x : A) → P x → Q x) → (p : x ≡ y) → (u : P x)
                          → transport Q p (f x u) ≡ f y (transport P p u)
 lemma-2-3-11 {A} P Q f p u = (j (λ x y p → (f : (x : A) → P x → Q x) → (u : P x)
                                          → transport Q p (f x u) ≡ f y (transport P p u))
                        (λ x f u → refl)
                        p) f u

 _~_ : {A : Set} → {P : A → Set} → (f g : (x : A) → P x) → Set
 f ~ g = (x : _) → f x ≡ g x

 lemma-2-4-2-i : {A B : Set} → (f : A → B) → f ~ f
 lemma-2-4-2-i f x = refl
 
 lemma-2-4-2-ii : {A B : Set} → (f g : A → B) → (f ~ g) → (g ~ f)
 lemma-2-4-2-ii f g H x = (H x)⁻¹

 lemma-2-4-2-iii : {A B : Set} → (f g h : A → B) → (f ~ g) → (g ~ h) → (f ~ h)
 lemma-2-4-2-iii f g h H I x = H x ■ I x

{-
 lemma-2-1-4-i-a : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■ refl)
 lemma-2-1-4-i-b : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■ p)
-}


 -- lemma-2-2-iv : {A : Set} → {x y : A} → (p : x ≡ y) → ap id p ≡ p
 -- ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
 -- transport : {A : Set} → (P : A → Set) → {x y : A} → (p : x ≡ y) → P x → P y
 -- _∗_ : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → P x → P y

 -- want from x ≡ y to get p x → p y

 -- lemma-2-1-4-iv : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → {w : A} → (r : z ≡ w)
 --                → (p ■ (q ■ r)) ≡ ((p ■ q) ■ r)

 -- subst : a ≡ b → f a ≡ f b
 -- syntax bind e1 (\x → e2) = x ← e1 ; e2

-- rightreducxse : {A : Set} → {x y z : A} → (p : x ≡ y) → (r : y ≡ z) → p ■ (r ■ (r ⁻¹)) ≡ p
-- rightreduce p r = ap (λ Q → p ■ Q) (lemma-2-1-4-iib r) ■ (lemma-2-1-4-i-a ⁻¹)

 -- a(bc) =[ assoc ] (ab)c =[ comm ] (ba)c
 -- assoc ■ comm

 ap₂ : {A B C : Set} → (f : A → B → C) → {x y : A} → (x ≡ y) → {z w : B} → (z ≡ w) → (f x z ≡ f y w)
 ap₂ f {x} {y} p {z} {w} q = f x z ≡⟨ ap (λ Q → f x Q) q ⟩
                             f x w ≡⟨ ap (λ Q → f Q w) p ⟩
                             f y w
                             ▻

 rightcancel : {A : Set} → {x y z : A} → (p q : x ≡ y) → (r : y ≡ z) → (p ■ r) ≡ (q ■ r) → p ≡ q
 rightcancel p q r α = p                ≡⟨ lemma-2-1-4-i-a ⟩
                       p ■ refl         ≡⟨ ap (λ Q → p ■ Q) ((lemma-2-1-4-iib r) ⁻¹) ⟩
                       p ■ (r ■ (r ⁻¹)) ≡⟨ lemma-2-1-4-iv p r (r ⁻¹) ⟩
                       (p ■ r) ■ (r ⁻¹) ≡⟨ ap (λ Q → Q ■ (r ⁻¹)) α ⟩
                       (q ■ r) ■ (r ⁻¹) ≡⟨ (lemma-2-1-4-iv q r (r ⁻¹))⁻¹ ⟩
                       q ■ (r ■ (r ⁻¹)) ≡⟨ ap (λ Q → q ■ Q) (lemma-2-1-4-iib r) ⟩
                       q ■ refl         ≡⟨ lemma-2-1-4-i-a ⁻¹ ⟩
                       q
                       ▻


{-
 lemma-2-1-4-i-a : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (p ■ refl)
 lemma-2-1-4-i-b : {A : Set} → {x y : A} → {p : x ≡ y} → p ≡ (refl ■ p)
-}
 -- lemma-2-1-4-iib : {A : Set} → {x y : A} → (p : x ≡ y) → (p ■ p ⁻¹) ≡ refl
 -- rightcancel : {A : Set} → {x y z : A} → (p q : x ≡ y) → (r : y ≡ z) → (p ■ r) ≡ (q ■ r) → p ≡ q
 -- rightcancel {A} {x} {y} {z} p q r α = ap (λ Q → ((lemma-2-1-4-iv Q r (r ⁻¹)) ⁻¹)) (rightcancel0 p q r α)

 lemma-2-4-3-0 : {A B : Set} → (f g : A → B) → (H : f ~ g) → {x : A}
                             → H x ■ ap g refl ≡ ap f refl ■ H x
 lemma-2-4-3-0 {A} {B} f g H {x} = ((lemma-2-1-4-i-a {_} {_} {_} {H x})⁻¹) ■ (refl {f x ≡ g x} ■ lemma-2-1-4-i-b)

 lemma-2-4-3 : {A B : Set} → (f g : A → B) → (H : f ~ g) → {x y : A} → (p : x ≡ y)
                           → H x ■ ap g p ≡ ap f p ■ H y
 lemma-2-4-3 f g H p = j (λ x y p → H x ■ ap g p ≡ ap f p ■ H y)
                         (λ x → lemma-2-4-3-0 f g H)
                         p

 corollary-2-4-4' : {A : Set} → (f : A → A) → (H : f ~ id {A}) → (x : A) → H (f x) ■ H x ≡ ap f (H x) ■ H x
 corollary-2-4-4' f H x = H (f x) ■ H x         ≡⟨ ap (λ Q → H (f x) ■ Q) ((lemma-2-2-iv (H x))⁻¹) ⟩
                          H (f x) ■ ap id (H x) ≡⟨ lemma-2-4-3 f id H (H x) ⟩
                          ap f (H x) ■ H x
                          ▻

 corollary-2-4-4 : {A : Set} → (f : A → A) → (H : f ~ id {A}) → (x : A) →  H (f x) ≡ ap f (H x)
 corollary-2-4-4 f H x = rightcancel _ _ _ (corollary-2-4-4' f H x)

 _×_ : Set → Set → Set
 A × B = ∑ A (λ _ → B)

 qinv : {A B : Set} → (f : A → B) → Set
 qinv {A} {B} f = ∑ (B → A) (λ g → ((f ○ g) ~ id) × ((g ○ f) ~ id))

 ex-2-4-7 : {A : Set} → qinv (id {A})
 ex-2-4-7 {A} = (id , ((λ x → refl) , (λ x → refl)))

 ex-2-4-8a : {A : Set} → {x y z : A} → {p : x ≡ y} → qinv (λ q → p ■ q)
 ex-2-4-8a {A} {x} {y} {z} {p} = ((λ q → (p ⁻¹) ■ q) , β , α)
                                 where α : (q : y ≡ z) → (p ⁻¹) ■ (p ■ q) ≡ q
                                       α q = (p ⁻¹) ■ (p ■ q) ≡⟨ lemma-2-1-4-iv (p ⁻¹) p q ⟩
                                             ((p ⁻¹) ■ p) ■ q ≡⟨ ap (λ Q → Q ■ q) (lemma-2-1-4-iia p) ⟩ 
                                             refl ■ q         ≡⟨ lemma-2-1-4-i-b ⁻¹ ⟩ 
                                             q
                                             ▻
                                       β : (q : x ≡ z) → p ■ ((p ⁻¹) ■ q) ≡ q
                                       β q = p ■ ((p ⁻¹) ■ q) ≡⟨ lemma-2-1-4-iv p (p ⁻¹) q ⟩
                                             (p ■ (p ⁻¹)) ■ q ≡⟨ ap (λ Q → Q ■ q) (lemma-2-1-4-iib p) ⟩ 
                                             refl ■ q         ≡⟨ lemma-2-1-4-i-b ⁻¹ ⟩ 
                                             q
                                             ▻
 ex-2-4-8b : {A : Set} → {x y z : A} → {p : x ≡ y} → qinv (λ q → q ■ p)
 ex-2-4-8b {A} {x} {y} {z} {p} = ((λ q → q ■ (p ⁻¹)) , β , α)
                                 where α : (q : z ≡ x) → (q ■ p) ■ (p ⁻¹) ≡ q
                                       α q = (q ■ p) ■ (p ⁻¹) ≡⟨ (lemma-2-1-4-iv q p (p ⁻¹))⁻¹ ⟩
                                             q ■ (p ■ (p ⁻¹)) ≡⟨ ap (λ Q → q ■ Q) (lemma-2-1-4-iib p) ⟩ 
                                             q ■ refl         ≡⟨ lemma-2-1-4-i-a ⁻¹ ⟩ 
                                             q
                                             ▻
                                       β : (q : z ≡ y) → (q ■ (p ⁻¹)) ■ p ≡ q
                                       β q = (q ■ (p ⁻¹)) ■ p ≡⟨ (lemma-2-1-4-iv q (p ⁻¹) p)⁻¹ ⟩
                                             q ■ ((p ⁻¹) ■ p) ≡⟨ ap (λ Q → q ■ Q) (lemma-2-1-4-iia p) ⟩ 
                                             q ■ refl         ≡⟨ lemma-2-1-4-i-a ⁻¹ ⟩ 
                                             q
                                             ▻
 {-
 lemma-2-3-9 : {A : Set} → {P : A → Set} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)
             → (u : P x) → (transport P q) ((p ∗) u) ≡ ((p ■ q)∗) u
 -}

 ex-2-4-9 : {A : Set} → {x y : A} → (p : x ≡ y) → (P : A → Set) → qinv (transport P p)
 ex-2-4-9 {A} {x} {y} p P = (transport P (p ⁻¹) , β , α)
                        where α : (u : P x) → transport P (p ⁻¹) (transport P p u) ≡ u
                              α u = transport P (p ⁻¹) (transport P p u) ≡⟨ lemma-2-3-9 {A} {P} x y x p (p ⁻¹) u ⟩
                                    transport P (p ■ (p ⁻¹)) u ≡⟨ ap (λ Q → transport P Q u) (lemma-2-1-4-iib p) ⟩
                                    u
                                    ▻
                              β : (u : P y) → transport P p (transport P (p ⁻¹) u) ≡ u
                              β u = transport P p (transport P (p ⁻¹) u) ≡⟨ lemma-2-3-9 {A} {P} y x y (p ⁻¹) p u ⟩
                                    transport P ((p ⁻¹) ■ p) u ≡⟨ ap (λ Q → transport P Q u) (lemma-2-1-4-iia p) ⟩
                                    u
                                    ▻
{-
 qinv : {A B : Set} → (f : A → B) → Set
 qinv {A} {B} f = ∑ (B → A) (λ g → ((f ○ g) ~ id) × ((g ○ f) ~ id))
-}

 isequiv : {A B : Set} → (f : A → B) → Set
 isequiv {A} {B} f = (∑ (B → A) (λ g → (f ○ g) ~ id) × (∑ (B → A) (λ h → (h ○ f) ~ id)))

 qinv-to-isequiv : {A B : Set} → (f : A → B) → qinv f → isequiv f
 qinv-to-isequiv f (g , (α , β)) = ((g , α) , (g , β))

 {-
 β : h ○ f ~ id
 β u : h (f u) ≡ u
 want
 b : g ~ h ○ f ○ g
 b u = g u ≡ h (f (g u))

 α : f ○ g ~ id
 α u : f (g u) ≡ u
 want
 a : h ○ f ○ g ~ h
 a u = h (f (g u)) ≡ h u

 γ : g ~ h
 γ u : g u ≡ h u

 β' : g ○ f ~ id
 β' u : g (f u) ≡ u

 β' u = γ (f u) ■ β u
 -}

 isequiv-to-qinv : {A B : Set} → (f : A → B) → isequiv f → qinv f
 isequiv-to-qinv f ((g , α) , (h , β)) = (g , (α , β'))
                                         where γ : g ~ h
                                               γ u = ((β (g u))⁻¹) ■ ap h (α u)
                                               β' : (g ○ f) ~ id
                                               β' u = γ (f u) ■ β u

 _≃_ : (A B : Set) → Set
 A ≃ B = ∑ (A → B) (λ f → isequiv f)

 lemma-2-4-12i : {A : Set} → isequiv (id {A})
 lemma-2-4-12i {A} = (id , (λ x → refl)) , id , (λ x → refl)

 lemma-2-4-12i' : (A : Set) → A ≃ A
 lemma-2-4-12i' A = (id , lemma-2-4-12i)

 -- α : f ○ f' ~ id
 -- β : f' ○ f ~ id
 lemma-2-4-12ii : {A B : Set} → A ≃ B → B ≃ A
 lemma-2-4-12ii (f , f-is-equiv) with isequiv-to-qinv f f-is-equiv
 lemma-2-4-12ii (f , f-is-equiv) | (f' , (α , β)) =
                                   (f' , qinv-to-isequiv f' (f , (β , α)))
 {-
 α : f ○ f' ~ id
 α u : f (f' u) ≡ u
 β : f' ○ f ~ id
 γ : g ○ g' ~ id
 δ : g' ○ g ~ id

 want
 μ : (g ○ f) ○ (f' ○ g') ~ id
 -}

 lemma-2-4-12iii : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
 lemma-2-4-12iii (f , f-is-equiv) (g , g-is-equiv) with isequiv-to-qinv f f-is-equiv
 lemma-2-4-12iii (f , f-is-equiv) (g , g-is-equiv) | (f' , (α , β)) with isequiv-to-qinv g g-is-equiv
 lemma-2-4-12iii {A} {B} {C} (f , f-is-equiv) (g , g-is-equiv) | (f' , (α , β)) | (g' , (γ , δ))
                 = (g ○ f , qinv-to-isequiv (g ○ f) ( f' ○ g' , ( μ , ν ) ))
                   where μ : (u : C) → g (f (f' (g' u))) ≡ u
                         μ u = g (f (f' (g' u))) ≡⟨ ap (λ Q → g Q) (α (g' u)) ⟩
                               g (g' u) ≡⟨ γ u ⟩
                               u
                               ▻
                         ν : (u : A) → f' (g' (g (f u))) ≡ u
                         ν u = f' (g' (g (f u))) ≡⟨ ap (λ Q → f' Q) (δ (f u)) ⟩
                               f' (f u)          ≡⟨ β u ⟩
                               u
                               ▻

 -- 2.6.1
 ipair : {A B : Set} → {x : A × B} → {y : A × B} → x ≡ y → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
 ipair p = (ap pr₁ p , ap pr₂ p)

 pair' : {A B : Set} → (a : A) → {b b' : B} → b ≡ b' → (a , b) ≡ (a , b')
 pair' a q = j (λ b b' q → (a , b) ≡ (a , b'))
              (λ b → refl)
              q
-- 2.6.3
 pair : {A B : Set} → {a a' : A} → {b b' : B} → (a ≡ a') × (b ≡ b') → (a , b) ≡ (a' , b')
 pair {A} {B} {a} {a'} {b} {b'} (p , q) = j (λ a a' p → (a , b) ≡ (a' , b'))
                                    (λ a → pair' a q)
                                    p

 {-                                       
 j : {A : Set}
     → (C : (x y : A) → x ≡ y → Set)
     → ((x : A) → C x x refl)
     → {M N : A}
     → (P : M ≡ N)
     → C M N P
 j _ b refl = b _
 -}

 {-
 assume r = refl
 ipair : r -> (refl {pr₁ x} , refl {pr₂ x})
 assume x = (a , b)
           -> (refl {a} , refl {b})
           -(pair)-> refl {a , b}
 -}

 rec∑ : {A B C : Set} → (A → B → C) → (x : A × B) → C
 rec∑ f (a , b) = f a b

 ind∑ : {A : Set} {B : A → Set} → (C : (∑ A B) → Set) → ((a : A) → (b : B a) → C (a , b))
                                → (p : ∑ A B) → C p
 ind∑ C g (a , b) = g a b

 -- Lifts equalities at component level to equality at pair level
 module 2-6-2 where
   pair= : {A B : Set} → {x y : A × B} → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → x ≡ y
   pair= {A} {B} {a , b} {a' , b'} = pair {A} {B} {a} {a'} {b} {b'}

 h : {A B : Set} → {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ipair r) ≡ r
 h = j prop
     (ind∑ (λ x → prop x x refl) (λ a b → refl))
     where
       prop : {A B : Set} → (x : A × B) → (y : A × B) → (x ≡ y) → Set
       prop = ind∑ _ (λ a b →
              ind∑ _ (λ a' b' →
                λ r → pair (ipair r) ≡ r))


 k : {A B : Set} → {x y : A × B} → (s : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)) → ipair (pair s) ≡ s
 k {A} {B} {x} {y} =
                  ind∑ (λ x → (y : A × B) → (s : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
                            → ipair (pair s) ≡ s) (λ a b →                           -- on x
                  ind∑ _ (λ a' b' →                                                  -- on y
                  ind∑ _ (λ p q →                                                    -- on s
                  j (λ a a' p → (b b' : B) → (q : b ≡ b')
                              → ipair (pair (p , q)) ≡ (p , q)) (λ a b b' q →        -- on q
                  j (λ b b' q → (a : A)
                              → ipair (pair (refl {A} {a} , q)) ≡ refl , q) (λ x a → -- on p
                  refl) q a) p b b' q))) x y
                                           
 theorem-2-6-2 : {A B : Set} {x : A × B} → {y : A × B} → isequiv (ipair {A} {B} {x} {y})
 theorem-2-6-2 {A} {B} {(a , b)} {(a' , b')} = qinv-to-isequiv (ipair {A} {B} {a , b} {a' , b'})
                                                               (pair {A} {B} , ( k {A} {B} {a , b} {a' , b'}, h ))

 prop-uniq-pair : {A B : Set} → {x y : A × B} → {r : x ≡ y} → r ≡ 2-6-2.pair= (ap pr₁ r , ap pr₂ r)
 prop-uniq-pair {A} {B} {a , b} {a' , b'} {r} = (h r)⁻¹

 refl× : {A B : Set} {z : A × B} → refl ≡ 2-6-2.pair= (refl , refl)
 refl× {_} {_} {z} = refl {_} {z} ≡⟨ prop-uniq-pair ⟩
                     2-6-2.pair= (ap pr₁ (refl {_} {z}), ap pr₂ (refl {_} {z}))
                                          ≡⟨ ap₂ (λ P Q → 2-6-2.pair= (P , Q)) refl refl ⟩
                     2-6-2.pair= (refl , refl)
                     ▻

 ×⁻¹ : {A B : Set} {x y : A × B} (p : x ≡ y) → p ⁻¹ ≡ 2-6-2.pair= ((ap pr₁ p)⁻¹ , (ap pr₂ p)⁻¹)
 ×⁻¹ {x} {y} p = j (λ x y (p : x ≡ y) → p ⁻¹ ≡ 2-6-2.pair= ((ap pr₁ p)⁻¹ , (ap pr₂ p)⁻¹))
                   (λ x → refl×)
                   p

 ×■ : {A B : Set} {x y z : A × B} (p : x ≡ y) (q : y ≡ z) → p ■ q ≡ 2-6-2.pair= (ap pr₁ p ■ ap pr₁ q , ap pr₂ p ■ ap pr₂ q)
 ×■ p q = j₂ (λ x y z p q → p ■ q ≡ 2-6-2.pair= (ap pr₁ p ■ ap pr₁ q , ap pr₂ p ■ ap pr₂ q))
             (λ x → refl ■ refl ≡⟨ prop-uniq-pair ⟩
                    2-6-2.pair= (ap pr₁ {x} (refl ■ refl) , ap pr₂ {x} (refl ■ refl))
                                        ≡⟨ ap₂ (λ P Q → 2-6-2.pair= (P , Q))
                                               (lemma-2-2-2-i pr₁ {x} refl {refl})
                                               (lemma-2-2-2-i pr₂ {x} refl {refl}) ⟩
                    2-6-2.pair= (ap pr₁ {x} refl ■ ap pr₁ {x} refl , ap pr₂ {x} refl ■ ap pr₂ {x} refl)
                    ▻)
                    p q

 uppt : {A B : Set} → (x : A × B) → (pr₁ x , pr₂ x) ≡ x
 uppt (a , b) = refl

 theorem-2-6-4 : {Z : Set} → {A B : Z → Set} → {w z : Z} → (p : z ≡ w) → (x : A z × B z) →
                          transport (λ z → A z × B z) p x ≡ (transport A p (pr₁ x) , transport B p (pr₂ x))
 theorem-2-6-4 {_} {A} {B} {w} {z} p
      = j (λ z w p → (x : A z × B z) → transport (λ z → A z × B z) p x ≡ (transport A p (pr₁ x) , transport B p (pr₂ x)))
          (λ x x₁ → transport (λ z₁ → A z₁ × B z₁) refl x₁
                      ≡⟨ (uppt x₁)⁻¹ ⟩
                    (transport A refl (pr₁ x₁) , transport B refl (pr₂ x₁))
                    ▻)
         p
 
 f-2-6-5 : {A B A' B' : Set} → (g : A → A') → (h : B → B') → (A × B) → (A' × B')
 f-2-6-5 g h x = (g (pr₁ x), h (pr₂ x))

 theorem-2-6-5 : {A B A' B' : Set} → (g : A → A') → (h : B → B') → (x y : A × B) → (p : pr₁ x ≡ pr₁ y) → (q : pr₂ x ≡ pr₂ y)
                 → ap (f-2-6-5 g h) (2-6-2.pair= {A} {B} {x} {y} (p , q))
                      ≡ 2-6-2.pair= {_} {_} {f-2-6-5 g h x} {f-2-6-5 g h y} (ap g p , ap h q)
 theorem-2-6-5 g h (a , b) (a' , b') p q =
          j (λ a a' p → ap (f-2-6-5 g h) (2-6-2.pair= {_} {_} {(_ , _)} {(_ , _)} (p , q))
                          ≡ 2-6-2.pair= (ap g p , ap h q))
            (λ a → j (λ b b' q → ap (f-2-6-5 g h) (2-6-2.pair= {_} {_} {_ , _} {_ , _} (refl , q))
                                   ≡ 2-6-2.pair= (refl , ap h q))
                     (λ b → refl)
                     q)
            p

 module 2-7 {A : Set} {P : A → Set} where

  module 2-7-2 where

   f : {w w' : ∑ A P} → (w ≡ w') → ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')
   f p = j (λ w w' p → ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w'))
                   (λ w → refl , refl)
                   p

   pair= : {w w' : ∑ A P}
                 → ∑ (pr₁ w ≡ pr₁ w') (λ p → (p ∗)(pr₂ w) ≡ pr₂ w') → (w ≡ w')
   pair= {_ , _} {_ , _} (p , q) =
         j (λ w₁ w₁' p → {w₂ : P w₁} →  {w₂' : P w₁'} → ((p ∗) w₂ ≡ w₂') → (w₁ , w₂) ≡ (w₁' , w₂'))
           (λ w₁ p → ap (λ Q → (w₁ , Q)) p) -- tiny mod from book
           p q 

   private fg≡id : {w w' : ∑ A P}
                   → (r : ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w'))
                   → f {w} {w'} (pair= r) ≡ r
           fg≡id {w₁ , w₂} {w₁' , w₂'} (p , q) =
                   j (λ w₁ w₁' p → (w₂ : P w₁) →  (w₂' : P w₁') → (q : (p ∗) w₂ ≡ w₂')
                        → f {w₁ , w₂} {w₁' , w₂'} (pair= (p , q)) ≡ (p , q))
                     (λ w₁ w₂ w₂' q → j (λ _ _ q → f {_ , _} {_ , _} (pair= (refl , q)) ≡ (refl , q))
                                        (λ x → refl)
                                        q)
                     p w₂ w₂' q 

   private gf≡id : {w w' : ∑ A P} → (p : w ≡ w') → pair= (f p) ≡ p
           gf≡id p = j (λ _ _ p → pair= (f p) ≡ p)
                       (λ _ → ind∑ (λ w → pair= (f (refl {_} {w})) ≡ refl {_} {w}) (λ _ _ → refl) _)
                       p

   private qinv-f : {w w' : ∑ A P} → qinv (f {w} {w'})
           qinv-f {w} {w'} = (pair= , (fg≡id {w} {w'} , gf≡id))

   theorem-2-7-2 :  {w w' : ∑ A P}
                   → (w ≡ w') ≃ ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')
   theorem-2-7-2 = ( f , qinv-to-isequiv f qinv-f )

  theorem-2-7-2 = 2-7-2.theorem-2-7-2

  corollary-2-7-3 : (z : ∑ A P) → z ≡ (pr₁ z , pr₂ z)
  corollary-2-7-3 z = 2-7-2.pair= (refl , refl)

  module 2-7-4 {Q : (∑ A P) → Set} where

    private R = λ x → ∑ (P x) (λ u → Q (x , u))

    theorem-2-7-4 : {x y : A} → (p : x ≡ y) → (u : P x) → (z : Q (x , u))
                  → (transport R p) (u , z) ≡ ((p ∗) u , transport Q (2-7-2.pair= (p , refl {P y} {(p ∗) u})) z)
    theorem-2-7-4 = {!!}

