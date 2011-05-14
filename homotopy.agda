{-# OPTIONS --without-K #-}

module homotopy where

infix 3 _≡_

data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

--sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
--sym refl = refl

--trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
--trans refl refl = refl

j : {A : Set} (C : (x y : A) → x ≡ y -> Set)
  → {M N : A} → (P : M ≡ N)
  → ((x : A) → C x x refl)
  → C M N P
j C {M} {.M} refl b = b M

{-
j2 : {A : Set} (D : (x y : A) (x' y' : B) → x ≡ y → x' ≡ y' -> Set)
  → {M N : A} → (P : M ≡ N)
  → {M' N' : B} → (P' : M' ≡ N')
  → ((x : A) → (y : B) → D x x y y refl)
  → D M N M' N' P P'
j2 C {M} {.M} refl b = b M
-}

sym : {a : Set} {x y : a} → x ≡ y → y ≡ x 
sym p = j (λ x y _ → y ≡ x) p (λ _ → refl)

subst : {A : Set} (p : A -> Set) {x y : A} -> x ≡ y -> p x -> p y
subst C p = j (λ x y _ → C x → C y) p (λ x → λ x' → x')

trans : {A : Set} {M N P : A} -> M ≡ N -> N ≡ P -> M ≡ P
trans {A}{M}{N}{P} a b = subst (\ x -> M ≡ x) b a

infix  2 _∎
infixr 2 _≃⟨_⟩_ 
 
_≃⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≃⟨ p1 ⟩ p2 = (trans p1 p2)

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_∎ _ = refl


subst' : {A : Set} (p : A → Set) {x y : A} -> x ≡ y -> p x → p y
subst' p proof = j (λ x y _ → (p x → p y)) proof (λ x → λ y → y) 

--trans' : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
--trans' {A} {x} {y} {z} x≡y = j (λ x y _ → y ≡ z → x ≡ z) x≡y (λ z → λ x → x)

sym' : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym' {A} {x} {y} x≡y = j (λ x y _ → y ≡ x) x≡y (λ z → refl)

-- refl is unit proof on left
trans-unit-left : {A : Set} {M N : A} -> (p : M ≡ N) -> trans refl p ≡ p
trans-unit-left q = j (λ x y p → trans refl p ≡ p) q (λ x → refl)

trans-unit-right : {A : Set} {m n : A} → (p : m ≡ n) → trans p refl ≡ p
trans-unit-right q = j (λ x y p → trans p refl ≡ p) q (λ x → refl)

lemma : {A : Set} {x y z : A} (p : x ≡ y) {p' q' : y ≡ z} 
           -> p' ≡ q' -> trans p p' ≡ trans p q'
lemma p proof = j (λ p' q' z → trans p p' ≡ trans p q') proof (λ x → refl)

resp : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
resp f proof = j (λ x y _ → f x ≡ f y) proof (λ x → refl)

lemma2 : {A B C : Set} -> {x x' : A} → (w : B) → (f : A → B -> C) → x ≡ x' → f x w ≡ f x' w
lemma2 w f proofx = resp (λ z → f z w) proofx

resp2 : {A B C : Set} -> {x x' : A} -> {y y' : B} → (f : A → B -> C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
resp2 {A} {B} {C} {x} {x'} {y} {y'} f proofx proofy =
  j (λ y y' p → f x y ≡ f x' y') proofy (\z → lemma2 z f proofx)

-- composing proofs respects equality
resptrans : {A : Set} {x y z : A} {p q : x ≡ y} {p' q' : y ≡ z} 
           -> p ≡ q -> p' ≡ q' -> trans p p' ≡ trans q q'
resptrans a b = resp2 trans a b 

resptrans-unit-r : {A : Set} {x y : A} {p q : x ≡ y} 
                  → (a : p ≡ q) → (resptrans a (refl{_}{refl})) ≡ a
resptrans-unit-r a = j (λ _ _ p → (resptrans p (refl {_} {refl})) ≡ p) a (λ _ → refl)

resptransrefl : {A : Set} {x y : A} → (p : x ≡ y) (q : x ≡ y) → (a : p ≡ q) → trans refl p ≡ trans refl q 
resptransrefl p q a = resp (trans refl) a

resptransrefl' : {A : Set} {x y : A} → (p : x ≡ y) (q : x ≡ y) → (a : p ≡ q) → trans refl p ≡ trans refl q 
resptransrefl' p q a = trans refl p  ≃⟨ trans-unit-left p ⟩ 
                       p             ≃⟨ a ⟩
                       q             ≃⟨ sym (trans-unit-left q)⟩
                       trans refl q ∎

resptrans-unit-left : {A : Set} {x y : A} {p q : x ≡ y} 
                  -> (a : p ≡ q) -> (resptransrefl p q a) ≡ resptransrefl' p q a
                                                   

resptrans-unit-left a = j
                       (λ p' q' a' → resptransrefl p' q' a' ≡ resptransrefl' p' q' a')
                        a
                       (λ x → j (λ _ _ x' → refl ≡ resptransrefl' x' x' refl) x (λ _ → refl))

Refl : {A : Set} → {a : A} → a ≡ a
Refl = refl


Id : {A : Set} → A -> A -> Set
Id = _≡_

_≃_ : {A : Set} -> A -> A -> Set
_≃_ = Id

jay : {A : Set} (C : (x y : A) -> Id x y -> Set)
    -> {M N : A} -> (P : Id M N)
    -> ((x : A) -> C x x Refl)
    -> C M N P
jay = j

trans-resptrans-ichange : {A : Set} {x y z : A} 
             (p q : x ≡ y) 
          -> (a : p ≡ q) (r : x ≡ y) (b : q ≡ r) 
             (p' q' : y ≡ z) (c : p' ≡ q') 
             (r' : y ≡ z) (d : q' ≡ r') 
          -> (resptrans (trans a b) (trans c d)) ≡ (trans (resptrans a c) (resptrans b d))

trans-resptrans-ichange {A}{x}{y}{z} p q a = j
                 (λ p' q' a' →
                    (r : x ≡ y) (b : q' ≡ r) (p0 q0 : y ≡ z) (c : p0 ≡ q0) (r' : y ≡ z)
                    (d : q0 ≡ r') →
                    (resptrans (trans a' b) (trans c d)) ≡ (trans (resptrans a' c) (resptrans b d)))
                 a
                 (λ pq r b →
                    j
                    (λ pq' r' b' →
                       (p' q' : y ≡ z) (c : p' ≡ q') (r0 : y ≡ z) (d : q' ≡ r0) →
                       (resptrans (trans refl b') (trans c d)) ≡ (trans (resptrans refl c) (resptrans b' d)))
                    b
                    (λ pqr p' q' c →
                       j
                       (λ p0 q0 c' →
                          (r' : Id y z) (d : Id q0 r') →
                          (resptrans refl (trans c' d)) ≡ (trans (resptrans refl c') (resptrans refl d)))
                       c
                       (λ p'q' r' d →
                          j
                          (λ p'q0 r0 d' →
                             (resptrans refl (trans refl d')) ≡ (trans refl (resptrans refl d')))
                          d (λ _ → refl))))
