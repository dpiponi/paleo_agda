{-# OPTIONS --without-K #-}

module homotopy where

infix 3 _≡_

data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a


j : {A : Set} (C : (x y : A) → x ≡ y -> Set)
  → {M N : A} → (P : M ≡ N)
  → ((x : A) → C x x refl)
  → C M N P
j C {M} {.M} refl b = b M

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


{-
j2 : {A : Set} (D : (x y : A) (x' y' : B) → x ≡ y → x' ≡ y' -> Set)
  → {M N : A} → (P : M ≡ N)
  → {M' N' : B} → (P' : M' ≡ N')
  → ((x : A) → (y : B) → D x x y y refl)
  → D M N M' N' P P'
j2 C {M} {.M} refl b = b M
-}

subst : {A : Set} (p : A -> Set) {x y : A} -> x ≡ y -> p x -> p y
subst C p = j (λ x y _ → C x → C y) p (λ x → λ x' → x')

trans : {A : Set} {M N P : A} -> M ≡ N -> N ≡ P -> M ≡ P
trans {A}{M}{N}{P} a b = subst (\ x -> M ≡ x) b a

sym : {a : Set} {x y : a} → x ≡ y → y ≡ x 
sym p = j (λ x y _ → y ≡ x) p (λ _ → refl)

infix  2 _∎
infixr 2 _≃⟨_⟩_ 
 
_≃⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≃⟨ p1 ⟩ p2 = (trans p1 p2)

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_∎ _ = refl



-- refl is unit proof on left
trans-unit-left : {A : Set} {M N : A} -> (p : M ≡ N) -> trans refl p ≡ p
trans-unit-left q = j (λ x y p → trans refl p ≡ p) q (λ x → refl)

trans-unit-right : {A : Set} {m n : A} → (p : m ≡ n) → trans p refl ≡ p
trans-unit-right q = j (λ x y p → trans p refl ≡ p) q (λ x → refl)

lemma : {A : Set} {x y z : A} (p : x ≡ y) {p' q' : y ≡ z} 
           -> p' ≡ q' -> trans p p' ≡ trans p q'
lemma p proof = j (λ p' q' z → trans p p' ≡ trans p q') proof (λ x → refl)

--resp : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
--resp f proof = j (λ x y _ → f x ≡ f y) proof (λ x → refl)
resp : {A C : Set} {M N : A} (f : A -> C) -> M ≃ N -> f M ≡ f N
resp {A}{C}{M}{N} f a = subst (\ x -> f M ≡ f x) a refl

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
                       sym (trans-unit-left q)
--                       q             ≃⟨ sym (trans-unit-left q)⟩
--                       trans refl q ∎

resptrans-unit-left : {A : Set} {x y : A} {p q : x ≡ y} 
                  -> (a : p ≡ q) -> (resptransrefl p q a) ≡ resptransrefl' p q a
                                                   

resptrans-unit-left a = j
                       (λ p' q' a' → resptransrefl p' q' a' ≡ resptransrefl' p' q' a')
                        a
                       (λ x → j (λ _ _ x' → refl ≡ resptransrefl' x' x' refl) x (λ _ → refl))

{-
resptrans-unit-left : {A : Set} {x y : A} {p q : x ≡ y} 
                  -> (a : Id p q) -> Id (resptrans (Refl{_}{Refl}) a) ( (trans (trans-unit-left p) (trans a (sym (trans-unit-left q)))) )

resptrans-unit-left a = jay {_}
                        (λ p' q' a' →
                           Id (resp (trans Refl) a')
                           (trans (trans-unit-left p') (trans a' (sym (trans-unit-left q')))))
                        {_} {_} a
                        (λ x →
                           jay
                           (λ xend _ x' →
                              Id Refl
                              (subst (Id (subst (Id xend) x' Refl))
                               (subst (Id x')
                                (jay (λ x0 y _ → Id y x0)
                                 (jay (λ _ _ p' → Id (subst (Id _) p' Refl) p') x' (λ _ → Refl))
                                 (λ _ → Refl))
                                Refl)
                               (jay (λ _ _ p' → Id (subst (Id _) p' Refl) p') x' (λ _ → Refl))))
                           x (λ _ → Refl))

-}
{-
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
                          (r' : y ≡ z) (d : q0 ≡ r') →
                          (resptrans refl (trans c' d)) ≡ (trans (resptrans refl c') (resptrans refl d)))
                       c
                       (λ p'q' r' d →
                          j
                          (λ p'q0 r0 d' →
                             (resptrans refl (trans refl d')) ≡ (trans refl (resptrans refl d')))
                          d (λ _ → refl))))
-}
trans-resptrans-ichange : {A : Set} {x y z : A} 
             (p q : Id x y) 
          -> (a : Id p q) (r : Id x y) (b : Id q r) 
             (p' q' : Id y z) (c : Id p' q') 
             (r' : Id y z) (d : Id q' r') 
          -> Id (resptrans (trans a b) (trans c d)) (trans (resptrans a c) (resptrans b d))
trans-resptrans-ichange {A}{x}{y}{z} p q a = jay
                 (λ p' q' a' →
                    (r : Id x y) (b : Id q' r) (p0 q0 : Id y z) (c : Id p0 q0) (r' : Id y z)
                    (d : Id q0 r') →
                    Id (resptrans (trans a' b) (trans c d))
                    (trans (resptrans a' c) (resptrans b d)))
                 a
                 (λ pq r b →
                    jay
                    (λ pq' r' b' →
                       (p' q' : Id y z) (c : Id p' q') (r0 : Id y z) (d : Id q' r0) →
                       Id (resptrans (trans Refl b') (trans c d))
                       (trans (resptrans Refl c) (resptrans b' d)))
                    b
                    (λ pqr p' q' c →
                       jay
                       (λ p0 q0 c' →
                          (r' : Id y z) (d : Id q0 r') →
                          Id (resptrans Refl (trans c' d))
                          (trans (resptrans Refl c') (resptrans Refl d)))
                       c
                       (λ p'q' r' d →
                          jay
                          (λ p'q0 r0 d' →
                             Id (resptrans Refl (trans Refl d'))
                             (trans Refl (resptrans Refl d')))
                          d (λ _ → Refl))))

module FundamentalAbelian (A : Set) (base : A) where
--  open Paths

  π1El : Set
  π1El = base ≃ base
  π2El : Set
  π2El = _≃_{π1El} Refl Refl 

  _∘_ : π2El → π2El → π2El 
  p ∘ q = trans q p

  _⊙_ : π2El → π2El → π2El 
  a ⊙ b =  resptrans b a

  ⊙-unit-l : (p : π2El) → (Refl ⊙ p) ≃ p
  ⊙-unit-l p = resptrans-unit-r p 

  ⊙-unit-r : (a : π2El) → (a ⊙ Refl) ≃ a
  ⊙-unit-r a = trans (resptrans-unit-left a) (trans-unit-left a) -- because we know the base is Refl, the adjustment cancels

  interchange : (a b c d : _) → ((a ∘ b) ⊙ (c ∘ d)) ≃ ((a ⊙ c)  ∘ (b ⊙ d))
  interchange a b c d = trans-resptrans-ichange  _ _ d _ c _ _ b _ a

  same : (a b : π2El) → (a ∘ b) ≃ (a ⊙ b)
  same a b = (( a         ∘ b)          ≃⟨ resp (λ x → x ∘ b) (sym (⊙-unit-r a))⟩
              ((a ⊙ Refl) ∘ b)          ≃⟨ resp (λ x → (a ⊙ Refl) ∘ x) (sym (⊙-unit-l b)) ⟩
              ((a ⊙ Refl) ∘ (Refl ⊙ b)) ≃⟨ sym (interchange a Refl Refl b) ⟩
              ((a ∘ Refl) ⊙ (Refl ∘ b))  ≃⟨ resp (λ x → x ⊙ (Refl ∘ b)) (trans-unit-left a) ⟩
              (a ⊙ (Refl ∘ b))           ≃⟨ resp (λ x → a ⊙ x) (trans-unit-right b) ⟩
              (a ⊙ b) 
              ∎)

  abelian : (a b : π2El) → (a ∘ b) ≃ (b ∘ a)
  abelian a b = (a ∘ b) ≃⟨ resp (λ x → x ∘ b) (sym (⊙-unit-l a)) ⟩
                   ((Refl ⊙ a) ∘ b)          ≃⟨ resp (λ x → (Refl ⊙ a) ∘ x) (sym (⊙-unit-r b)) ⟩
                   ((Refl ⊙ a) ∘ (b ⊙ Refl)) ≃⟨ interchange refl b a refl ⟩
                   ((Refl ∘ b) ⊙ (a ∘ Refl)) ≃⟨ resp (λ x → x ⊙ (a ∘ Refl)) (trans-unit-right b) ⟩
                   (b         ⊙ (a ∘ Refl)) ≃⟨ resp (λ x → b ⊙ x) (trans-unit-left a) ⟩
                   (b ⊙ a)                   ≃⟨ sym (same b a) ⟩
                   (b ∘ a) 
                   ∎

