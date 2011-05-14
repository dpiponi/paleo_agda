{-# OPTIONS --without-K #-}

module Abelian where

module Paths where
 infix 3 _≡_

 data _≡_ {A : Set} : A → A → Set where
   refl : {a : A} → a ≡ a

 Paths : {A : Set} → A → A → Set
 Paths = _≡_

 j : {A : Set} (C : (x y : A) → x ≡ y → Set)
     → {M N : A} → (P : M ≡ N)
     → ((x : A) → C x x refl)
     → C M N P
 j _ refl b = b _

 subst : {A : Set} (p : A → Set) {x y : A} → x ≡ y → p x → p y
 subst C p = j (λ x y _ → C x → C y) p (λ x → λ x' → x')

 trans : {A : Set} {M N P : A} → M ≡ N → N ≡ P → M ≡ P
 trans {A}{M}{N}{P} a b = subst (\ x → M ≡ x) b a

 sym : {a : Set} {x y : a} → x ≡ y → y ≡ x 
 sym p = j (λ x y _ → y ≡ x) p (λ _ → refl)

 infix  2 _∎
 infixr 2 _≡⟨_⟩_ 
 
 _≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
 _ ≡⟨ p1 ⟩ p2 = (trans p1 p2)

 _∎ : ∀ {A : Set} (x : A) → x ≡ x
 _∎ _ = refl

 resp : {A C : Set} {M N : A} (f : A → C) → M ≡ N → f M ≡ f N
 resp {A}{C}{M}{N} f a = subst (\ x → f M ≡ f x) a refl

 resp2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A → B → C) → M ≡ N → M' ≡ N' → f M M' ≡ f N N'
 resp2 {A}{B}{C}{M}{N}{M'}{N'} f a b = 
   subst (λ x → f M M' ≡ f x N') a (subst (λ x → f M M' ≡ f M x) b refl) 

 trans-unit-l : {A : Set} {M N : A} → (p : M ≡ N) → trans refl p ≡ p
 trans-unit-l p = j (λ _ _ p' → trans refl p' ≡ p') p (λ _ → refl)

 trans-unit-r : {A : Set} {M N : A} → (p : M ≡ N) → trans p refl ≡ p
 trans-unit-r p = refl

 resptrans : {A : Set} {x y z : A} {p q : x ≡ y} {p' q' : y ≡ z} 
           → p ≡ q → p' ≡ q' → trans p p' ≡ trans q q'
 resptrans a b = resp2 trans a b 

 resptrans-unit-r : {A : Set} {x y : A} {p q : x ≡ y} 
                  → (a : p ≡ q) → (resptrans a (refl {_} {refl})) ≡ a
 resptrans-unit-r a = j (λ _ _ p → (resptrans p (refl {_} {refl})) ≡ p) a (λ _ → refl)

 resptransrefl : {A : Set} {x y : A} → (p : x ≡ y) (q : x ≡ y) → (a : p ≡ q) → trans refl p ≡ trans refl q 
 resptransrefl p q a = resp (trans refl) a

 resptransrefl' : {A : Set} {x y : A} → (p : x ≡ y) (q : x ≡ y) → (a : p ≡ q) → trans refl p ≡ trans refl q 
 resptransrefl' p q a = trans refl p  ≡⟨ trans-unit-l p ⟩ 
                        p             ≡⟨ a ⟩
                        q             ≡⟨ sym (trans-unit-l q)⟩
                        trans refl q ∎ -- Puts an extra refl at end.
                                       -- Have we proved it doesn't matter?
                                       -- Easy to fix if needed.

 resptrans-unit-l : {A : Set} {x y : A} {p q : x ≡ y} 
                  → (a : p ≡ q) → resptransrefl p q a ≡ resptransrefl' p q a
                                                   
 resptrans-unit-l a = j
                       (λ p' q' a' → resptransrefl p' q' a' ≡ resptransrefl' p' q' a')
                        a
                       (λ x → j (λ _ _ x' → refl ≡ resptransrefl' x' x' refl) x (λ _ → refl))

 trans-resptrans-ichange : {A : Set} {x y z : A} 
             (p q : x ≡ y) 
          → (a : p ≡ q) (r : x ≡ y) (b : q ≡ r) 
             (p' q' : y ≡ z) (c : p' ≡ q') 
             (r' : y ≡ z) (d : q' ≡ r') 
          → resptrans (trans a b) (trans c d) ≡ trans (resptrans a c) (resptrans b d)

 trans-resptrans-ichange {A}{x}{y}{z} p q a = j
                 (λ p' q' a' →
                    (r : x ≡ y) (b : q' ≡ r) (p0 q0 : y ≡ z) (c : p0 ≡ q0) (r' : y ≡ z)
                    (d : q0 ≡ r') →
                    resptrans (trans a' b) (trans c d) ≡ trans (resptrans a' c) (resptrans b d))
                 a
                 (λ pq r b →
                    j
                    (λ pq' r' b' →
                       (p' q' : y ≡ z) (c : p' ≡ q') (r0 : y ≡ z) (d : q' ≡ r0) →
                       resptrans (trans refl b') (trans c d) ≡ trans (resptrans refl c) (resptrans b' d))
                    b
                    (λ pqr p' q' c →
                       j
                       (λ p0 q0 c' →
                          (r' : y ≡ z) (d : q0 ≡ r') →
                          resptrans refl (trans c' d) ≡ trans (resptrans refl c') (resptrans refl d))
                       c
                       (λ p'q' r' d →
                          j
                          (λ p'q0 r0 d' →
                             resptrans refl (trans refl d') ≡ trans refl (resptrans refl d'))
                          d (λ _ → refl))))

module FundamentalAbelian (A : Set) (base : A) where
  open Paths

  π₁El : Set
  π₁El = base ≡ base
  π₂El : Set
  π₂El = _≡_ {π₁El} refl refl 

  _∘_ : π₂El → π₂El → π₂El 
  p ∘ q = trans q p

  _⊙_ : π₂El → π₂El → π₂El 
  a ⊙ b =  resptrans b a

  ⊙-unit-l : (p : π₂El) → (refl ⊙ p) ≡ p
  ⊙-unit-l p = resptrans-unit-r p 

  ⊙-unit-r : (a : π₂El) → (a ⊙ refl) ≡ a
  ⊙-unit-r a = trans (resptrans-unit-l a) (trans-unit-l a)

  interchange : (a b c d : _) → ((a ∘ b) ⊙ (c ∘ d)) ≡ ((a ⊙ c)  ∘ (b ⊙ d))
  interchange a b c d = trans-resptrans-ichange  _ _ d _ c _ _ b _ a

  same : (a b : π₂El) → (a ∘ b) ≡ (a ⊙ b)
  same a b = (( a         ∘ b)           ≡⟨ resp (λ x → x ∘ b) (sym (⊙-unit-r a)) ⟩ 
             ((a ⊙ refl) ∘ b)           ≡⟨ resp (λ x → (a ⊙ refl) ∘ x) (sym (⊙-unit-l b)) ⟩ 
             ((a ⊙ refl) ∘ (refl ⊙ b)) ≡⟨ sym (interchange a refl refl b) ⟩ 
             ((a ∘ refl) ⊙ (refl ∘ b)) ≡⟨ resp (λ x → x ⊙ (refl ∘ b)) (trans-unit-l a) ⟩ 
             (a ⊙ (refl ∘ b))          ≡⟨ resp (λ x → a ⊙ x) (trans-unit-r b) ⟩ 
             (a ⊙ b) ∎)

  abelian : (a b : π₂El) → (a ∘ b) ≡ (b ∘ a)
  abelian a b = (a ∘ b) ≡⟨ resp (λ x → x ∘ b) (sym (⊙-unit-l a)) ⟩ 
                   ((refl ⊙ a) ∘ b)          ≡⟨ resp (λ x → (refl ⊙ a) ∘ x) (sym (⊙-unit-r b)) ⟩ 
                   ((refl ⊙ a) ∘ (b ⊙ refl)) ≡⟨ interchange refl b a refl ⟩ 
                   ((refl ∘ b) ⊙ (a ∘ refl)) ≡⟨ resp (λ x → x ⊙ (a ∘ refl)) (trans-unit-r b) ⟩ 
                   (b         ⊙ (a ∘ refl)) ≡⟨ resp (λ x → b ⊙ x) (trans-unit-l a) ⟩ 
                   (b ⊙ a)                   ≡⟨ sym (same b a) ⟩ 
                   (b ∘ a)  ∎

