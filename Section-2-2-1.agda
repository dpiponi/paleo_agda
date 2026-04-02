 module Section-2-2-1 where

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
 
  -- Easier to define this here
  ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
  ap f p = j (λ x y p → f x ≡ f y)
             (λ x → refl)
             p

  lemma-2-2-1 : {A B : Set} → (f : A → B) → {x y : A} → ap {A} {B} f (refl {A} {x}) ≡ refl
  lemma-2-2-1 f = refl

  _⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
  p ⁻¹ = j D d p 
                  where D : (x y : _) → x ≡ y → Set
                        D x y p = y ≡ x
                        d : (x : _) → D x x refl
                        d x = refl

  _■₀_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  p ■₀ q = j (λ x y p → (y ≡ _) → (x ≡ _))
             (λ x → id)
             p q

  _■₁_ : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  p ■₁ q = j (λ y z p → (_ ≡ y) → (_ ≡ z))
             (λ y → id)
             q p

  infixr 14 _■_
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
--  infixr 2 _→⟨_⟩_
--  infix 3 _□

  lemma-2-1-4-i-a : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ (p ■ refl)
  lemma-2-1-4-i-a p = j (λ _ _ p → p ≡ p ■ refl)
                      (λ _ → refl)
                      _
  p≡p■refl = lemma-2-1-4-i-a

  p■refl≡p : {A : Set} → {x y : A} → (p : x ≡ y) → (p ■ refl) ≡ p
  p■refl≡p {A} {x} {y} p = (lemma-2-1-4-i-a {A} {x} {y} p)⁻¹

  lemma-2-1-4-i-b : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ (refl ■ p)
  lemma-2-1-4-i-b p = j (λ _ _ p → p ≡ refl ■ p)
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
  p⁻¹⁻¹≡p = lemma-2-1-4-iii

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

  antihom : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → ((p ■ q)⁻¹) ≡ (q ⁻¹) ■ (p ⁻¹)
  antihom = j₂ (λ x y z p q → ((p ■ q)⁻¹) ≡ (q ⁻¹) ■ (p ⁻¹))
                (λ x → refl)

  Ω² : (A : Set) → (a : A) → Set
  Ω² A a = refl' a ≡ refl' a

  _■r'_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p ■ r) ≡ (q ■ r)
  _■r'_ {A} {a} {b} {c} {p} {q} α r =
             j (λ b c r → {p q : a ≡ b} → (α : p ≡ q) → (p ■ r) ≡ (q ■ r))
               (λ b {p} {q} α → p ■ refl ≡⟨ lemma-2-1-4-i-a p ⁻¹ ⟩
                            p        ≡⟨ α ⟩
                            q        ≡⟨ lemma-2-1-4-i-a q ⟩
                            q ■ refl
                            ▻
               )
               r α


  _■r_ : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p ■ r) ≡ (q ■ r)
  α ■r refl = lemma-2-1-4-i-a _ ⁻¹ ■ α ■ lemma-2-1-4-i-a _
{-
  α ■r r = j (λ b _ r → {a : _} → {p q : a ≡ b} → (α : p ≡ q) → (p ■ r) ≡ (q ■ r))
               (λ _ α → ((lemma-2-1-4-i-a ⁻¹) ■ (α ■ lemma-2-1-4-i-a)))
               r α
-}

  _■l_ : {A : Set} → {a b c : A} → {r s : b ≡ c} → (q : a ≡ b) → (α : r ≡ s) → (q ■ r) ≡ (q ■ s)
  refl ■l α = ((lemma-2-1-4-i-b _ ⁻¹) ■ α) ■ lemma-2-1-4-i-b _
{-
  q ■l α = j (λ _ b q → {c : _} → {r s : b ≡ c} → (α : r ≡ s) → (q ■ r) ≡ (q ■ s))
               (λ _ α → ((lemma-2-1-4-i-b ⁻¹) ■ α) ■ lemma-2-1-4-i-b)
               q α
-}

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

{-
  hor-comm0 : {A : Set} → {a b c : A} → (r : b ≡ c) → (p : a ≡ b)
                  → (refl' p · refl' r) ≡ (refl' p ·' refl' r)
  hor-comm0 refl refl = refl {-j₂ (λ a b c p r → (refl' p · refl' r) ≡ (refl' p ·' refl' r))
                     (λ x → refl)
                     p r-}

  hor-comm1 : {A : Set} → {a b c : A} → {p q : a ≡ b} → {r : b ≡ c} → (α : p ≡ q)
                  → (α · refl' r) ≡ (α ·' refl' r)
  hor-comm1 α = j (λ p q α → (α · refl) ≡ (α ·' refl))
                  (λ p → hor-comm0 _ p)
                  α 

  hor-comm2' : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → {r s : b ≡ c} → (β : r ≡ s)
                  → (α · β) ≡ (α ·' β)
  hor-comm2' α β = j (λ r s β → (α · β) ≡ (α ·' β))
                    (λ r → hor-comm1 α)
                    β
-}

  hor-comm2 : {A : Set} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → {r s : b ≡ c} → (β : r ≡ s)
                  → (α · β) ≡ (α ·' β)
  hor-comm2 {A} {a} {.a} {.a} {refl} {refl} refl {refl} {refl} refl = refl


  u : {A : Set} → {a : A} → refl {A} {a} ≡ refl ■ refl
  u = lemma-2-1-4-i-a refl

  v : {A : Set} → {a : A} → refl {A} {a} ≡ refl ■ refl
  v = lemma-2-1-4-i-b refl

  -- OMG!!!
  eckmann-hilton : {A : Set} → {a : A} → (α β : Ω² A a) →  α ■ β ≡ β ■ α
  eckmann-hilton α β =
                α ■ β
                  ≡⟨ p≡p■refl _ ⟩
                (α ■ β) ■ refl
                  ≡⟨ ■-assoc (α ■ β) v (v ⁻¹)⟩
                ((α ■ β) ■ v) ■ v ⁻¹
                  ≡⟨ ap (λ Q → Q ■ v ⁻¹) (
                      (α ■ β) ■ v
                        ≡⟨ ■-assoc' α β v ⟩
                      (α ■ (β ■ v))
                        ≡⟨ p≡refl■p _ ⟩
                      refl ■ (α ■ (β ■ v))
                        ≡⟨ ■-assoc' u (u ⁻¹) (α ■ (β ■ v)) ⟩
                      u ■ (u ⁻¹ ■ (α ■ (β ■ v))) ≡⟨
                        ap (λ Q → u ■ Q) (
                          u ⁻¹ ■ (α ■ (β ■ v))
                             ≡⟨ ap (λ Q → u ⁻¹ ■ Q) (
                                α ■ (β ■ v) 
                                 ≡⟨ ap (λ Q → (α ■ Q)) (p≡refl■p _) ⟩
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
                             ≡⟨ ap (λ Q → v ⁻¹ ■ (β ■ Q)) (p≡refl■p _ ⁻¹) ⟩
                          v ⁻¹ ■ (β ■ (α ■ u))
                          ▻) ⟩
                      u ■ (v ⁻¹ ■ (β ■ (α ■ u)))
                        ≡⟨ ■-assoc u (v ⁻¹) (β ■ (α ■ u))⟩
                      refl ■ (β ■ (α ■ u))
                        ≡⟨ p≡refl■p _ ⁻¹ ⟩
                      β ■ (α ■ u)
                      ▻ ) 
                  ⟩
                (β ■ (α ■ u)) ■ v ⁻¹
                  ≡⟨ ■-assoc' β (α ■ u) (v ⁻¹) ⟩
                β ■ ((α ■ u) ■ v ⁻¹)
                  ≡⟨ ap (λ Q → β ■ Q) (■-assoc' α u (v ⁻¹)) ⟩
                β ■ (α ■ refl)
                  ≡⟨ ap (λ Q → β ■ Q) (p≡p■refl α ⁻¹)⟩
                β ■ α
                ▻

{-
  eckmann-hilton' : {A : Set} → {a : A} → (α β : Ω² A a) →  α ■ β ≡ β ■ α
  eckmann-hilton' refl refl =
                refl ■ refl
                  ≡⟨ p≡p■refl ⟩
                (refl ■ refl) ■ refl
                  ≡⟨ ■-assoc (refl ■ refl) v (v ⁻¹)⟩
                ((refl ■ refl) ■ v) ■ v ⁻¹
                  ≡⟨ ap (λ Q → Q ■ v ⁻¹) (
                      (refl ■ refl) ■ v
                        ≡⟨ ■-assoc' refl refl v ⟩
                      (refl ■ (refl ■ v))
                        ≡⟨ p≡refl■p ⟩
                      refl ■ (refl ■ (refl ■ v))
                        ≡⟨ ■-assoc' u (u ⁻¹) (refl ■ (refl ■ v)) ⟩
                      u ■ (u ⁻¹ ■ (refl ■ (refl ■ v))) ≡⟨
                        ap (λ Q → u ■ Q) (
                          u ⁻¹ ■ (refl ■ (refl ■ v))
                             ≡⟨ ap (λ Q → u ⁻¹ ■ Q) (
                                refl ■ (refl ■ v) 
                                 ≡⟨ ap (λ Q → (refl ■ Q)) p≡refl■p ⟩
                                (refl ■ ((u ■ v ⁻¹) ■ (refl ■ v)))
                                  ≡⟨ ap (λ Q → (refl ■ Q)) (■-assoc' u (v ⁻¹) (refl ■ v)) ⟩
                                (refl ■ (u ■ (v ⁻¹ ■ (refl ■ v))))
                                  ≡⟨ ap (λ Q → (refl ■ (u ■ Q))) (■-assoc (v ⁻¹) refl v) ⟩
                                (refl ■ (u ■ ((v ⁻¹ ■ refl) ■ v)))
                                  ≡⟨ (■-assoc refl u ((v ⁻¹ ■ refl) ■ v)) ⟩
                                (refl ■ u) ■ ((v ⁻¹ ■ refl) ■ v)
                                ▻
                             ) ⟩
                          u ⁻¹ ■ ((refl ■ u) ■ ((v ⁻¹ ■ refl) ■ v))
                             ≡⟨ ■-assoc (u ⁻¹) ((refl ■ u)) ((v ⁻¹ ■ refl) ■ v) ⟩
                          refl · refl
                             ≡⟨ refl ⟩
                          refl ·' refl
                             ≡⟨ ap (λ Q → Q ■ ((u ⁻¹ ■ (refl ■ u)))) (■-assoc' (v ⁻¹) refl v) ⟩
                          (v ⁻¹ ■ (refl ■ v)) ■ ((u ⁻¹ ■ (refl ■ u)))
                            ≡⟨ (■-assoc (v ⁻¹) (refl ■ v) (u ⁻¹ ■ (refl ■ u)))⁻¹ ⟩
                          v ⁻¹ ■ ((refl ■ v) ■ (u ⁻¹ ■ (refl ■ u)))
                            ≡⟨ ap (λ Q → v ⁻¹ ■ Q) (■-assoc' refl v (u ⁻¹ ■ (refl ■ u)))  ⟩
                          v ⁻¹ ■ (refl ■ (v ■ (u ⁻¹ ■ (refl ■ u))))
                            ≡⟨ ap (λ Q → v ⁻¹ ■ (refl ■ Q)) (■-assoc v (u ⁻¹) (refl ■ u)) ⟩
                          v ⁻¹ ■ (refl ■ (refl ■ (refl ■ u)))
                             ≡⟨ ap (λ Q → v ⁻¹ ■ (refl ■ Q)) (p≡refl■p ⁻¹) ⟩
                          v ⁻¹ ■ (refl ■ (refl ■ u))
                          ▻) ⟩
                      u ■ (v ⁻¹ ■ (refl ■ (refl ■ u)))
                        ≡⟨ ■-assoc u (v ⁻¹) (refl ■ (refl ■ u))⟩
                      refl ■ (refl ■ (refl ■ u))
                        ≡⟨ p≡refl■p ⁻¹ ⟩
                      refl ■ (refl ■ u)
                      ▻ ) 
                  ⟩
                (refl ■ (refl ■ u)) ■ v ⁻¹
                  ≡⟨ ■-assoc' refl (refl ■ u) (v ⁻¹) ⟩
                refl ■ ((refl ■ u) ■ v ⁻¹)
                  ≡⟨ ap (λ Q → refl ■ Q) (■-assoc' refl u (v ⁻¹)) ⟩
                refl ■ (refl ■ refl)
                  ≡⟨ ap (λ Q → refl ■ Q) (p≡p■refl ⁻¹)⟩
                refl ■ refl
                ▻
-}

 open Paths  

