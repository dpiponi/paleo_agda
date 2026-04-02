module Geometry where

data Empty : Set where

infix 3 _≡_

data _≡_ {A : Set} : A → A → Set where
   refl : {a : A} → a ≡ a


data coprod (A : Set1) (B : Set1) : Set1 where
    inl : ∀ (a : A) -> coprod A B
    inr : ∀ (b : B) -> coprod A B 

postulate exmid : ∀ (A : Set1) -> coprod A (A -> Empty)

record Congruence : Set₁ where
  field
    Points : Set
    _-_≣_-_ : Points → Points → Points → Points → Set
    reflexivity-≡ : ∀ {x y} → x - y ≣ y - x
    congruence-≡ : ∀ {x y z} → x - y ≣ z - z → x ≡ y
    transitivity-≡ : ∀ { x y z u v w } → x - y ≣ z - u → x - y ≣ v - w → z - u ≣ v - w

record Bewteen : Set₁ where
  field
    Points : Set
    _⟨_⟩_ : Points → Points → Points → Set 
    identity-⟨⟩ : {x y z : Points } → x ⟨ y ⟩ z → x ≡ y
    pasch : {x y z u v : Points} → x ⟨ u ⟩ z → y ⟨ v ⟩ z → ∃ a (u ⟨ a ⟩ y , v ⟨ a ⟩ x )