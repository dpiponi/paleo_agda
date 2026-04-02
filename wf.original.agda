module wf where

open import Data.Nat hiding (_<_)
--open import Relation.Binary


Rel : Set → Set₁
Rel A = A → A → Set

data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

data Tree (A : Set) : Set where
  tree : (ℕ → Tree A) → Tree A

tfold : {A B : Set} → ((ℕ → B) → B) → Tree A → B
tfold f (tree g) = f (λ i → tfold f (g i))

{-
cons : x -> List x -> List x
nil : List x

foldr : (a -> b -> b) -> b -> [a] -> b
-}

module WF {A : Set} (_<_ : Rel A) where

  data Acc (x : A) : Set where
    acc : (∀ y → y < x → Acc y) → Acc x

  Well-founded : Set
  Well-founded = ∀ x → Acc x

  wfold : {x : A} → (P : A → Set) → (∀ x → (∀ y → y < x → P y) → P x) → Acc x → P x
  wfold P ind-step (acc p) = ind-step _ (λ z q → wfold P ind-step (p z q))

  wfold' : {x : A} → Well-founded → (P : A → Set) → (∀ x → (∀ y → y < x → P y) → P x) → P x
  wfold' p P ind-step = wfold P ind-step (p _)

module temp where
  open WF
  
  <-ℕ-wf : Well-founded _<_
  <-ℕ-wf x = acc (aux x) where
    aux : ∀ x y → y < x → Acc _<_ y
    aux .(suc y) y <-base = <-ℕ-wf y
    aux .(suc x) y (<-step {x} y<x) = aux x y y<x

data Proposition (A : Set ) : Set where
  var : A → Proposition A
  ¬_  : Proposition A → Proposition A
  _∧_ : Proposition A → Proposition A → Proposition A
  _∨_ : Proposition A → Proposition A → Proposition A

data _⊴_ : {A : Set} → Proposition A → Proposition A → Set₁ where
  sub-id : {A : Set} → {p : Proposition A} → p ⊴ p
  sub-¬ : {A : Set} → {p p' : Proposition A} → p ⊴ p' → p ⊴ (¬ p')
  sub-∧₁ : {A : Set} → {p q p' : Proposition A} → p ⊴ p' → p ⊴ (p' ∧ q)
  sub-∧₂ : {A : Set} → {p q q' : Proposition A} → q ⊴ q' → q ⊴ (p ∧ q')
  sub-∨₁ : {A : Set} → {p q p' : Proposition A} → p ⊴ p' → p ⊴ (p' ∨ q)
  sub-∨₂ : {A : Set} → {p q q' : Proposition A} → q ⊴ q' → q ⊴ (p ∨ q')

data _⊲_ : {A : Set} → Proposition A → Proposition A → Set₁ where
  sub-¬ : {A : Set} → {p p' : Proposition A} → p ⊴ p' → p ⊲ (¬ p')
  sub-∧₁ : {A : Set} → {p q p' : Proposition A} → p ⊴ p' → p ⊲ (p' ∧ q)
  sub-∧₂ : {A : Set} → {p q q' : Proposition A} → q ⊴ q' → q ⊲ (p ∧ q')
  sub-∨₁ : {A : Set} → {p q p' : Proposition A} → p ⊴ p' → p ⊲ (p' ∨ q)
  sub-∨₂ : {A : Set} → {p q q' : Proposition A} → q ⊴ q' → q ⊲ (p ∨ q')

xxx : (var 1) ⊲ (var 1 ∧ var 2)
xxx = sub-∧₁ sub-id

