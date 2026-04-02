--
--{-# OPTIONS --universe-polymorphism #-}

module wf where

open import Data.Nat hiding (_<_)
open import Level
open import Relation.Binary
open import Data.List
open import Data.List.Any

--Rel : Set → Set₂
--Rel A = A → A → Set₁

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

module WF {A : Set} (_<_ : Rel A (suc zero)) where

  data Acc (x : A) : Set₁ where
    acc : (∀ y → y < x → Acc y) → Acc x

  Well-founded : Set₁
  Well-founded = ∀ x → Acc x

{-
  wfold : {x : A} → (P : A → Set) → (∀ x → (∀ y → y < x → P y) → P x) → Acc x → P x
  wfold P ind-step (acc p) = ind-step _ (λ z q → wfold P ind-step (p z q))

  wfold' : {x : A} → Well-founded → (P : A → Set) → (∀ x → (∀ y → y < x → P y) → P x) → P x
  wfold' p P ind-step = wfold P ind-step (p _)
-}

{-
module temp where
  open WF
  
  <-ℕ-wf : Well-founded _<_
  <-ℕ-wf x = acc (aux x) where
    aux : ∀ x y → y < x → Acc _<_ y
    aux .(suc y) y <-base = <-ℕ-wf y
    aux .(suc x) y (<-step {x} y<x) = aux x y y<x
-}

data Proposition (A : Set ) : Set where
  var : A → Proposition A
  ¬_  : Proposition A → Proposition A
  _∧_ : Proposition A → Proposition A → Proposition A
  _∨_ : Proposition A → Proposition A → Proposition A

data _⊲_ : {A : Set} → Proposition A → Proposition A → Set₁ where
  sub-¬ : {A : Set} → {p p'    : Proposition A} → p ⊲ p' → p ⊲ (¬ p')
  seq-¬ : {A : Set} → {p       : Proposition A}          → p ⊲ (¬ p)
  sub-∧₁ : {A : Set} → {p q p' : Proposition A} → p ⊲ p' → p ⊲ (p' ∧ q)
  seq-∧₁ : {A : Set} → {p q    : Proposition A}          → p ⊲ (p  ∧ q)
  sub-∧₂ : {A : Set} → {p q q' : Proposition A} → q ⊲ q' → q ⊲ (p ∧ q')
  seq-∧₂ : {A : Set} → {p q    : Proposition A}           → q ⊲ (p ∧ q)
  sub-∨₁ : {A : Set} → {p q p' : Proposition A} → p ⊲ p' → p ⊲ (p' ∨ q)
  seq-∨₁ : {A : Set} → {p q    : Proposition A}           → p ⊲ (p ∨ q)
  sub-∨₂ : {A : Set} → {p q q' : Proposition A} → q ⊲ q' → q ⊲ (p ∨ q')
  seq-∨₂ : {A : Set} → {p q    : Proposition A}           → q ⊲ (p ∨ q)

xxx : (var 1) ⊲ (var 1 ∧ var 2)
xxx = seq-∧₁

open WF

wf-⊲ : Well-founded {Proposition ℕ} _⊲_
wf-⊲ x = acc (aux x) where
      aux : ∀ (x y : Proposition ℕ) → y ⊲ x → Acc {Proposition ℕ} _⊲_ y
      aux .(¬ p') y (sub-¬ {.ℕ} {.y} {p'} y') = aux p' y y'
      aux .(¬ y) y seq-¬ = wf-⊲ y
      aux .(p' ∧ q) y (sub-∧₁ {.ℕ} {.y} {q} {p'} y') = aux p' y y'
      aux .(y ∧ q) y (seq-∧₁ {.ℕ} {.y} {q}) = wf-⊲ y
      aux .(p ∧ q') y (sub-∧₂ {.ℕ} {p} {.y} {q'} y') = aux q' y y'
      aux .(p ∧ y) y (seq-∧₂ {.ℕ} {p}) = wf-⊲ y
      aux .(p' ∨ q) y (sub-∨₁ {.ℕ} {.y} {q} {p'} y') = aux p' y y'
      aux .(y ∨ q) y (seq-∨₁ {.ℕ} {.y} {q}) = wf-⊲ y
      aux .(p ∨ q') y (sub-∨₂ {.ℕ} {p} {.y} {q'} y') = aux q' y y'
      aux .(p ∨ y) y (seq-∨₂ {.ℕ} {p}) = wf-⊲ y

open Membership-≡

data Closes : {A : Set} → List A → List A → Proposition A → Set₁ where
  var-closes : {A : Set} → (a : A) → (ayes : List A) → (noes : List A) → a ∈ noes → Closes {A} ayes noes (var a)
  nvar-closes : {A : Set} → (a : A) → (ayes : List A) → (noes : List A) → a ∈ ayes → Closes {A} ayes noes (var a)
  doesn't : {A : Set} → (ayes : List A) → 
  
yyy : Closes [] (0 ∷ []) (var 0)
yyy = var-closes 0 [] (0 ∷ []) (here _≡_.refl)

zzz : Closes [] (0 ∷ 1 ∷ []) (var 1)
zzz = var-closes 1 [] (0 ∷ 1 ∷ []) (there (here _≡_.refl))

closes? : {A : Set} → Proposition A → 