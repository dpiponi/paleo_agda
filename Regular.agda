{-# OPTIONS --no-positivity-check #-}
module Regular where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (inj₁ to left; inj₂ to right; map to mapSum)

-- non-dependent product to get nicer-looking types.
record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ 

module Matrices {Ix : Set} {Σ : (Ix -> Set) -> Set} where

  Matrix : Set₁
  Matrix = (i j : Ix) -> Set

  _+_ : Matrix -> Matrix -> Matrix
  m + n = λ i j -> m i j ⊎ n i j
  
  _*_ : Matrix -> Matrix -> Matrix
  m * n = λ i j -> Σ λ k -> m i k × n k j

  data Fix (f : Matrix -> Matrix) (i j : Ix) : Set where
     fix : f (Fix f) i j -> Fix f i j

  open Fix public
open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec

-- finite sums
Σ# : {n : ℕ} -> (Fin n -> Set) -> Set
Σ# {zero} f = ⊥
Σ# {suc zero} f = f zero
Σ# {suc n} f = f zero ⊎ Σ# {n} λ i -> f (suc i)

module Matrices2 where
  module Dummy {n : ℕ} where
    open Matrices {Fin n} {Σ#} public
  open Dummy public

  I : ∀ {n} -> Matrix {n}
  I zero zero = ⊤
  I (suc m) (suc n) = I m n
  I _ _ = ⊥

  ListF : ∀ {n} -> Matrix {n} -> Matrix -> Matrix
  ListF x self = I + (x * self)

  
  K : ∀ {n} -> Vec (Vec Set n) n -> (i j : Fin n) -> Set
  K v i j = lookup j (lookup i v)

  D : Set -> Matrix {2}
  D a = K ((a ∷ ⊤ ∷ [])
        ∷  (⊥ ∷ a ∷ []) ∷ [])

  List : Set -> Set
  List x = Fix (ListF (D x)) zero zero
   
  nil : {a : Set} -> List a
  nil = fix (left _)
  cons : {a : Set} -> a -> List a -> List a
  cons x xs = fix (right (left (x , xs)))
  
  
  open import Data.List renaming (List to L)
  
  iso1 : {A : Set} -> List A -> L A 
  iso1 (fix (left tt)) = []
  iso1 (fix (right (left (x , xs)))) = x ∷ iso1 xs
  iso1 (fix (right (right (_ , xs)))) = ⊥-elim (empty xs)
    where
      empty : {A : Set} -> Fix (ListF (K ((A ∷ ⊤ ∷ []) ∷ (⊥ ∷ A ∷ []) ∷ []))) (suc zero) zero -> ⊥
      empty (fix (left ()))
      empty (fix (right (left (() , _))))
      empty (fix (right (right (x , xs)))) = empty xs




  Pure : Set -> Matrix
  Pure a = K ((a ∷ ⊥ ∷ []) ∷ 
              (⊥ ∷ a ∷ []) ∷ [])
  

-- ((), Fix (S Zero, Zero) (K22 (x, ()) (Void, x)) (I :+: (X :*: Y)))
  x0 = nil {ℕ}
  x1 = cons 1 nil
--  boh : List ℕ
--  boh = fix (right (suc zero , (_ , fix (right (suc zero , (1 , fix {!!}))))))
  
  List' : Set -> Set
  List' x = Fix (ListF (D x)) zero (suc zero)
  empty : List' ℕ
  empty = fix (right (right (_ , fix (left _))))


open Matrices2 public


postulate Rec : Matrix {2}
postulate rec : Matrix {3}

ListI : (A : Set) -> Matrix
ListI a = ListF (D a) Rec

E : Set -> Matrix {3}
E a = K ((a ∷ ⊥ ∷ ⊤ ∷ [])
        ∷ (⊥ ∷ a ∷ ⊥ ∷ [])
        ∷ (⊥ ∷ ⊥ ∷ a ∷ []) ∷ [])



square : ∀ {n} -> Matrix {n} -> Vec (Vec Set n) n
square f = map (λ i -> map (f i) (allFin _)) (allFin _)

z = square (ListF (E ℕ) rec)

table = ((⊤ ⊎ ℕ × Rec zero zero ⊎ ⊤ × Rec (suc zero) zero) ∷ (⊥ ⊎ ℕ × Rec zero (suc zero) ⊎ ⊤ × Rec (suc zero) (suc zero)) ∷ []) ∷
        ((⊥ ⊎ ⊥ × Rec zero zero ⊎ ℕ × Rec (suc zero) zero) ∷ (⊤ ⊎ ⊥ × Rec zero (suc zero) ⊎ ℕ × Rec (suc zero) (suc zero)) ∷ []) ∷ []