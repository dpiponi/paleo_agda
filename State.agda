module State where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit

data Desc : Set1 where
  0# 1# : Desc
  Id : Desc
  _+_ _*_ : (D1 D2 : Desc) -> Desc
  K : Set -> Desc

[_] : Desc -> Set -> Set
[ 0# ] X = ⊥
[ 1# ] X = ⊤
[ Id ] X = X
[ D1 + D2 ] X = [ D1 ] X ⊎ [ D2 ] X
[ D1 * D2 ] X = [ D1 ] X × [ D2 ] X
[ K S ] X = S

open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec

-- finite sums
Σ# : {n : ℕ} -> (Fin n -> Set) -> Set
Σ# {zero} f = ⊥
Σ# {suc zero} f = f zero
Σ# {suc n} f = f zero ⊎ Σ# {n} λ i -> f (suc i)

module Matrices {Ix : Set} {Σ : (Ix -> Set) -> Set} where

  Matrix : Set₁
  Matrix = (i j : Ix) -> Set

  _+m_ : Matrix -> Matrix -> Matrix
  m +m n = λ i j -> m i j ⊎ n i j
  
  _*m_ : Matrix -> Matrix -> Matrix
  m *m n = λ i j -> Σ λ k -> m i k × n k j

module Dimension {n : ℕ} where
  open Matrices {Fin n} {Σ#} public
open Dimension public
  
0m : ∀ {n} → Matrix {n}
0m _ _ = ⊥

I : ∀ {n} -> Matrix {n}
I zero zero = ⊤
I (suc m) (suc n) = I m n
I _ _ = ⊥

X : ∀ {n} → Matrix {n}
X _ _ = ℕ

k : ∀ {n} -> Vec (Vec Set n) n -> (i j : Fin n) -> Set
k v i j = lookup j (lookup i v)

⟨_⟩ : ∀ {n} → Desc → Matrix {n}
⟨ 0# ⟩ = 0m
⟨ 1# ⟩ = I
⟨ Id ⟩ = X
⟨ a + b ⟩ = ⟨ a ⟩ +m ⟨ b ⟩
⟨ a * b ⟩ = ⟨ a ⟩ *m ⟨ b ⟩
⟨ K x ⟩ = k x

{-  
data Mu (D : Desc) : Set where
  <_> : [ D ] (Mu D) -> Mu D
  
  
ListD : Set -> Desc
ListD A = 1# + (K A * Id) 

List : Set -> Set
List A = Mu (ListD A)

nil : ∀ {A} -> List A
nil = < inj₁ _ >

cons : ∀ {A} -> A -> List A -> List A
cons x xs = < inj₂ (x , xs) >
-}