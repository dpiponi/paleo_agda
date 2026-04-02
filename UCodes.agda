module UCodes where

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