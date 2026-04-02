
module Abelian where

-- identity types that never use K
-- homotopically, Id M N is thought of as a path from M to N
-- we also use M ≃ N and Paths M N as notation for Id M N

module Paths where
 data Id {A : Set} : A -> A -> Set where
   Refl : {a : A} -> Id a a

 _≃_ : {A : Set} -> A -> A -> Set
 _≃_ = Id

 Paths : {A : Set} -> A -> A -> Set

 jay : {A : Set} (C : (x y : A) -> Id x y -> Set)
     -> {M N : A} -> (P : Id M N)
     -> ((x : A) -> C x x Refl)
     -> C M N P

 subst : {A : Set} (p : A -> Set) {x y : A} -> Id x y -> p x -> p y

 resp : {A C : Set} {M N : A} (f : A -> C) -> Id M N -> Id (f M) (f N)

 resp2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> Id M N -> Id M' N' -> Id (f M M') (f N N')

 trans : {A : Set} {M N P : A} -> Id M N -> Id N P -> Id M P

 sym : {a : Set} {x y : a} -> Id x y -> Id y x 

 trans-unit-l : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans Refl p) p

 trans-unit-r : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans p Refl) p

 resptrans : {A : Set} {x y z : A} {p q : Id x y} {p' q' : Id y z} 
           -> Id p q -> Id p' q' -> Id (trans p p') (trans q q') 

 resptrans-unit-r : {A : Set} {x y : A} {p q : Id x y} 
                  -> (a : Id p q) -> Id (resptrans a (Refl{_}{Refl})) a -- definitional equalities work out such that this works unadjusted

 resptrans-unit-l : {A : Set} {x y : A} {p q : Id x y} 
                  -> (a : Id p q) -> Id (resptrans (Refl{_}{Refl}) a) ( (trans (trans-unit-l p) (trans a (sym (trans-unit-l q)))) )


 -- would be a one-liner using pattern matching
 -- nothing about the interchange law depends on talking about loops
 trans-resptrans-ichange : {A : Set} {x y z : A} 
             (p q : Id x y) 
          -> (a : Id p q) (r : Id x y) (b : Id q r) 
             (p' q' : Id y z) (c : Id p' q') 
             (r' : Id y z) (d : Id q' r') 
          -> Id (resptrans (trans a b) (trans c d)) (trans (resptrans a c) (resptrans b d))


 infix  2 _∎
 infixr 2 _≃〈_〉_ 
 
 _≃〈_〉_ : {A : Set} (x : A) {y z : A} → Id x y → Id y z → Id x z

 _∎ : ∀ {A : Set} (x : A) → Id x x


module FundamentalAbelian (A : Set) (base : A) where
  open Paths

  π1El : Set
  π1El = base ≃ base
  π2El : Set
  π2El = _≃_{π1El} Refl Refl 

  _∘_ : π2El → π2El → π2El 

  _⊙_ : π2El → π2El → π2El 

  ⊙-unit-l : (p : π2El) → (Refl ⊙ p) ≃ p

  ⊙-unit-r : (a : π2El) → (a ⊙ Refl) ≃ a


  interchange : (a b c d : _) → ((a ∘ b) ⊙ (c ∘ d)) ≃ ((a ⊙ c)  ∘ (b ⊙ d))

  same : (a b : π2El) → (a ∘ b) ≃ (a ⊙ b)

  abelian : (a b : π2El) → (a ∘ b) ≃ (b ∘ a)
