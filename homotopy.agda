{-# OPTIONS --without-K #-}

module homotopy where

infix 3 _≡_

data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

--sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
--sym refl = refl

--trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
--trans refl refl = refl

j : {A : Set} (C : (x y : A) → x ≡ y -> Set)
  → {M N : A} → (P : M ≡ N)
  → ((x : A) → C x x refl)
  → C M N P
j C {M} {.M} refl b = b M

sym : {a : Set} {x y : a} → x ≡ y → y ≡ x 
sym p = j (λ x y _ → y ≡ x) p (λ _ → refl)

subst : {A : Set} (p : A -> Set) {x y : A} -> x ≡ y -> p x -> p y
subst C p = j (λ x y _ → C x → C y) p (λ x → λ x' → x')

trans : {A : Set} {M N P : A} -> M ≡ N -> N ≡ P -> M ≡ P
trans {A}{M}{N}{P} a b = subst (\ x -> M ≡ x) b a

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixl 6 _+_
infixl 8 _×_

_+_ : Nat -> Nat -> Nat
zero + b = b
suc a + b = suc (a + b)

_×_ : Nat -> Nat -> Nat
zero × b = zero
suc a × b = b + (a × b)

a≡a+0 : ∀ {a} -> a ≡ (a + zero)
a≡a+0 {zero}   = refl
a≡a+0 {suc a'} = cong suc a≡a+0

sa+b≡a+sb : ∀ {a b} → (suc a + b) ≡ (a + suc b)
sa+b≡a+sb {zero} {b} = refl
sa+b≡a+sb {suc a} {b} = cong suc (sa+b≡a+sb {a})

comm : ∀ {a b} → (a + b) ≡ (b + a)
comm {zero} {b} = a≡a+0
comm {suc a} {b} = trans (cong suc (comm {a})) (sa+b≡a+sb {b})

a×0≡0 : ∀ {a} → (a × zero) ≡ zero
a×0≡0 {zero} = refl
a×0≡0 {suc a} = cong (_+_ zero) (a×0≡0 {a})

infix  2 _∎
infixr 2 _≃⟨_⟩_ 
 
_≃⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≃⟨ p1 ⟩ p2 = (trans p1 p2)

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_∎ _ = refl

a+1≡sa : {a : Nat} -> (suc zero + a) ≡ suc a
a+1≡sa {a} = (suc zero + a) ≃⟨ refl ⟩ (suc a ∎)

a+2≡sa : {a : Nat} -> (suc (suc zero) + a) ≡ suc (suc a)
a+2≡sa {a} = (suc (suc zero) + a) ≃⟨ refl ⟩ (suc (suc a) ∎)

a+b≣b+a : ∀ {a b} → (a + b) ≡ (b + a)
a+b≣b+a {zero}  {b} = a≡a+0
a+b≣b+a {suc a} {b} = suc a + b ≃⟨ sa+b≡a+sb {a}⟩
                      a + suc b ≃⟨ a+b≣b+a {a}⟩
                      suc b + a ≃⟨ sa+b≡a+sb {b}⟩
                      b + suc a ∎

assoc+ : ∀ {a b c} → (a + (b + c)) ≡ ((a + b) + c)
assoc+ {zero} = refl
assoc+ {suc a} {b} {c} = suc a + (b + c) ≃⟨ sa+b≡a+sb {a} ⟩
                          a + suc (b + c) ≃⟨ refl ⟩
                          a + (suc b + c) ≃⟨ assoc+ {a} {suc b} ⟩
                          (a + suc b) + c ≃⟨ cong (λ x → x + c) (sym (sa+b≡a+sb {a})) ⟩
                          (suc a + b) + c ∎

inter : ∀ {a b c d} → (a + b) + (c + d) ≡ (a + c) + (b + d)
inter {a} {b} {c} {d} = (a + b) + (c + d) ≃⟨ assoc+ {a + b} ⟩
                        ((a + b) + c) + d ≃⟨ cong (λ x → x + d) (sym (assoc+ {a}))⟩
                        a + (b + c) + d ≃⟨ cong (λ x → a + x + d) (comm {b}) ⟩
                        a + (c + b) + d ≃⟨ cong (λ x → x + d) (assoc+ {a})⟩
                        a + c + b + d ≃⟨ sym (assoc+ {a + c})⟩
                        (a + c) + (b + d) ∎

dist : ∀ {a b c} → a × (b + c) ≡ a × b + a × c
dist {zero} = refl
dist {suc a} {b} {c} = suc a × (b + c) ≃⟨ refl ⟩
                       (b + c) + a × (b + c) ≃⟨ cong (λ x → (b + c) + x) (dist {a}) ⟩
                       (b + c) + (a × b + a × c) ≃⟨ inter {b}⟩
                       (b + a × b) + (c + a × c) ≃⟨ refl ⟩
                       (suc a × b) + (suc a × c) ∎

a×sb≡a+a×b : ∀ {a b} → a × suc b ≡ a + a × b
a×sb≡a+a×b {zero} = refl
a×sb≡a+a×b {suc a} {b} = suc a × suc b ≃⟨ refl ⟩
                       suc b + a × suc b ≃⟨ cong (λ x → suc b + x) (a×sb≡a+a×b {a}) ⟩
                       suc b + (a + a × b) ≃⟨ assoc+ {suc b}⟩
                       (suc b + a) + a × b ≃⟨ cong (λ x → x + a × b) (comm {suc b}) ⟩
                       (a + suc b) + a × b ≃⟨ cong (λ x → x + a × b) (sym (sa+b≡a+sb {a})) ⟩
                       (suc a + b) + a × b ≃⟨ sym (assoc+ {suc a})⟩
                       suc a + (b + a × b) ≃⟨ refl ⟩
                       suc a + (suc a × b) ∎

comm× : ∀ {a b} → a × b ≡ b × a
comm× {zero} {b} = zero × b ≃⟨ refl ⟩
                   zero ≃⟨ sym (a×0≡0 {b}) ⟩
                   b × zero ∎

comm× {suc a} {b} = suc a × b ≃⟨ refl ⟩
                    b + a × b ≃⟨ cong (λ x → b + x) (comm× {a}) ⟩
                    b + b × a ≃⟨ sym (a×sb≡a+a×b {b}) ⟩
                    b × suc a ∎

n = suc zero + suc zero

{- suc (suc zero) ≡ suc zero + suc zero -}

{-
C : (x y : A) → x ≡ y → Set
refl : M ≡ N
b : ((x : A) → C x x refl)

b _ : C M N P
C x x refl = C M N P
M : A
-}

subst' : {A : Set} (p : A → Set) {x y : A} -> x ≡ y -> p x → p y
subst' p proof = j (λ x y _ → (p x → p y)) proof (λ x → λ y → y) 

--trans' : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
--trans' {A} {x} {y} {z} x≡y = j (λ x y _ → y ≡ z → x ≡ z) x≡y (λ z → λ x → x)

sym' : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym' {A} {x} {y} x≡y = j (λ x y _ → y ≡ x) x≡y (λ z → refl)

-- refl is unit proof on left
trans-unit-left : {A : Set} {M N : A} -> (p : M ≡ N) -> trans refl p ≡ p
trans-unit-left q = j (λ x y p → trans refl p ≡ p) q (λ x → refl)

trans-unit-right : {A : Set} {m n : A} → (p : m ≡ n) → trans p refl ≡ p
trans-unit-right q = j (λ x y p → trans p refl ≡ p) q (λ x → refl)

lemma : {A : Set} {x y z : A} (p : x ≡ y) {p' q' : y ≡ z} 
           -> p' ≡ q' -> trans p p' ≡ trans p q'
lemma p proof = j (λ p' q' z → trans p p' ≡ trans p q') proof (λ x → refl)

resp : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
resp f proof = j (λ x y _ → f x ≡ f y) proof (λ x → refl)

lemma2 : {A B C : Set} -> {x x' : A} → (w : B) → (f : A → B -> C) → x ≡ x' → f x w ≡ f x' w
lemma2 w f proofx = resp (λ z → f z w) proofx

resp2 : {A B C : Set} -> {x x' : A} -> {y y' : B} → (f : A → B -> C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
resp2 {A} {B} {C} {x} {x'} {y} {y'} f proofx proofy =
  j (λ y y' p → f x y ≡ f x' y') proofy (\z → lemma2 z f proofx)

-- composing proofs respects equality
resptrans : {A : Set} {x y z : A} {p q : x ≡ y} {p' q' : y ≡ z} 
           -> p ≡ q -> p' ≡ q' -> trans p p' ≡ trans q q'
{-
resptrans {A} {x} {y} {z} {p} {q} {p'} {q'} proof1 proof2 =
  j (λ p q z → trans p p' ≡ trans q q') proof1 (λ x → lemma x proof2)
-}
resptrans a b = resp2 trans a b 
{-

a : p ≡ q      refl : refl ≣ refl

gives

(a' : trans p refl ≣ trans q refl) ≡ a
-}
{-
resptrans-unit-r : {A : Set} {x y : A} {p q : x ≡ y} 
                  → (a : p ≡ q) → resptrans a (refl {_} {refl}) ≡ a
resptrans-unit-r proofp≡q = j (λ _ _ r → resptrans r (refl {_} {refl}) ≡ r) proofp≡q (λ _ → refl)
-}

resptrans-unit-r : {A : Set} {x y : A} {p q : x ≡ y} 
                  → (a : p ≡ q) → (resptrans a (refl{_}{refl})) ≡ a
resptrans-unit-r a = j (λ _ _ p → (resptrans p (refl {_} {refl})) ≡ p) a (λ _ → refl)



{-
resptrans-unit-l a = j {_}
                        (λ p' q' a' →
                           (resp (trans refl) a') ≡
                           (trans (trans-unit-left p') (trans a' (sym (trans-unit-left q')))))
                        {_} {_} a
                        (λ x →
                           j
                           (λ xend _ x' →
                              refl ≡
                              (subst (_≡_ (subst (_≡_ xend) x' refl))
                               (subst (_≡_ x')
                                (j (λ x0 y _ → y ≡ x0)
                                 (j (λ _ _ p' → (subst (_≡_ _) p' refl) ≡ p') x' (λ _ → refl))
                                 (λ _ → refl))
                                refl)
                               (j (λ _ _ p' → (subst (_≡_ _) p' refl) ≡ p') x' (λ _ → refl))))
                           x (λ _ → refl))
-}

{-
resptrans-unit-l a = j {_}
                        (λ p' q' a' →
                           (resp (trans refl) a') ≡
                           (trans (trans-unit-left p') (trans a' (sym (trans-unit-left q')))))
                        {_} {_} a
                        (λ x →
                           j
                           (λ xend _ x' →
                              refl ≡
                              (trans

                               (j (λ _ _ p' → trans refl p' ≡ p') x' (λ _ → refl))

                               (trans refl
                                (j (λ x0 y _ → y ≡ x0)
                                 (j (λ _ _ p' → trans refl p' ≡ p') x' (λ _ → refl))
                                 (λ _ → refl)))

                              ))
                           x (λ _ → refl))
-}

{-
x y : A
p : x ≡ y
q : x ≡ y
a : p ≡ q
resptrans : {A : Set} {x y z : A} {ppp qqqq : x ≡ y} {p q : y ≡ z} 
           -> xxx ≡ xxx -> p' ≡ q' -> trans p p' ≡ trans q q'
resptrans (refl {_} {refl} : xxx ≡ xxx) (a : p ≡ q) : trans xxx p ≡ trans xxx q

trans-unit-left : {A : Set} {x y : A} -> (p : x ≡ y) -> trans refl p ≡ p 
trans-unit-left p : trans refl p ≡ p

trans a (trans (sym (trans-unit-left q) : q ≡ trans refl q) refl)
trans a (trans (sym (trans-unit-left q) : q ≡ trans refl q) (trans refl q ∎))

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_∎ _ = refl

resptrans : {A : Set} {x y z : A} {p q : x ≡ y} {p' q' : y ≡ z} 
           -> p ≡ q -> p' ≡ q' -> trans p p' ≡ trans q q'

-}
resptrans-unit-l : {A : Set} {x y : A} {p q : x ≡ y} 
                  -> (a : p ≡ q) -> (resptrans (refl {_} {refl}) a) ≡
                                                (trans refl p ≃⟨ trans-unit-left p ⟩
                                                 p            ≃⟨ a ⟩
                                                 q            ≃⟨ sym (trans-unit-left q)⟩
                                                 trans refl q ∎)
                                                   

resptrans-unit-l a = j {_}
                        (λ p' q' a' →
                           (resp (trans refl) a') ≡
                                                  (trans refl p' ≃⟨ trans-unit-left p' ⟩ 
                                                   p'            ≃⟨ a' ⟩
                                                   q'            ≃⟨ sym (trans-unit-left q')⟩
                                                   trans refl q' ∎)
                                                                )
                        {_} {_} a
                        (λ x →
                           j
                           (λ xend _ x' →
                              refl ≡
                              (trans
                                     (trans-unit-left x')
                                     (trans refl
--                                            (trans (sym (trans-unit-left x')) refl)
                                            (trans (sym (trans-unit-left x')) refl)
                                     )

                              )
                           )
                           x (λ _ → refl))

{-
trans-unit-left : {A : Set} {M N : A} -> (p : M ≡ N) -> trans refl p ≡ p
trans-unit-left q = j (λ x y p → trans refl p ≡ p) q (λ x → refl)

λ x' → j (λ u v p' → (subst (_≡_ _) p' refl) ≡ p') x' (λ _ → refl)

subst (_≡_ _) (p' : u ≡ v) (refl : _ ≡ u) : (_ ≡ v)

-}

{- (refl : _ ≡ u) → _ ≡ v -}

{-
trans : {A : Set} {M N P : A} -> M ≡ N -> N ≡ P -> M ≡ P
trans {A}{M}{N}{P} a b = subst (_≡_ M) b a
-}
