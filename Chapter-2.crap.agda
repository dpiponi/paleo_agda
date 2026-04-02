{-# OPTIONS --without-K --type-in-type #-}

module Chapter-2 where

 import Section-2-2-1
 open Section-2-2-1
 open Paths

 import Section-2-2-2
 open Section-2-2-2

 import Section-2-2-3
 open Section-2-2-3

 import Section-2-2-4
 open Section-2-2-4

 module 2-6 {A B : Set} where

  -- 2.6.1
  ipair : {x : A × B} → {y : A × B} → x ≡ y → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
  ipair p = (ap pr₁ p , ap pr₂ p)

  pair' : (a : A) → {b b' : B} → b ≡ b' → (a , b) ≡ (a , b')
  pair' a refl = refl

 -- 2.6.3
  pair : {a a' : A} → {b b' : B} → (a ≡ a') × (b ≡ b') → (a , b) ≡ (a' , b')
  pair (refl , refl) = refl

  rec∑ : {A B C : Set} → (A → B → C) → (x : A × B) → C
  rec∑ f (a , b) = f a b

  ind∑ : {A : Set} {B : A → Set} → (C : (∑ A B) → Set) → ((a : A) → (b : B a) → C (a , b))
                                 → (p : ∑ A B) → C p
  ind∑ C g (a , b) = g a b

  -- Lifts equalities at component level to equality at pair level
  module 2-6-2 where
    pair= : {x y : A × B} → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → x ≡ y
    pair= {a , b} {a' , b'} = pair {a} {a'} {b} {b'}

  h : {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ipair r) ≡ r
  h = j prop
      (ind∑ (λ x → prop x x refl) (λ a b → refl))
      where
        prop : (x : A × B) → (y : A × B) → (x ≡ y) → Set
        prop = ind∑ _ (λ a b →
               ind∑ _ (λ a' b' →
                 λ r → pair (ipair r) ≡ r))

{-
  h4 : {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ipair r) ≡ r
  h4 = j prop
      (ind∑ (λ x → prop x x refl) (λ a b → refl))
      where
        prop : (x : A × B) → (y : A × B) → (x ≡ y) → Set
        prop  = ind∑ {!!} (λ a b →
               ind∑ {!!} (λ a' b' →
                 λ r → pair (ipair r) ≡ r)) 

  h5 : {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ipair r) ≡ r
  h5 {a} {a'} {b} {b'}  = j (ind∑ {!!} (λ a b →
               ind∑ {!!} (λ a' b' →
                 λ r → pair (ipair r) ≡ r)))
      (ind∑ (λ x → (ind∑ {!!} (λ a b →
               ind∑ {!!} (λ a' b' →
                 λ r → pair (ipair r) ≡ r))) x x refl) (λ a b → refl))

  h''' : (x x' : A × B) → (r : (pr₁ x , pr₂ x) ≡ (pr₁ x' , pr₂ x')) → pair (ipair r) ≡ r
  h''' x x' r = {!!}

  h'' : {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ap pr₁ r , ap pr₂ r) ≡ r
  h'' {a} {a'} {b} {b'} r = h''' (a , b) (a' , b') r

  h' : {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ipair r) ≡ r
  h' = h''
-}


  k : {x y : A × B} → (s : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)) → ipair (pair s) ≡ s
  k {x} {y} =
                   ind∑ (λ x → (y : A × B) → (s : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
                             → ipair (pair s) ≡ s) (λ a b →                           -- on x
                   ind∑ _ (λ a' b' →                                                  -- on y
                   ind∑ _ (λ p q →                                                    -- on s
                   j (λ a a' p → (b b' : B) → (q : b ≡ b')
                               → ipair (pair (p , q)) ≡ (p , q)) (λ a b b' q →        -- on q
                   j (λ b b' q → (a : A)
                               → ipair (pair (refl {A} {a} , q)) ≡ refl , q) (λ x a → -- on p
                   refl) q a) p b b' q))) x y

  theorem-2-6-2 : {x : A × B} → {y : A × B} → isequiv (ipair {x} {y})
  theorem-2-6-2 {(a , b)} {(a' , b')} = qinv-to-isequiv (ipair {a , b} {a' , b'})
                                                                (pair , ( k {a , b} {a' , b'}, h ))

  prop-uniq-pair : {x y : A × B} → {r : x ≡ y} → r ≡ 2-6-2.pair= (ap pr₁ r , ap pr₂ r)
  prop-uniq-pair {a , b} {a' , b'} {r} = (h r)⁻¹

  refl× : {z : A × B} → refl {A × B} {z} ≡ 2-6-2.pair= (refl {A} {pr₁ z} , refl {B} {pr₂ z})
  refl× {z} = refl {_} {z} ≡⟨ prop-uniq-pair ⟩
                      2-6-2.pair= (ap pr₁ (refl {_} {z}), ap pr₂ (refl {_} {z}))
                                           ≡⟨ ap₂ (λ P Q → 2-6-2.pair= (P , Q)) refl refl ⟩
                      2-6-2.pair= (refl , refl)
                      ▻

  ×⁻¹ : {x y : A × B} (p : x ≡ y) → p ⁻¹ ≡ 2-6-2.pair= ((ap pr₁ p)⁻¹ , (ap pr₂ p)⁻¹)
  ×⁻¹ {x} {.x} refl = refl×

  ×■ : {x y z : A × B} (p : x ≡ y) (q : y ≡ z) → p ■ q ≡ 2-6-2.pair= (ap pr₁ p ■ ap pr₁ q , ap pr₂ p ■ ap pr₂ q)
  ×■ {x} {.x} {.x} refl refl = refl ■ refl ≡⟨ prop-uniq-pair ⟩
                     2-6-2.pair= (ap pr₁ {x} (refl ■ refl) , ap pr₂ {x} (refl ■ refl))
                                         ≡⟨ ap₂ (λ P Q → 2-6-2.pair= (P , Q))
                                                (lemma-2-2-2-i pr₁ {x} refl {refl})
                                                (lemma-2-2-2-i pr₂ {x} refl {refl}) ⟩
                     2-6-2.pair= (ap pr₁ {x} refl ■ ap pr₁ {x} refl , ap pr₂ {x} refl ■ ap pr₂ {x} refl)
                     ▻

{-
  ×■ : {x y z : A × B} (p : x ≡ y) (q : y ≡ z) → p ■ q ≡ 2-6-2.pair= (ap pr₁ p ■ ap pr₁ q , ap pr₂ p ■ ap pr₂ q)
  ×■ p q = j₂ (λ x y z p q → p ■ q ≡ 2-6-2.pair= (ap pr₁ p ■ ap pr₁ q , ap pr₂ p ■ ap pr₂ q))
              (λ x → refl ■ refl ≡⟨ prop-uniq-pair ⟩
                     2-6-2.pair= (ap pr₁ {x} (refl ■ refl) , ap pr₂ {x} (refl ■ refl))
                                         ≡⟨ ap₂ (λ P Q → 2-6-2.pair= (P , Q))
                                                (lemma-2-2-2-i pr₁ {x} refl {refl})
                                                (lemma-2-2-2-i pr₂ {x} refl {refl}) ⟩
                     2-6-2.pair= (ap pr₁ {x} refl ■ ap pr₁ {x} refl , ap pr₂ {x} refl ■ ap pr₂ {x} refl)
                     ▻)
                     p q
-}

 open 2-6

 -- These theorems use a slightly different context to earlier parts of chapter
 -- so not in module.
 uppt : {A B : Set} → (x : A × B) → (pr₁ x , pr₂ x) ≡ x
 uppt (a , b) = refl

 theorem-2-6-4 : {Z : Set} → {A B : Z → Set} → {w z : Z} → (p : z ≡ w) → (x : A z × B z) →
                          transport (λ z → A z × B z) p x ≡ (transport A p (pr₁ x) , transport B p (pr₂ x))
 theorem-2-6-4 refl x = (uppt x)⁻¹
        

 module 2-6-5 {A B A' B' : Set} where

  private f : (g : A → A') → (h : B → B') → (A × B) → (A' × B')
  f g h x = (g (pr₁ x), h (pr₂ x))

  theorem-2-6-5 : (g : A → A') → (h : B → B') → (x y : A × B) → (p : pr₁ x ≡ pr₁ y) → (q : pr₂ x ≡ pr₂ y)
                  → ap (f g h) (2-6-2.pair= {A} {B} {x} {y} (p , q))
                       ≡ 2-6-2.pair= {_} {_} {f g h x} {f g h y} (ap g p , ap h q)
  theorem-2-6-5 g h (a , b) (a' , b') p q =
           j (λ a a' p → ap (f g h) (2-6-2.pair= {_} {_} {(_ , _)} {(_ , _)} (p , q))
                           ≡ 2-6-2.pair= (ap g p , ap h q))
             (λ a → j (λ b b' q → ap (f g h) (2-6-2.pair= {_} {_} {_ , _} {_ , _} (refl , q))
                                    ≡ 2-6-2.pair= (refl , ap h q))
                      (λ b → refl)
                      q)
             p

 open 2-6-5

 module 2-7 {A : Set} {P : A → Set} where

  module 2-7-2 where

   comp : {w w' : ∑ A P} → (w ≡ w') → ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')
   comp refl = refl , refl

   pair= : {w w' : ∑ A P}
                 → ∑ (pr₁ w ≡ pr₁ w') (λ p → (p ∗)(pr₂ w) ≡ pr₂ w') → (w ≡ w')

   pair= {_ , _} {_ , _} (p , q) =
         j (λ w₁ w₁' p → {w₂ : P w₁} →  {w₂' : P w₁'} → ((p ∗) w₂ ≡ w₂') → (w₁ , w₂) ≡ (w₁' , w₂'))
           (λ w₁ q → ap (λ Q → (w₁ , Q)) q) -- tiny mod from book
           p q 

{-
   comp○pair≡id : {w w' : ∑ A P}
                   → (r : ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w'))
                   → comp {w} {w'} (pair= r) ≡ r
   comp○pair≡id {w₁ , w₂} {w₁' , w₂'} (p , q) =
                   j (λ w₁ w₁' p → (w₂ : P w₁) →  (w₂' : P w₁') → (q : (p ∗) w₂ ≡ w₂')
                        → comp {w₁ , w₂} {w₁' , w₂'} (pair= (p , q)) ≡ (p , q))
                     (λ w₁ w₂ w₂' q → j (λ _ _ q → comp {_ , _} {_ , _} (pair= (refl , q)) ≡ (refl , q))
                                        (λ x → refl)
                                        q)
                     p w₂ w₂' q 
-}

   comp○pair≡id : {w w' : ∑ A P}
                   → (r : ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w'))
                   → comp {w} {w'} (pair= r) ≡ r
   comp○pair≡id {w₁ , w₂} {.w₁ , .w₂} (refl , refl) = refl

   private gf≡id : {w w' : ∑ A P} → (p : w ≡ w') → pair= (comp p) ≡ p
           gf≡id {w} refl with w
           ... | (a , b) = refl

   private qinv-f : {w w' : ∑ A P} → qinv (comp {w} {w'})
           qinv-f {w} {w'} = (pair= , (comp○pair≡id {w} {w'} , gf≡id))

   theorem-2-7-2 :  {w w' : ∑ A P}
                   → (w ≡ w') ≃ ∑ (pr₁ w ≡ pr₁ w') (λ p → transport P p (pr₂ w) ≡ pr₂ w')
   theorem-2-7-2 = ( comp , qinv-to-isequiv comp qinv-f )

  theorem-2-7-2 = 2-7-2.theorem-2-7-2
  open 2-7-2

  corollary-2-7-3 : (z : ∑ A P) → z ≡ (pr₁ z , pr₂ z)
  corollary-2-7-3 z = 2-7-2.pair= (refl , refl)

  module 2-7-4 {Q : (∑ A P) → Set} where

    private R = λ x → ∑ (P x) (λ u → Q (x , u))

    theorem-2-7-4 : {x y : A} → (p : x ≡ y) → (u : P x) → (z : Q (x , u))
                  → (transport R p) (u , z) ≡ ((p ∗) u , transport Q (2-7-2.pair= (p , refl {P y} {(p ∗) u})) z)
    theorem-2-7-4 p = j (λ x y p → (u : P x) → (z : Q (x , u))
                  → (transport R p) (u , z) ≡ ((p ∗) u , transport Q (2-7-2.pair= (p , refl {P y} {(p ∗) u})) z))
                                (λ _ _ _ → refl)
                                p

  open 2-7-4
 open 2-7

 data unit : Set where
   ⋆ : unit

 module 2-8-1 where

   private f : (x y : unit) → (x ≡ y) → unit
   f x y _ = ⋆

   private g : (x y : unit) → unit → (x ≡ y)
   g ⋆ ⋆ ⋆ = refl

   private fg≡id : (x y : unit) → (r : unit) → f x y (g x y r) ≡ r
   fg≡id x y ⋆ = refl

   ind⋆ : (C : unit → Set) → (x : unit) → C ⋆ → C x
   ind⋆ _ ⋆ z = z

   private gf≡id : (x y : unit) → (r : x ≡ y) → g x y (f x y r) ≡ r
   gf≡id x y r = j (λ x y r → g x y (f x y r) ≡ r)
                   (λ x → ind⋆ (λ x → g x x (f x x refl) ≡ refl) x refl)
                   r

   theorem-2-8-1 : (x y : unit) → (x ≡ y) ≃ unit
   theorem-2-8-1 x y = (f x y , qinv-to-isequiv (f x y) (g x y , (fg≡id x y , gf≡id x y)))

 module 2-9 {A : Set} {B : A → Set} where

   happly : {f g : ((x : A) → B x)} → (f ≡ g) → (x : A) → f x ≡ g x
   happly {f} {g} r = j (λ f g r → (x : A) → f x ≡ g x)
                    (λ f r → refl)
                    r

   postulate axiom-2-9-3 : {f g : ((x : A) → B x)} → isequiv (happly {f} {g})

   funext : {f g : ((x : A) → B x)} → ((x : A) → f x ≡ g x) → f ≡ g
   funext = pr₁ (isequiv-to-qinv happly axiom-2-9-3)

   computation : {f g : ((x : A) → B x)} → (r : (x : A) → f x ≡ g x) → happly (funext r) ≡ r
   computation = pr₁ (pr₂ (isequiv-to-qinv happly axiom-2-9-3))

   uniqueness : {f g : ((x : A) → B x)} → (r : f ≡ g) → funext (happly r) ≡ r
   uniqueness = pr₂ (pr₂ (isequiv-to-qinv happly axiom-2-9-3))

   refl∏ : (f : ((x : A) → B x)) → refl {_} {f} ≡ funext (λ x → refl {_} {f x})
   refl∏ f = refl {_} {f}                   ≡⟨ (uniqueness refl)⁻¹ ⟩
             funext (happly (refl {_} {f})) ≡⟨ ap (λ Q → funext Q) refl ⟩        
             funext (λ x → refl {_} {f x})
             ▻

   ∏⁻¹ : {f g : ((x : A) → B x)} → (α : f ≡ g) → α ⁻¹ ≡ funext (λ x → (happly α x)⁻¹)
   ∏⁻¹ = j (λ f g α → α ⁻¹ ≡ funext (λ x → (happly α x)⁻¹))
             (λ f → (refl {_} {f})⁻¹  ≡⟨ (uniqueness refl)⁻¹ ⟩
                    funext (happly ((refl {_} {f}) ⁻¹)) ≡⟨ ap funext refl ⟩
                    funext (λ x → (happly (refl {(x₁ : A) → B x₁} {f}) x) ⁻¹)
                    ▻)
 
   ∏■ : {f g h : ((x : A) → B x)} → (α : f ≡ g) → (β : g ≡ h) → (α ■ β) ≡ funext (λ x → happly α x ■ happly β x)
   ∏■ = j₂ (λ f g h α β → (α ■ β) ≡ funext (λ x → happly α x ■ happly β x))
           (λ f → (refl {_} {f} ■ refl {_} {f}) ≡⟨ refl ⟩
                  refl {_} {f} ≡⟨ (uniqueness refl)⁻¹ ⟩
                  funext (happly (refl {_} {f})) ≡⟨ ap funext refl ⟩
                  funext (λ x → happly (refl {_} {f}) x ■ happly (refl {_} {f}) x)
                  ▻)

 open 2-9

 module theorem-2-9-4 {X : Set} {A B : X → Set} where

   A→B = λ x → A x → B x

   theorem-2-9-4 : {x₁ x₂ : X} → (p : x₁ ≡ x₂) →  (f : A x₁ → B x₁)
                   → transport A→B p f ≡ λ z → transport B p (f (transport A (p ⁻¹) z))
   theorem-2-9-4 = j (λ x₁ x₂ p → (f : A x₁ → B x₁)
                       → transport A→B p f ≡ λ z → transport B p (f (transport A (p ⁻¹) z)))
                    (λ x f → refl)

 open theorem-2-9-4

 module theorem-2-9-5 {X : Set} {A : X → Set} {B : (x : X) → A x → Set} where

   Π : X → Set
   Π = λ x → (a : A x) → B x a

   B^ : (∑ X A) → Set
   B^ = λ w → B (pr₁ w) (pr₂ w)

   theorem-2-9-5 : {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (f : (a : A x₁) → B x₁ a) → (a : A x₂) →
                   transport Π p f a ≡
                   transport B^ 
                             ((2-7-2.pair= {_} {_} {_ , _} {_ , _} ((p ⁻¹) , refl {_} {transport A (p ⁻¹) a}))⁻¹)
                             (f (transport A (p ⁻¹) a))
   theorem-2-9-5 = j (λ x₁ x₂ p → (f : (a : A x₁) → B x₁ a) → (a : A x₂) →
                        transport Π p f a ≡
                        transport B^ 
                             ((2-7-2.pair= {_} {_} {_ , _} {_ , _} ((p ⁻¹) , refl {_} {transport A (p ⁻¹) a}))⁻¹)
                             (f (transport A (p ⁻¹) a)))
                     (λ x f a → refl)


 module lemma-2-9-6 {X : Set} {A B : X → Set} where

   lemma-2-9-6 : {x y : X} {p : x ≡ y} → (f : A x → B x) → (g : A y → B y)
                           → (transport _ p f ≡ g) ≃ ((a : A x) → (transport _ p (f a) ≡ g (transport _ p a)))
   lemma-2-9-6 {x} {y} {p} = j (λ x y p → (f : A x → B x) → (g : A y → B y)
                           → (transport _ p f ≡ g) ≃ ((a : A x) → (transport _ p (f a) ≡ g (transport _ p a))))
                   (λ x f g → (happly , axiom-2-9-3))
                   p

   hat : {x y : X} {p : x ≡ y} (f : A x → B x) → (g : A y → B y)
                           → (transport _ p f ≡ g) → ((a : A x) → (transport _ p (f a) ≡ g (transport _ p a)))
   hat {x} {y} {p} = j (λ x y p → (f : A x → B x) → (g : A y → B y)
                           → (transport _ p f ≡ g) → ((a : A x) → (transport _ p (f a) ≡ g (transport _ p a))))
                   (λ x f g → happly)
                   p

   proof : {x y : X} {p : x ≡ y} (f : A x → B x) → (g : A y → B y) → (a : A x) → (q : transport _ p f ≡ g)
              → (transport (λ x → A x → B x) p f) (transport A p a) ≡ g (transport A p a)
   proof {x} {y} {p} f g a q = (transport (λ x → A x → B x) p f) (transport A p a)
                                   ≡⟨ ap {(x₁ : A y) → B y} (λ h → h (transport A p a)) (theorem-2-9-4 p f) ⟩
                 transport B p (f (transport A (p ⁻¹) (transport A p a)))
                                   ≡⟨ ap (λ Q → transport B p (f Q)) (lemma-2-3-9 {X} {A} x y x (p) (p ⁻¹) a) ⟩
                 transport B p (f (transport A (p ■ (p ⁻¹)) a))
                                   ≡⟨ ap (λ Q → transport B p (f (transport A Q a))) (p■p⁻¹≡refl p) ⟩
                 hat {x} {y} {p} f g q a

   -- What did I miss? XXX
   theorem : {x y : X} {p : x ≡ y} → (f : A x → B x) → (g : A y → B y) → (a : A x) → (q : transport _ p f ≡ g)
             → happly q (transport _ p a) ≡ proof {x} {y} {p} f g a q
   theorem {x} {y} {p} = j (λ x y p → (f : A x → B x) → (g : A y → B y) → (a : A x) → (q : transport (λ z → (x₁ : A z) → B z) p f ≡ g)
                        → happly q (transport A p a) ≡ proof {x} {y} {p} f g a q)
               (λ x f g a q → hat {x} {x} {refl} f g q a
                                         ≡⟨ p≡refl■p ⟩
                              (ap (λ Q → transport B refl (f (transport A Q a))) (p■p⁻¹≡refl refl)) ■ happly q a
                                         ≡⟨ p≡refl■p ⟩
                              ap (λ Q → transport B refl (f Q)) (lemma-2-3-9 {X} {A} x x x (refl) (refl ⁻¹) a) ■ refl ■ happly q a
                                         ≡⟨ p≡refl■p ⟩
                              ap (λ h → h (transport A refl a))
                                 (theorem-2-9-4 (refl {_} {g a}) f) ■ refl {_} {f a} ■ refl {_} {f a} ■ happly q (a)
                              ▻)
               p

 module lemma-2-9-7 {X : Set} {A : X → Set} {B : (x : X) → A x → Set} where

   B^ : (∑ X A) → Set
   B^ = λ w → B (pr₁ w) (pr₂ w)
   F = λ z → (x : A z) → B z x
   fibresection = λ x → (a : A x) → B x a

   compute : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                          (transport F p f ≡ g) →
                          (a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl)) (f a) ≡ g ((p ∗) a)
   compute = j (λ x y p → (f : fibresection x) → (g : fibresection y) →
                           (transport F p f ≡ g) →
                           (a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl)) (f a) ≡ g ((p ∗) a))
               (λ x f g → happly)

   unique : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                    (((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl)) (f a) ≡ g ((p ∗) a))
                    → transport F p f ≡ g)
   unique = j (λ x y p → (f : fibresection x) → (g : fibresection y) →
                          (((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl)) (f a) ≡ g ((p ∗) a))
                          → transport F p f ≡ g))
              (λ x f g p → funext p)

   forward : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
              (r : ((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , transport A p a} (p , refl)) (f a) ≡ g ((p ∗) a))) → compute p f g (unique p f g r) ≡ r 
   forward {x} {y} p = j (λ x y p → (f : fibresection x) → (g : fibresection y) →
              (r : ((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , transport A p a} (p , refl)) (f a) ≡ g ((p ∗) a))) → compute p f g (unique p f g r) ≡ r)
                       (λ x f g → computation)
                       p

   backward : {x y : X} → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                                          (r : transport F p f ≡ g) → unique p f g (compute p f g r) ≡ r 
   backward {x} {y} p = j (λ x y p → (f : fibresection x) → (g : fibresection y) →
                                      (r : transport F p f ≡ g) → unique p f g (compute p f g r) ≡ r)
                          (λ x f g → uniqueness)
                          p

   lemma-2-9-7 : (x y : X) → (p : x ≡ y) → (f : fibresection x) → (g : fibresection y) →
                    (transport F p f ≡ g) ≃
                    ((a : A x) → transport B^ (2-7-2.pair= {X} {A} {x , a} {y , (p ∗) a} (p , refl {A y} {(p ∗) a})) (f a) ≡ g ((p ∗) a))
   lemma-2-9-7 = λ x y p f g → (compute p f g , qinv-to-isequiv (compute p f g) (unique p f g , forward p f g , backward p f g))

 module 2-10 where
   
   idtoeqv : {A B : Set} → (A ≡ B) → A ≃ B
   idtoeqv p = (p ∗ , f) where
      f : isequiv (transport (λ A → A) p) 
      f = j (λ A B p → isequiv (transport (λ A → A) p))
              (λ A → (id , (λ x → refl)) , id , (λ x → refl))
              p

   postulate axiom-2-10-3 : {A B : Set} → isequiv (idtoeqv {A} {B})

   ua : {A B : Set} → (A ≃ B) → (A ≡ B)
   ua = pr₁ (isequiv-to-qinv idtoeqv axiom-2-10-3)

   idtoeqv○ua≡id : {A B : Set} → (r : A ≃ B) → (idtoeqv ○ ua) r ≡ id r
   idtoeqv○ua≡id {A} {B} = pr₁ (pr₂ (isequiv-to-qinv idtoeqv axiom-2-10-3))

   ua○idtoeqv≡id : {A B : Set} → (ua {A} {B} ○ idtoeqv) ~ id
   ua○idtoeqv≡id {A} {B} = pr₂ (pr₂ (isequiv-to-qinv idtoeqv axiom-2-10-3))

   elim : {A B : Set} → (pr₁ ○ idtoeqv {A} {B}) ≡ transport (λ A → A)
   elim {A} {B} = funext (λ p → refl)

   -- Confusing 'cos book treats A ≃ B as if it's A → B.
   -- So need extra pr₁ on RHS
   unicomp : {A B : Set} → {f : A ≃ B} → {x : A} → transport {Set} (λ X → X) {A} {B} (ua f) x ≡ pr₁ f x
   unicomp {A} {B} {f} {x} = transport {Set} (λ X → X) {A} {B} (ua f) x ≡⟨ refl ⟩
                             pr₁ (idtoeqv (ua f)) x ≡⟨ ap (λ Q → pr₁ Q x) (idtoeqv○ua≡id f) ⟩
                             pr₁ f x
                             ▻

   uniuniq : {A B : Set} → {p : A ≡ B} → p ≡ ua (idtoeqv p)
   uniuniq {A} {B} {p} = (ua○idtoeqv≡id p)⁻¹

   -- Identity of equivalence
   ide : {A : Set} → A ≃ A
   ide {A} = lemma-2-4-12i' A

   -- Composition of equivalence
   _○e_ : {A B C : Set} → (f : B ≃ C) → (f' : A ≃ B) → (A ≃ C)
   f ○e g = lemma-2-4-12iii g f

   _⁻¹e : {A B : Set} → A ≃ B → B ≃ A
   f ⁻¹e = lemma-2-4-12ii f

   refl≡uaid : {A : Set} → refl {Set} {A} ≡ ua ide
   refl≡uaid {A} = refl {Set} {A} ≡⟨ (ua○idtoeqv≡id refl)⁻¹ ⟩
                   ua (idtoeqv (refl {Set} {A})) ≡⟨ ap ua refl ⟩
                   ua ide
                   ▻

{-
   rhs : {A B C : Set} → (p : A ≡ B) → (q : B ≡ C) → A ≃ C
   rhs {A} {B} {C} p q = ((p ■ q) ∗) , qinv-to-isequiv (transport id (p ■ q)) ((((q ⁻¹) ■ (p ⁻¹)) ∗) ,
                 (( λ x → ((transport id (p ■ q))   ((transport id ((q ⁻¹) ■ (p ⁻¹)))   x)) ≡⟨  lemma-2-3-9 {Set} {id} C A C (((q ⁻¹) ■ (p ⁻¹))) (p ■ q) x ⟩
                          (((transport id (((q ⁻¹) ■ (p ⁻¹)) ■ (p ■ q))) x)) ≡⟨ ap (λ Q → transport id Q x) ((■-assoc (q ⁻¹) (p ⁻¹) (p ■ q))⁻¹) ⟩
                          (((transport id ((q ⁻¹) ■ ((p ⁻¹)) ■ (p ■ q))) x)) ≡⟨ ap (λ Q → transport id (q ⁻¹ ■ Q) x) ((■-assoc (p ⁻¹) (p) (q))) ⟩
                          (((transport id ((q ⁻¹) ■ (((p ⁻¹) ■ p) ■ q))) x)) ≡⟨ ap (λ Q → transport id ((q ⁻¹) ■ (Q ■ q)) x) (p⁻¹■p≡refl p) ⟩
                          (((transport id ((q ⁻¹) ■ (refl ■ q))  )   x)) ≡⟨ ap (λ Q → ((transport id ((q ⁻¹) ■ Q)  )   x)) ((p≡refl■p)⁻¹) ⟩
                          (((transport id ((q ⁻¹) ■ q)) x)) ≡⟨ ap (λ Q → transport id Q x) (p⁻¹■p≡refl q) ⟩
                          id x ▻) ,
                  (λ x → ((transport id (q ⁻¹ ■ p ⁻¹)) ○ transport id (p ■ q)) x ≡⟨ lemma-2-3-9 {Set} {id} A C A (p ■ q) (q ⁻¹ ■ p ⁻¹) x ⟩
                         ((transport id ((p ■ q) ■ (q ⁻¹ ■ p ⁻¹))) x) ≡⟨ ap (λ Q → transport id Q x) ((■-assoc p q (q ⁻¹ ■ p ⁻¹)))⁻¹ ⟩
                         ((transport id (p ■ (q ■ (q ⁻¹ ■ p ⁻¹)))) x) ≡⟨ ap (λ Q → ((transport id (p ■ Q)) x)) (■-assoc q (q ⁻¹) (p ⁻¹)) ⟩
                         transport id (p ■ ((q ■ q ⁻¹) ■ p ⁻¹)) x ≡⟨ ap (λ Q → (transport id (p ■ (Q ■ p ⁻¹))) x) ((p■p⁻¹≡refl q)) ⟩
                         transport id (p ■ (refl ■ p ⁻¹)) x ≡⟨ ap (λ Q → transport id (p ■ Q) x) (p≡refl■p ⁻¹) ⟩
                         transport id (p ■ (p ⁻¹)) x ≡⟨ ap (λ Q → (transport id Q) x) (p■p⁻¹≡refl p) ⟩
                         ((transport id (refl)) x) ≡⟨ refl ⟩
                         id x
                         ▻)))

   temp' : {A B C : Set} → {p : A ≡ B} → {q : B ≡ C} → idtoeqv (p ■ q) ≡ rhs p q
   temp' {A} {B} {C} {p} {q} = {!!}
-}

   -- Not quite method in book
   uafuag≡uafg-0 : {A B C : Set} → {p : A ≡ B} → {q : B ≡ C} → idtoeqv (p ■ q) ≡ idtoeqv q ○e idtoeqv p
   uafuag≡uafg-0 {A} {B} {C} {p} {q} = j₂ (λ A B C p q → idtoeqv (p ■ q) ≡ idtoeqv q ○e idtoeqv p)
                                 (λ x → refl)
                                 p q

   uafuag≡uafg : {A B C : Set} → {f : A ≃ B} → {g : B ≃ C} → ((ua f) ■ (ua g)) ≡ (ua (g ○e f))
   uafuag≡uafg {A} {B} {C} {f} {g} = ua f ■ ua g                ≡⟨ (ua○idtoeqv≡id (ua f ■ ua g))⁻¹ ⟩
                                     ua (idtoeqv (ua f ■ ua g)) ≡⟨ ap ua (uafuag≡uafg-0 {A} {B} {C} {ua f} {ua g}) ⟩
                                     ua (idtoeqv (ua g) ○e idtoeqv (ua f)) ≡⟨ ap (λ Q → ua (Q ○e idtoeqv (ua f))) (idtoeqv○ua≡id g) ⟩
                                     ua (g ○e idtoeqv (ua f)) ≡⟨ ap (λ Q → ua (g ○e Q)) (idtoeqv○ua≡id f) ⟩
                                     (ua (g ○e f))
                                     ▻

   uaf⁻1-0 : {A B : Set} → {f : A ≡ B} → idtoeqv (f ⁻¹) ≡ (idtoeqv f)⁻¹e
   uaf⁻1-0 {A} {.A} {refl} = refl

   uaf⁻1 : {A B : Set} → {f : A ≃ B} → ((ua f) ⁻¹) ≡ (ua (f ⁻¹e))
   uaf⁻1 {A} {B} {f} = (ua f) ⁻¹ ≡⟨ (ua○idtoeqv≡id ((ua f)⁻¹))⁻¹ ⟩
                       ua (idtoeqv ((ua f) ⁻¹)) ≡⟨ ap ua (uaf⁻1-0 {A} {B} {ua f}) ⟩
                       ua ((idtoeqv (ua f)) ⁻¹e) ≡⟨ ap (λ Q → ua (Q ⁻¹e)) (idtoeqv○ua≡id f) ⟩
                       ua (f ⁻¹e)
                       ▻
   
   lemma-2-10-5 : {A : Set} → {B : A → Set} → {x y : A} → {p : x ≡ y} → {u : B x}
                            → transport B p u ≡ pr₁ (idtoeqv (ap B p)) u
   lemma-2-10-5 {A} {B} {x} {y} {p} {u} =
                  transport (B ○ id) p u ≡⟨ lemma-2-3-10 B id p u ⟩
                  transport id (ap B p) u ≡⟨ refl ⟩
                  pr₁ (idtoeqv (ap B p)) u
                  ▻

 lcancel : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) →
           p ⁻¹ ■ p ■ q ≡ q
 lcancel {A} {x} {y} {z} p q = p ⁻¹ ■ p ■ q ≡⟨ ■-assoc (p ⁻¹) p q ⟩
                               (p ⁻¹ ■ p) ■ q ≡⟨ ap (λ Q → Q ■ q) (p⁻¹■p≡refl p) ⟩
                               refl ■ q ≡⟨ (p≡refl■p)⁻¹ ⟩
                               q
                               ▻

 open 2-10

 module 2-11 where

{-
   temp : {A B : Set} (f : A ≃ B) (a : A) → isequiv (ap {A} {B} (pr₁ f) {a} {a})
   temp = {!!}

   alt : {A B : Set} (f : A ≃ B) {a a' : A} (p : a ≡ a') → isequiv (ap {A} {B} (pr₁ f) {a} {a'})
   alt {A} {B} f {a} {a'} p = j (λ a a' p → isequiv (ap {A} {B} (pr₁ f) {a} {a'}))
                                {!temp!}
                                p


   module theorem-2-11-1' {A B : Set} (f : A ≃ B) {a : A} where
     
     f₀ : A → B
     f₀ = pr₁ f

     q : qinv f₀
     q = isequiv-to-qinv f₀ (pr₂ f)

     f⁻¹ : B → A
     f⁻¹ = pr₁ q

     α : (b : B) → f₀ (f⁻¹ b) ≡ b
     α = pr₁ (pr₂ q) 

     β : (a : A) → f⁻¹ (f₀ a) ≡ a
     β = pr₂ (pr₂ q) 

     apf⁻¹ : f₀ a ≡ f₀ a → f⁻¹ (f₀ a) ≡ f⁻¹ (f₀ a)
     apf⁻¹ = ap f⁻¹

     i : f₀ a ≡ f₀ a → a ≡ a
     i p = (β a) ⁻¹ ■ ap f⁻¹ refl ■ β a

     need : (β a) ⁻¹ ■ ap f⁻¹ (ap f₀ refl) ■ β a ≡ refl
     need = (β a) ⁻¹ ■ ap f⁻¹ (ap f₀ refl) ■ β a
                          ≡⟨ ap (λ Q → (β a) ⁻¹ ■ ap f⁻¹ Q ■ β a) (lemma-2-2-1 {A} {B} f₀) ⟩
            (β a) ⁻¹ ■ ap f⁻¹ refl ■ β a
                          ≡⟨  ap (λ Q → (β a) ⁻¹ ■ Q ■ β a) (lemma-2-2-1 {B} {A} f⁻¹ {f₀ a} {f₀ a}) ⟩
            (β a) ⁻¹ ■ refl ■ β a ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q) ((p≡refl■p)⁻¹) ⟩
            (β a) ⁻¹ ■ β a ≡⟨ p⁻¹■p≡refl (β a) ⟩
            refl
             ▻

     need' : ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ refl ■ β a) ≡ refl
     need' = ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ refl ■ β a)
                     ≡⟨ ap (λ Q → ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ refl ■ β a)) (lemma-2-2-1 {B} {A} f⁻¹ {f₀ a} {f₀ a}) ⟩
             ap f₀ ((β a) ⁻¹ ■ refl ■ β a) ≡⟨ ap (λ Q → ap f₀ ((β a) ⁻¹ ■ Q)) (p≡refl■p)⁻¹ ⟩
             ap f₀ ((β a) ⁻¹ ■ β a) ≡⟨ ap (λ Q → ap f₀ Q) ((p⁻¹■p≡refl (β a))) ⟩
             ap f₀ refl ≡⟨ lemma-2-2-1 f₀ ⟩
             refl
             ▻

     need1 : (x : f₀ a ≡ f₀ a) → ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ refl ■ β a) ≡ x
     need1 = {!!}

     theorem-2-11-1 : isequiv (ap {A} {B} (pr₁ f) {a} {a})
     theorem-2-11-1 = qinv-to-isequiv (ap f₀) (i , ({!need1!} , {!need'!}))
-}

   module theorem-2-11-1 {A B : Set} (f : A ≃ B) {a a' : A} where
     
     f₀ : A → B
     f₀ = pr₁ f

     q : qinv f₀
     q = isequiv-to-qinv f₀ (pr₂ f)

     f⁻¹ : B → A
     f⁻¹ = pr₁ q

     α : (b : B) → f₀ (f⁻¹ b) ≡ b
     α = pr₁ (pr₂ q) 

     β : (a : A) → f⁻¹ (f₀ a) ≡ a
     β = pr₂ (pr₂ q) 

     f⁻¹₁ : B → A
     f⁻¹₁ = pr₁ (pr₁ (pr₂ f))

     f⁻¹₂ : B → A
     f⁻¹₂ = pr₁ (pr₂ (pr₂ f))

     α' : (b : B) → f₀ (f⁻¹₁ b) ≡ b
     α' = pr₂ (pr₁ (pr₂ f))

     β' : (a : A) → f⁻¹₂ (f₀ a) ≡ a
     β' = pr₂ (pr₂ (pr₂ f))

     apf⁻¹ : f₀ a ≡ f₀ a' → f⁻¹ (f₀ a) ≡ f⁻¹ (f₀ a')
     apf⁻¹ = ap f⁻¹

     i : f₀ a ≡ f₀ a' → a ≡ a'
     i p = (β a) ⁻¹ ■ ap f⁻¹ p ■ β a'

     i₁ : f₀ a ≡ f₀ a' → a ≡ a'
     i₁ p = (β' a) ⁻¹ ■ ap f⁻¹₂ p ■ β' a'

     i₂ : f₀ a ≡ f₀ a' → a ≡ a'
     i₂ p = (β' a) ⁻¹ ■ ap f⁻¹₂ p ■ β' a'

     inv-image : {A B : Set} → (f : A → B) → (y : B) → Set
     inv-image {A} f y = ∑ A (λ x → f x ≡ y)

     is-contr : (A : Set) → Set
     is-contr A = ∑ A (λ x → (y : A) → x ≡ y)

     is-equiv' : {A B : Set} → (f : A → B) → Set
     is-equiv' {A} {B} f = (y : B) → is-contr (inv-image f y)
     
     -- x' : ∑ A (λ x' → pr₁ f x' ≡ y)
     -- (f₀ (pr₁ x') ≡ y
     -- Given
     -- pr₁ x' = x, say
     -- pr₂ x' : (f₀ x ≡ y)
     -- ap f⁻¹ (pr₂ x') : f⁻¹ (f₀ x) ≡ f⁻¹ y
     -- β x ■ ap f⁻¹ (pr₂ x') : x ≡ f⁻¹ y

     -- RTP : ?0 : (f⁻¹ y , α y) ≡ (x , f₀ (f⁻¹ y) ≡ y)
     {-
     x' : ∑ A (λ x → pr₁ f x ≡ y)
     pr₁ x' : A
     β (pr₁ x') : f⁻¹ (f₀ (pr₁ x')) ≡ pr₁ x'
     pr₂ x' : f₀ (pr₁ x') ≡ y
     (β (pr₁ x'))⁻¹ : pr₁ x' ≡ f⁻¹ (f₀ (pr₁ x'))
     ap f⁻¹ (pr₂ x') : f⁻¹ (f₀ (pr₁ x')) ≡ f⁻¹ y
     (β (pr₁ x'))⁻¹ ■ ap f⁻¹ (pr₂ x') : pr₁ x' ≡ f⁻¹ y 
     (ap f⁻¹ (pr₂ x'))⁻¹ ■ β (pr₁ x') : (...)⁻¹
     -}

     -- ?0 : ∑ (.y ≡ .y') (λ q₁ → ∑ (.y ≡ .y') (λ r → .y , .y' , q₁ ≡ .y , .y' , r))
     -- ?0 : .y , .y' , ap pr₁ α ≡ .y , .y' , ap pr₁ α
     μ : {A : Set} → {x y x' y' : A} → (p : x ≡ y) (p' : x' ≡ y') (α : (x , y , p) ≡ (x' , y' , p'))
                   → ∑ (x ≡ x') (λ q → ∑ (y ≡ y') (λ r → (x , x' , q) ≡ (y , y' , r)))
     μ refl refl α = ap pr₁ α , (ap pr₁ α , refl)

     module test {A B : Set} {f : A → B} {f⁻¹ : B → A} (b : B) (a : ∑ A (λ x → f x ≡ b)) (q : a ≡ a) where

       -- 0: f (pr₁ a) , b , pr₂ a ≡ f (pr₁ a) , b , pr₂ a
       x : ∑ (f (pr₁ a) ≡ f (pr₁ a)) (λ q → ∑ (b ≡ b) (λ r → (f (pr₁ a) , f (pr₁ a) , q) ≡ (b , b , r)))
       x = μ (pr₂ a) (pr₂ a) (ap (λ x₁ → f (pr₁ x₁) , (b , pr₂ x₁)) q)

       -- b ≡ b
       y : (f (pr₁ a) , f (pr₁ a) , pr₁ x) ≡ (b , b , pr₁ (pr₂ x))
       y = pr₂ (pr₂ x)

       -- ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
       z = 2-7-2.comp y
       z1 : {!!} ≡ b , {!!}
       z1 = pr₂ z
       z2 : ∑ {!!} (λ x₁ → {!!})
       z2 = 2-7-2.comp z1
       z3 : {!!} ≡ {!!}
       z3 = pr₂ z2

       ν : q ≡ refl
       ν = {!!}

     -- ?0 : ?0 : f⁻¹ y , α y ≡ x'
     xxx : is-equiv' f₀
     xxx y = (f⁻¹ y , α y) , {!!}

     need : (p : a ≡ a') → (β a) ⁻¹ ■ ap f⁻¹ (ap f₀ p) ■ β a' ≡ p
     need p = ((β a)⁻¹) ■ ap f⁻¹ (ap f₀ p) ■ β a'
                    ≡⟨  ap (λ Q → (β a) ⁻¹ ■ Q ■ β a') (lemma-2-2-iii {A} {B} f₀ f⁻¹ p) ⟩
              ((β a)⁻¹) ■ ap (f⁻¹ ○ f₀) p ■ β a'
                    ≡⟨ ap (λ Q → ((β a)⁻¹) ■ Q) ((lemma-2-4-3 (f⁻¹ ○ f₀) id β p)⁻¹) ⟩
              ((β a)⁻¹) ■ (β a) ■ ap id p
                    ≡⟨ lcancel (β a) (ap id p) ⟩
              ap id p
                    ≡⟨ apidp≡p p ⟩
              p
              ▻

     need-alt : {a a' : A} → (p : a ≡ a') → (β a) ⁻¹ ■ ap f⁻¹ (ap f₀ p) ■ β a' ≡ p
     need-alt {a} {.a} refl = ((β a)⁻¹) ■ refl ■ β a
                                        ≡⟨ ap (λ Q → ((β a)⁻¹) ■ Q) (p≡refl■p ⁻¹) ⟩
                              ((β a)⁻¹) ■ (β a)
                                        ≡⟨ (p⁻¹■p≡refl (β a)) ⟩
                              refl
                              ▻

     need' : (q : f₀ a ≡ f₀ a') → ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ q ■ β a') ≡ q
     need' p = ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ p ■ β a') ≡⟨ ap■ f₀ ((β a) ⁻¹) (ap f⁻¹ p ■ β a') ⟩
               ap f₀ ((β a) ⁻¹) ■ ap f₀ (ap f⁻¹ p ■ β a') ≡⟨ ap (λ Q → ap f₀ ((β a) ⁻¹) ■ Q) (ap■ f₀ (ap f⁻¹ p) (β a')) ⟩
               ap f₀ ((β a) ⁻¹) ■ ap f₀ (ap f⁻¹ p) ■ ap f₀ (β a') ≡⟨ ap (λ Q → ap f₀ ((β a) ⁻¹) ■ Q ■ ap f₀ (β a')) ((lemma-2-2-iii f⁻¹ f₀ p)) ⟩
               ap f₀ ((β a) ⁻¹) ■ ap (f₀ ○ f⁻¹) p ■ ap f₀ (β a') ≡⟨ {!ap (λ Q → !} ⟩
               p
               ▻

     ■-id : (A : Set) → (a b : A) → (p : a ≡ b) → (a , p) ≡ (b , refl {A} {b})  --∑ A (λ c → a ≡ c) → 
     ■-id A a .a refl = refl

     ■-left : (A : Set) → (a b : A) → (c : A) → (p : a ≡ b) → (q : b ≡ c) → (a , p ■ q) ≡ (b , q)  --∑ A (λ c → a ≡ c) → 
     ■-left A a .a .a refl refl = refl

     ■-right : (A : Set) → (a b c : A) → (p : a ≡ b) → (q : b ≡ c) → (c , p ■ q) ≡ (b , p)  --∑ A (λ c → a ≡ c) → 
     ■-right A a .a .a refl refl = refl



     -- ?3: (x : pr₁ f a ≡ pr₁ f a') → ap f₀ ((β a) ⁻¹ ■ ap f⁻¹ p ■ β a') ≡ p
     -- ?4 : (x : a ≡ a') → (β a) ⁻¹ ■ ap f⁻¹ (ap f₀ p) ■ β a' ≡ p
     theorem-2-11-1 : isequiv (ap {A} {B} (pr₁ f) {a} {a'})
     theorem-2-11-1 = qinv-to-isequiv (ap (pr₁ f)) (i , need' , need-alt)

     need₂ : (p : a ≡ a') → (β' a) ⁻¹ ■ ap f⁻¹₂ (ap f₀ p) ■ β' a' ≡ p
     need₂ p = ((β' a)⁻¹) ■ ap f⁻¹₂ (ap f₀ p) ■ β' a'
                    ≡⟨  ap (λ Q → (β' a) ⁻¹ ■ Q ■ β' a') (lemma-2-2-iii {A} {B} f₀ f⁻¹₂ p) ⟩
              ((β' a)⁻¹) ■ ap (f⁻¹₂ ○ f₀) p ■ β' a'
                    ≡⟨ ap (λ Q → ((β' a)⁻¹) ■ Q) ((lemma-2-4-3 (f⁻¹₂ ○ f₀) id β' p)⁻¹) ⟩
              ((β' a)⁻¹) ■ (β' a) ■ ap id p
                    ≡⟨ lcancel (β' a) (ap id p) ⟩
              ap id p
                    ≡⟨ apidp≡p p ⟩
              p
              ▻

     theorem-2-11-1' : isequiv (ap {A} {B} (pr₁ f) {a} {a'})
     theorem-2-11-1' = ({!!} , {!!}) , (i₂ , need₂)

