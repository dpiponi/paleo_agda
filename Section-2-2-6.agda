{-# OPTIONS --without-K --type-in-type #-}

module Section-2-2-6 where

 import Section-2-2-1
 open Section-2-2-1
 open Paths

 import Section-2-2-2
 open Section-2-2-2

 import Section-2-2-3
 open Section-2-2-3

 import Section-2-2-4
 open Section-2-2-4

 import tools
 open tools

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

  private h : {a a' : A} → {b b' : B} → (r : (a , b) ≡ (a' , b')) → pair (ipair r) ≡ r
  h = j prop
      (ind∑ (λ x → prop x x refl) (λ a b → refl))
      where
        prop : (x : A × B) → (y : A × B) → (x ≡ y) → Set
        prop = ind∑ _ (λ a b →
               ind∑ _ (λ a' b' →
                 λ r → pair (ipair r) ≡ r))

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

 -- These theorems use a slightly different context to earlier parts of chapter
 -- so not in module.


 uppt : {A B : Set} → (x : A × B) → (pr₁ x , pr₂ x) ≡ x
 uppt (a , b) = refl

 theorem-2-6-4 : {Z : Set} → {A B : Z → Set} → {w z : Z} → (p : z ≡ w) → (x : A z × B z) →
                          transport (λ z → A z × B z) p x ≡ (transport A p (pr₁ x) , transport B p (pr₂ x))
 theorem-2-6-4 refl x = (uppt x)⁻¹

 open 2-6
        
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

