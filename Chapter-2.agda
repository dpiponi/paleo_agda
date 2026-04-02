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

 import tools
 open tools

 open import Section-2-2-6
-- open Section-2-2-6

 open import Section-2-2-7
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
   gf≡id x .x refl = ind⋆ (λ x → g x x (f x x refl) ≡ refl) x refl

   theorem-2-8-1 : (x y : unit) → (x ≡ y) ≃ unit
   theorem-2-8-1 x y = (f x y , qinv-to-isequiv (λ _ → ⋆) (g x y , (fg≡id x y , gf≡id x y)))

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
                                         ≡⟨ p≡refl■p _ ⟩
                              (ap (λ Q → transport B refl (f (transport A Q a))) (p■p⁻¹≡refl refl)) ■ happly q a
                                         ≡⟨ p≡refl■p _ ⟩
                              ap (λ Q → transport B refl (f Q)) (lemma-2-3-9 {X} {A} x x x (refl) (refl ⁻¹) a) ■ refl ■ happly q a
                                         ≡⟨ p≡refl■p _ ⟩
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

   -- Not quite method in book
   uafuag≡uafg-0 : {A B C : Set} → {p : A ≡ B} → {q : B ≡ C} → idtoeqv (p ■ q) ≡ idtoeqv q ○e idtoeqv p
   uafuag≡uafg-0 {A} {.A} {.A} {refl} {refl} = refl

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
                               refl ■ q ≡⟨ (p≡refl■p _)⁻¹ ⟩
                               q
                               ▻

 open 2-10

 module 2-out-of-6 {A B C D : Set} (f : A → B) (g : B → C) (h : C → D) (q : isequiv (g ○ f)) (r : isequiv (h ○ g)) where
   q' : qinv (g ○ f)
   q' = isequiv-to-qinv (g ○ f) q
   
   a : C → A
   a = pr₁ q'

   α : (g ○ (f ○ a)) ~ id
   α = pr₁ (pr₂ q')

   β : (a ○ (g ○ f)) ~ id
   β = pr₂ (pr₂ q')

   r' : qinv (h ○ g)
   r' = isequiv-to-qinv (h ○ g) r
   
   b : D → B
   b = pr₁ r'

   γ : (h ○ (g ○ b)) ~ id
   γ = pr₁ (pr₂ r')

   δ : (b ○ (h ○ g)) ~ id
   δ = pr₂ (pr₂ r')

   f-has-right-inverse : (f ○ (a ○ g)) ~ id
   f-has-right-inverse x = f (a (g x)) ≡⟨ (δ (f (a (g x))))⁻¹ ⟩
             b (h (g (f (a (g x))))) ≡⟨ ap (b ○ h) (α (g x)) ⟩
             b (h (g x)) ≡⟨ δ x ⟩
             x
             ▻

   f-has-qinv : qinv f
   f-has-qinv = (a ○ g , f-has-right-inverse , β)

   f-is-equiv : isequiv f
   f-is-equiv = qinv-to-isequiv f f-has-qinv

 module homotopic-to-equiv {A B : Set} (f : A → B) (g : A ≃ B) (H : f ~ pr₁ g) where
   g₀ : A → B
   g₀ = pr₁ g

   g' : qinv g₀
   g' = isequiv-to-qinv g₀ (pr₂ g)

   h : B → A
   h = pr₁ g'

   α : (g₀ ○ h) ~ id
   α = pr₁ (pr₂ g')

   β : (h ○ g₀) ~ id
   β = pr₂ (pr₂ g')

   is-equiv : isequiv f
   is-equiv = qinv-to-isequiv f (h , (λ x → H (h x) ■ α x) , (λ x → ap h (H x) ■ β x))

 module 2-11 where

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

     concat : {A : Set} {a a' b b' : A} (α' : b ≡ a) → (β : a' ≡ b') → (a ≡ a') → (b ≡ b')
     concat α' β p = α' ■ p ■ β

     conc'' : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (p : a ≡ a') → (b ≡ b')
     conc'' one two p = (one ⁻¹) ■ p ■ two

     concat' : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β' : b' ≡ a') → (b ≡ b') → (a ≡ a')
     concat' α β' q = α ■ q ■ β'

     conc' : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (p : b ≡ b') → (a ≡ a')
     conc' one two p = one ■ p ■ (two ⁻¹)

     myequiv : {A : Set} {a a' b b' : A} (α : a ≡ b) → (α' : b ≡ a) → (β : a' ≡ b') → (β' : b' ≡ a') →
               (q : b ≡ b')
               → ({d : A} (q : b ≡ d) → α' ■ (α ■ q) ≡ q)
               → ({d : A} (q : d ≡ b') → q ■ (β' ■ β) ≡ q)
               → concat α' β (concat' α β' q) ≡ q
     myequiv α α' β β' q lcancel rcancel = α' ■ (α ■ q ■ β') ■ β ≡⟨ ■-assoc α' (α ■ q ■ β') β ⟩
                          (α' ■ (α ■ (q ■ β'))) ■ β ≡⟨ lcancel (q ■ β') ■r β ⟩
                          (q ■ β') ■ β ≡⟨ (■-assoc q β' β)⁻¹ ⟩
                          q ■ (β' ■ β) ≡⟨ rcancel q ⟩
                           q ▻

     isequiv-odd : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (q : b ≡ b')
               → concat (α ⁻¹) β (concat' α (β ⁻¹) q) ≡ q
     isequiv-odd one two p = myequiv one (one ⁻¹) two (two ⁻¹) p (λ p → p⁻¹■p■q≡q one p) (λ p → p■q⁻¹■q≡p p two)

     isequiv-even : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → (q : a ≡ a')
               → concat (α) (β ⁻¹) (concat' (α ⁻¹) (β ) q) ≡ q
     isequiv-even one two q = myequiv (one ⁻¹) one (two ⁻¹) two q (λ p → p■p⁻¹■q≡q one p) (λ p → p■q■q⁻¹≡p p two)

     concat-is-qinv : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → qinv (conc' α β)
     concat-is-qinv one two = conc'' one two , (isequiv-even one two , isequiv-odd one two)

     concat-is-equiv : {A : Set} {a a' b b' : A} (α : a ≡ b) → (β : a' ≡ b') → isequiv (conc' α β)
     concat-is-equiv one two = qinv-to-isequiv (conc' one two) (concat-is-qinv one two)

     ap-homotopic-concat : (ap f⁻¹ ○ ap f₀) ~ (conc' (β a) (β a'))
     ap-homotopic-concat p = (ap f⁻¹ ○ ap f₀) p ≡⟨ (ap-hom-first f₀ f⁻¹ p) ⟩
                             ap (f⁻¹ ○ f₀) p ≡⟨ p≡p■q■q⁻¹ _ (β a') ⟩
                             ap (f⁻¹ ○ f₀) p ■ β a' ■ (β a')⁻¹ ≡⟨ ■-assoc (ap (f⁻¹ ○ f₀) p) (β a') ((β a')⁻¹) ⟩
                             (ap (f⁻¹ ○ f₀) p ■ β a') ■ (β a')⁻¹ ≡⟨ ((hom-square (f⁻¹ ○ f₀) id β p)⁻¹) ■r (β a' ⁻¹) ⟩
                             (β a ■ ap id p) ■ (β a')⁻¹ ≡⟨ (β a ■l ap-id-first p) ■r ((β a')⁻¹) ⟩
                             (β a ■ p) ■ (β a')⁻¹ ≡⟨ (■-assoc (β a) p _)⁻¹ ⟩
                             β a ■ p ■ (β a')⁻¹
                             ▻

     ap-homotopic-concat' : (ap f₀ ○ ap f⁻¹) ~ (conc' (α (f₀ a)) (α (f₀ a')))
     ap-homotopic-concat' q = (ap f₀ ○ ap f⁻¹) q ≡⟨ (ap-hom-first f⁻¹ f₀ q) ⟩
                             ap (f₀ ○ f⁻¹) q ≡⟨ p≡p■q■q⁻¹ _ (α (f₀ a')) ⟩
                             ap (f₀ ○ f⁻¹) q ■ α (f₀ a') ■ α (f₀ a')⁻¹ ≡⟨ ■-assoc (ap (f₀ ○ f⁻¹) q) (α (f₀ a')) (α (f₀ a')⁻¹) ⟩
                             (ap (f₀ ○ f⁻¹) q ■ α (f₀ a')) ■ α (f₀ a')⁻¹ ≡⟨ ((hom-square (f₀ ○ f⁻¹) id α q)⁻¹) ■r (α (f₀ a')⁻¹) ⟩
                             (α (f₀ a) ■ ap id q) ■ α (f₀ a')⁻¹ ≡⟨ (α (f₀ a) ■l ap-id-first q) ■r ((α (f₀ a'))⁻¹) ⟩
                             (α (f₀ a) ■ q) ■ α (f₀ a')⁻¹ ≡⟨ (■-assoc (α (f₀ a)) q _)⁻¹ ⟩
                             α (f₀ a) ■ q ■ (α (f₀ a'))⁻¹
                             ▻

     res₁ : isequiv (ap f⁻¹ ○ ap f₀ {a} {a'})
     res₁ = homotopic-to-equiv.is-equiv (ap f⁻¹ ○ ap f₀) ((conc' (β a) (β a')) , concat-is-equiv (β a) (β a')) ap-homotopic-concat

     res₂ : isequiv (ap f₀ ○ ap f⁻¹ {f₀ a} {f₀ a'})
     res₂ = homotopic-to-equiv.is-equiv (ap f₀ ○ ap f⁻¹) ((conc' (α (f₀ a)) (α (f₀ a'))) , (concat-is-equiv (α (f₀ a)) (α (f₀ a')))) ap-homotopic-concat'

     proof : isequiv (ap f₀ {a} {a'})
     proof = f-is-equiv (ap f₀) (ap f⁻¹) (ap f₀) res₁ res₂
                       where open 2-out-of-6

{-
     module X {a : A} {p : a ≡ a} {u : ap f₀ p ≡ refl} where

       inv-refl : p ≡ refl
       inv-refl = p ≡⟨ p≡refl■p ⟩
            refl ■ p ≡⟨ ap (λ Q → Q ■ p) (p⁻¹■p≡refl (β a))⁻¹ ⟩
            ((β a)⁻¹ ■ β a) ■ p ≡⟨ (■-assoc ((β a)⁻¹) (β a) p)⁻¹ ⟩
            (β a)⁻¹ ■ (β a ■ p) ≡⟨ ap (λ Q → (β a)⁻¹ ■ β a ■ Q) ((ap-id-first p)⁻¹) ⟩
            (β a)⁻¹ ■ (β a ■ ap id p) ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q) (hom-square (f⁻¹ ○ f₀) id β p) ⟩
            (β a)⁻¹ ■ (ap (f⁻¹ ○ f₀) p ■ β a) ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q ■ β a) ((ap-hom-first f₀ f⁻¹ p)⁻¹) ⟩
            (β a)⁻¹ ■ (ap f⁻¹ (ap f₀ p) ■ β a) ≡⟨ ap (λ Q → (β a)⁻¹ ■ (ap f⁻¹ Q ■ β a)) u ⟩
            (β a)⁻¹ ■ (refl ■ β a) ≡⟨ ap (λ Q → (β a)⁻¹ ■ Q) (p≡refl■p ⁻¹) ⟩
            (β a)⁻¹ ■ β a ≡⟨ p⁻¹■p≡refl (β a) ⟩
            refl
            ▻
     open X

     module Y {a : A} {p : a ≡ a} {q : a ≡ a} {u v : ap f₀ p ≡ ap f₀ q} where

       r1 : ap f₀ (p ■ q ⁻¹) ≡ refl
       r1 = ap f₀ (p ■ q ⁻¹) ≡⟨ ap-hom-second f₀ p (q ⁻¹) ⟩
            ap f₀ p ■ ap f₀ (q ⁻¹) ≡⟨ ap (λ Q → ap f₀ p ■ Q) (ap-inv-second f₀ q) ⟩
            ap f₀ p ■ (ap f₀ q)⁻¹ ≡⟨ ap (λ Q → ap f₀ p ■ (Q ⁻¹)) (v ⁻¹) ⟩
            ap f₀ p ■ (ap f₀ p)⁻¹ ≡⟨ p■p⁻¹≡refl (ap f₀ p) ⟩
            refl
            ▻

       r2 : p ■ q ⁻¹ ≡ refl
       r2 = X.inv-refl {a} {p ■ q ⁻¹} {r1} 

-}

 lemma-2-11-2-i : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : a ≡ x₁) → transport (λ x → a ≡ x) p q ≡ q ■ p
 lemma-2-11-2-i a .a .a refl refl = refl

 lemma-2-11-2-ii : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : x₁ ≡ a) → transport (λ x → x ≡ a) p q ≡ p ⁻¹ ■ q
 lemma-2-11-2-ii a .a .a refl refl = refl

 lemma-2-11-2-iii : {A : Set} (x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : x₁ ≡ x₁) → transport (λ x → x ≡ x) p q ≡ p ⁻¹ ■ q ■ p
 lemma-2-11-2-iii x₁ .x₁ refl q = q ≡⟨ p≡p■refl _ ⟩
                                 q ■ refl ≡⟨ p≡refl■p _ ⟩
                                 refl ■ q ■ refl
                                 ▻

{-
  lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                             → transport (P ○ f) p u ≡ transport P (ap f p) u

-}

 theorem-2-11-3 : {A B : Set} (f g : A → B) → (a a' : A) → (p : a ≡ a') → (q : f a ≡ g a)
                      → transport (λ x → f x ≡ g x) p q ≡ (ap f p)⁻¹ ■ q ■ ap g p
 theorem-2-11-3 f g a .a refl q = q ≡⟨ p≡p■refl _ ⟩
                                 q ■ refl ≡⟨ p≡refl■p _ ⟩
                                 refl ■ q ■ refl
                                 ▻

 -- (p ∗) (f a) ≡ (p ∗) (g a)
 theorem-2-11-4 : {A : Set} (B : A → Set) (f g : (x : A) → B x) → {a a' : A} → (p : a ≡ a') → (q : f a ≡ g a)
                      → transport (λ x → f x ≡ g x) p q ≡ (apd f p)⁻¹ ■ ap (transport B p) q ■ apd g p
 theorem-2-11-4 B f g refl q = q ≡⟨ (apidp≡p q)⁻¹ ⟩
                              ap id q ≡⟨ p≡p■refl _ ⟩
                              ap id q ■ refl ≡⟨ p≡refl■p _ ⟩
                              refl ■ ap id q ■ refl
                              ▻

{-
?0 : ∑ q ≡ r → q ■ refl ≡ refl ■ r) isequiv
-}

 module theorem-2-11-5-refl {A : Set} {a : A} (q : a ≡ a) (r : a ≡ a) where

   forward : (q ≡ r) → (q ■ refl ≡ refl ■ r)
   forward p = p■refl≡p q ■ p ■ p≡refl■p r

   reverse : (q ■ refl ≡ refl ■ r) → (q ≡ r)
   reverse p = p≡p■refl q ■ p ■ refl■p≡p r

   hom1 : (x : q ■ refl ≡ refl ■ r) → forward (reverse x) ≡ x
   hom1 p = p■refl≡p q ■ (p≡p■refl q ■ p ■ refl■p≡p r) ■ p≡refl■p r
                     ≡⟨ ■-assoc (p■refl≡p q) _ (p≡refl■p r) ⟩
            (p■refl≡p q ■ (p≡p■refl q ■ p ■ refl■p≡p r)) ■ p≡refl■p r
                     ≡⟨ p⁻¹■p■q≡q (p≡p■refl q) _ ■r p≡refl■p r ⟩
            (p ■ refl■p≡p r) ■ p≡refl■p r
                     ≡⟨ (■-assoc p _ _)⁻¹ ⟩
            p ■ refl■p≡p r ■ p≡refl■p r
                     ≡⟨ p■q⁻¹■q≡p p (p≡refl■p r) ⟩
            p
            ▻

   hom2 : (x : q ≡ r) → reverse (forward x) ≡ x
   hom2 p = p≡p■refl q ■ (p■refl≡p q ■ p ■ p≡refl■p r) ■ refl■p≡p r ≡⟨ ■-assoc (p≡p■refl q) _ (refl■p≡p r) ⟩
            (p≡p■refl q ■ p■refl≡p q ■ p ■ p≡refl■p r) ■ refl■p≡p r ≡⟨ (p■p⁻¹■q≡q (p≡p■refl q) _) ■r refl■p≡p r ⟩
            (p ■ p≡refl■p r) ■ refl■p≡p r ≡⟨ (■-assoc p _ _)⁻¹ ⟩
            p ■ p≡refl■p r ■ refl■p≡p r ≡⟨ p■q■q⁻¹≡p p (p≡refl■p r) ⟩
            p
            ▻

   proof : (q ≡ r) ≃ (q ■ refl ≡ refl ■ r)
   proof = forward , qinv-to-isequiv forward (reverse , (hom1 , hom2))

   

 theorem-2-11-5 : {A : Set} {a a' : A} (p : a ≡ a') → (q : a ≡ a) → (r : a' ≡ a')
                            → (transport (λ x → x ≡ x) p q ≡ r) ≃ (q ■ p ≡ p ■ r)
 theorem-2-11-5 refl q r = proof
                           where open theorem-2-11-5-refl q r

 data void : Set where

 elim-void : {A : Set} → void → A
 elim-void ()

 data _+_ (A B : Set) : Set where
   inl : A → A + B
   inr : B → A + B

 based : {A : Set} {a : A} (C : (x : A) → a ≡ x → Set)
          → C a refl
          → (x : A) → (P : a ≡ x)
          → C x P
 based _ b _ refl = b

 module theorem-2-12-5 {A B : Set} {a₀ : A} where

{-
  code x = paths from base point to x
-}

   code : A + B → Set
   code (inl a) = a₀ ≡ a
   code (inr b) = void

   -- convert path to x to new rep
   encode : (x : A + B) → (p : inl a₀ ≡ x) → code x
   encode x p = transport code p (refl {_} {a₀})

   decode : (x : A + B) → (c : code x) → inl a₀ ≡ x
   decode (inl a) c = ap inl c
   decode (inr _) c = elim-void c

   proof₁ : (x : A + B) (p : inl a₀ ≡ x) → decode x (encode x p) ≡ p
   proof₁ x p = based {A + B} {inl a₀}
                (λ x p → decode x (encode x p) ≡ p)
                refl
                x p

{-
  lemma-2-3-10 : {A B : Set} → (f : A → B) → (P : B → Set) → {x y : A} → (p : x ≡ y) → (u : P (f x))
                             → transport (P ○ f) p u ≡ transport P (ap f p) u

  lemma-2-11-2-ii : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : x₁ ≡ a) → transport (λ x → x ≡ a) p q ≡ p ⁻¹ ■ q
  lemma-2-11-2-i : {A : Set} (a x₁ x₂ : A) → (p : x₁ ≡ x₂) → (q : a ≡ x₁) → transport (λ x → a ≡ x) p q ≡ q ■ p

  code ○ inl = λ a → a₀ ≡ a
  P = code
  f = inl
  P ○ f = λ a → a₀ ≡ a

-}
   proof₂ : (x : A + B) (c : code x) → encode x (decode x c) ≡ c
   proof₂ (inl a) c = transport code (ap inl c) (refl {_} {a₀}) ≡⟨ (lemma-2-3-10 inl code c refl)⁻¹ ⟩
                      transport (λ a → a₀ ≡ a) c (refl {_} {a₀}) ≡⟨ lemma-2-11-2-i a₀ a₀ a c refl ⟩
                      refl {_} {a₀} ■ c ≡⟨ refl■p≡p c ⟩
                      c
                      ▻
   proof₂ (inr _) c = elim-void c

   proof : (x : A + B) → (inl a₀ ≡ x) ≃ code x
   proof x = encode x , qinv-to-isequiv (encode x) (decode x , (proof₂ x , proof₁ x))

 transport-coproduct-i : {X : Set} → {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (A B : X → Set)
                            → (a : A x₁)
                            → transport (λ x → A x + B x) p (inl a) ≡ inl (transport A p a)
 transport-coproduct-i refl A B a = refl

 transport-coproduct-ii : {X : Set} → {x₁ x₂ : X} → (p : x₁ ≡ x₂) → (A B : X → Set)
                            → (b : B x₁)
                            → transport (λ x → A x + B x) p (inr b) ≡ inr (transport B p b)
 transport-coproduct-ii refl A B b = refl

 module Section-2-2-13 where
   open import Data.Nat

   code : ℕ → ℕ → Set
   code ℕ.zero ℕ.zero = unit
   code ℕ.zero (suc n) = void
   code (suc m) ℕ.zero = void
   code (suc m) (suc n) = code m n

   r : (n : ℕ) → code n n
   r ℕ.zero = ⋆
   r (suc n) = r n

   module theorem-2-13-1 where

     encode : (m n : ℕ) → (m ≡ n) → code m n
     encode m n p = transport (code m) p (r m)

     decode : (m n : ℕ) → code m n → m ≡ n
     decode zero zero x = refl {_} {zero}
     decode zero (suc n) x = elim-void x
     decode (suc m) zero x = elim-void x
     decode (suc m) (suc n) x = ap suc (decode m n x)

     proof₀ : (n : ℕ) → encode n n refl ≡ r n
     proof₀ n = refl

     proof₁ : (m n : ℕ) → (p : m ≡ n) → decode m n (encode m n p) ≡ p
     proof₁ zero .zero refl = refl
     proof₁ (suc n) .(suc n) refl = ap suc (decode n n (r n))
                                            ≡⟨ proof₁ (suc n) (suc n) refl ⟩
                                    refl
                                    ▻