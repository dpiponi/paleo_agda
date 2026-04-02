module Exercises where

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

infixl 40 _+_
infixl 60 _*_

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero * m = zero
suc n * m = m + n * m

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

-- Ex 2.2 (a)

Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

vec : {n : Nat} {A : Set} -> A -> Vec A n
vec {zero} x = []
vec {suc y} x = x :: vec {y} x

-- Ex 2.2 (b)

module xxx where
  infixl 90 _$_
  
  _$_ : {n : Nat} {A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
  [] $ [] = []
  (f :: fs) $ (y :: ys) = f y :: fs $ ys
  
  transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
  transpose [] = vec []
  transpose (xs :: xss) = vec _::_ $ xs $ (transpose xss)
  
  _∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
    (f : {x : A}(y : B x) -> C x y)(g : (x : A) -> B x)
    (x : A) -> C x (g x)
  (f ∘ g) x = f (g x)
  
  data Fin : Nat -> Set where
    fzero : {n : Nat} -> Fin (suc n)
    fsuc : {n : Nat} -> Fin n -> Fin (suc n)
  
  _!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
  [] ! ()
  (x :: xs) ! fzero = x
  (x :: xs) ! (fsuc i) = xs ! i
  
  tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
  tabulate {zero} f = []
  tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)
  
  -- Ex 2.2 (c)
  
  lem-!-tab : ∀ {A n} (f : Fin n → A) (i : Fin n) → (tabulate f ! i) ≡ f i
  lem-!-tab f fzero = refl
  lem-!-tab f (fsuc y) = lem-!-tab (f ∘ fsuc) y
  
  list-equal : {A : Set} {x x' : A} {n : Nat } {xs xs' : Vec A n}
               → x ≡ x' → xs ≡ xs' → (x :: xs) ≡ (x' :: xs')
  list-equal refl refl = refl
  
  lem-tab-! : forall {A n} (xs : Vec A n) -> tabulate (_!_ xs) ≡ xs
  lem-tab-! [] = refl
  lem-tab-! {_} {suc n} (x :: xs) = list-equal refl (lem-tab-! {_} {n} xs)
  
-- Ex 2.3 (a)

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {x xs ys} -> xs ⊆ ys -> xs ⊆ x :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

⊆-refl : {A : Set}{xs : List A} -> xs ⊆ xs
⊆-refl {A} {[]} = stop
⊆-refl {A} {x :: xs} = keep ⊆-refl

⊆-trans : {A : Set}{xs ys zs : List A} ->
          xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
⊆-trans stop q = q
⊆-trans p (drop q) = drop (⊆-trans p q)
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
⊆-trans (drop p) (keep q) = drop (⊆-trans p q)

-- infixr 30 _::_
data SubList {A : Set} : List A -> Set where
  [] : SubList []
  _::_ : ∀ x {xs} -> SubList xs -> SubList (x :: xs)
  skip : ∀ {x xs} -> SubList xs -> SubList (x :: xs)

-- Ex 2.3 (b)

forget : {A : Set} {xs : List A} -> SubList xs -> List A
forget [] = []
forget (x :: y) = x :: forget y
forget (skip y) = forget y

-- Ex 2.3 (c)

lem-forget : {A : Set} {xs : List A} (zs : SubList xs) -> forget zs ⊆ xs
lem-forget [] = stop
lem-forget (x :: xs) = keep (lem-forget xs)
lem-forget (skip xs) = drop (lem-forget xs)

-- Ex 2.3 (d)

data Bool : Set where
  true : Bool
  false : Bool

filter' : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
filter' p [] = []
filter' p (x :: xs) with p x
... | true = x :: filter' p xs
... | false = skip (filter' p xs)

-- Ex 2.3 (e)

complement : {A : Set} {xs : List A} -> SubList xs -> SubList xs
complement {A} {[]} _ = []
complement {A} {y :: y'} (.y :: y0) = skip (complement {A} {y'} y0)
complement {A} {y :: y'} (skip y0) = y :: complement {A} {y'} y0

_++_ : {A : Set} → List A → List A → List A
_++_ [] xs = xs
_++_ (x :: xs) ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) -> List A → List B
map f [] = []
map f (y :: y') = f y :: map f y'

-- Ex 2.3 (f) 
sublists : {A : Set}(xs : List A) → List (SubList xs)
sublists [] = [] :: []
sublists (y :: y') = let u = sublists y'
                     in (map skip u) ++ (map (_::_ y) u)

z : List (SubList (zero :: suc zero :: []))
z = sublists (zero :: suc zero :: [])

-- Conor's type checker

module lambda where
  
  infixl 30 _∈_
  data _∈_ {A : Set}(x : A) : List A -> Set where
    hd : forall {xs} -> x ∈ x :: xs
    tl : forall {y xs} -> x ∈ xs -> x ∈ y :: xs
  
  index : forall {A} {x : A} {xs} -> x ∈ xs -> Nat
  index hd = zero
  index (tl p) = suc (index p)

  length : {A : Set} -> List A -> Nat
  length [] = zero
  length (x :: xs) = suc (length xs)
  
  data Lookup {A : Set}(xs : List A) : Nat -> Set where
    inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
    outside : (m : Nat) -> Lookup xs (length xs + m)
  
  _!_ : {A : Set} (xs : List A) (n : Nat) -> Lookup xs n
  [] ! n = outside n
  (x :: xs) ! zero = inside x hd
  (x :: xs) ! suc n with xs ! n
  (x :: xs) ! suc .(index p) | inside y p = inside y (tl p)
  (x :: xs) ! suc .(length xs + n) | outside n = outside n
    
  infixr 30 _⟶_
  data Type : Set where
    ı : Type
    _⟶_ : Type → Type → Type

  infixl 80 _$_
  data Raw : Set where
    var : Nat → Raw
    _$_ : Raw → Raw → Raw
    lam : Type → Raw → Raw
  
  -- Ex 3.2 (a)

  data _≠_ : Type -> Type -> Set where
    ı≠⟶ : {σ τ : Type} → ı ≠ (σ ⟶ τ)
    ⟶≠ı : {σ τ : Type} → (σ ⟶ τ) ≠ ı
    ⟶≠⟶₁ : {σ₁ τ₁ σ₂ τ₂ : Type} → (σ₁ ≠ σ₂) → (σ₁ ⟶ τ₁) ≠ (σ₂ ⟶ τ₂)
    ⟶≠⟶₂ : {σ₁ τ₁ σ₂ τ₂ : Type} → (τ₁ ≠ τ₂) → (σ₁ ⟶ τ₁) ≠ (σ₂ ⟶ τ₂)

  data Equal? : Type -> Type -> Set where
    yes : ∀ {τ} -> Equal? τ τ
    no  : ∀ {σ τ} -> σ ≠ τ -> Equal? σ τ
  
  _=?=_ : (σ τ : Type) -> Equal? σ τ
  ı =?= ı = yes
  ı =?= (σ ⟶ τ) = no ı≠⟶
  (σ ⟶ τ) =?= ı = no ⟶≠ı
  (σ₁ ⟶ τ₁) =?= (σ₂ ⟶ τ₂) with σ₁ =?= σ₂
  (σ₁ ⟶ τ₁) =?= (σ₂ ⟶ τ₂) | no p = no (⟶≠⟶₁ p)
  (σ ⟶ τ₁) =?= (.σ ⟶ τ₂) | yes with τ₁ =?= τ₂
  (σ ⟶ τ₁) =?= (.σ ⟶ τ₂) | yes | no q = no (⟶≠⟶₂ q)
  (σ ⟶ τ) =?= (.σ ⟶ .τ) | yes | yes = yes

  Cxt = List Type
  data Term (Γ : Cxt) : Type -> Set where
    var : forall {τ} → τ ∈ Γ → Term Γ τ
    _$_ : forall {σ τ} -> Term Γ (σ ⟶ τ) -> Term Γ σ -> Term Γ τ
    lam : forall σ {τ} → Term (σ :: Γ) τ → Term Γ (σ ⟶ τ)
    

  erase : forall { Γ τ } -> Term Γ τ -> Raw
  erase (var x) = var (index x)
  erase (t $ u) = erase t $ erase u
  erase (lam σ t) = lam σ (erase t)
  
  -- Ex 3.2 (b)

  data BadTerm (Γ : Cxt) : Set where
    varBad : Nat → BadTerm Γ
    bad$τ : ∀ {τ} → BadTerm Γ → Term Γ τ → BadTerm Γ
    τ$bad : ∀ {τ} → Term Γ τ → BadTerm Γ → BadTerm Γ
    bad$bad : BadTerm Γ → BadTerm Γ → BadTerm Γ
    ı$τ : ∀ {τ} → Term Γ ı → Term Γ τ → BadTerm Γ
    ı$bad : ∀ {τ} → Term Γ τ → BadTerm Γ → BadTerm Γ
    lambad : ∀ σ → BadTerm (σ :: Γ) → BadTerm Γ
    mis$ : ∀ {σ₁ τ σ₂} → σ₁ ≠ σ₂ → Term Γ (σ₁ ⟶ τ) → Term Γ σ₂ → BadTerm Γ

  eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
  eraseBad (varBad x) = var x
  eraseBad (bad$τ t u) = eraseBad t $ erase u
  eraseBad (τ$bad t u) = erase t $ eraseBad u
  eraseBad (bad$bad t u) = eraseBad t $ eraseBad u
  eraseBad (ı$τ t u) = erase t $ erase u
  eraseBad (ı$bad t u) = erase t $ eraseBad u
  eraseBad (lambad σ y) = lam σ (eraseBad y)
  eraseBad (mis$ _ t u) = erase t $ erase u

  data Infer (Γ : Cxt) : Raw -> Set where
    ok : (τ : Type) (t : Term Γ τ ) -> Infer Γ (erase t)
    bad : (b : BadTerm Γ) -> Infer Γ (eraseBad b)  
  
  infer : (Γ : Cxt) (e : Raw) -> Infer Γ e
  infer Γ (var n) with Γ ! n
  infer Γ (var .(length Γ + n)) | outside n = bad (varBad (length Γ + n))
  infer Γ (var .(index x))      | inside σ x = ok σ (var x)
  infer Γ (e₁ $ e₂) with infer Γ e₁ | infer Γ e₂
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok ı t₁ | ok σ' t₂ = bad (ı$τ t₁ t₂)
  infer Γ (.(erase t₁) $ .(eraseBad t₂)) | ok ı t₁ | bad t₂ = bad (ı$bad t₁ t₂)
  infer Γ (.(erase t₁) $ .(eraseBad t₂)) | ok (σ ⟶ τ) t₁ | bad t₂ = bad (τ$bad t₁ t₂)
  infer Γ (.(eraseBad t₁) $ .(erase t₂)) | bad t₁ | ok σ' t₂ = bad (bad$τ t₁ t₂)
  infer Γ (.(eraseBad t₁) $ .(eraseBad t₂)) | bad t₁ | bad t₂ = bad (bad$bad t₁ t₂)
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⟶ τ) t₁ | ok σ' t₂ with σ =?= σ'
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⟶ τ) t₁ | ok σ' t₂ | no p = bad (mis$ p t₁ t₂)
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⟶ τ) t₁ | ok .σ t₂ | yes = ok τ (t₁ $ t₂)
  infer Γ (lam σ e) with infer (σ :: Γ) e
  infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⟶ τ) (lam σ t)
  infer Γ (lam σ .(eraseBad t)) | bad t = bad (lambad σ t)

  Γ : Cxt
  Γ = ı :: []
  e : Raw
  e = var zero
  f : Raw
  f = lam ı (var (suc zero))
  g : Raw
  g = f $ f
  a : Infer Γ g
  a = infer Γ g

module ex31 where

  -- 3.1 (a)
  data Compare : Nat -> Nat -> Set where
    less : forall {n} k -> Compare n (n + suc k)
    more : forall {n} k -> Compare (n + suc k) n
    same : forall {n} -> Compare n n

  -- 3.1 (b)
  compare : (n m : Nat) -> Compare n m
  compare zero zero = same
  compare zero (suc k) = less k
  compare (suc k) zero = more k
  compare (suc k) (suc l) with compare k l
  compare (suc k) (suc .(k + suc n)) | less n = less n
  compare (suc .(l + suc n)) (suc l) | more n = more n
  compare (suc k) (suc .k) | same = same

  difference : Nat -> Nat -> Nat
  difference n m with compare n m
  difference n .(n + suc k) | less k = suc k
  difference .(m + suc k) m | more k = suc k
  difference .m m | same = zero

  b = suc (suc (suc zero))
  c = suc zero
  u = difference b c
  v = difference c b
