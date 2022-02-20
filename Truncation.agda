module Truncation where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ₁ : Level
  
data Susp (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : A → north ≡ south

SuspF : {A : Type ℓ} {B : Type ℓ₁} → (A → B) → Susp A → Susp B
SuspF f north = north
SuspF f south = south
SuspF f (merid a i) = merid (f a) i

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data ⊥ : Type where

S : ℕ → Type
S 0 = ⊥
S (suc n) = Susp (S n)

data ⊤ : Type where
  ⋆ : ⊤

D : ℕ → Type
D 0 = ⊤
D (suc n) = Susp (D n)

S→D : {n : ℕ} → S n → D n
S→D {suc n} = SuspF S→D

data ∥_∥_ (A : Type ℓ) (n : ℕ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥ n
  hub : (f : S n → ∥ A ∥ n) (u : D n) → ∥ A ∥ n
  spoke : (f : S n → ∥ A ∥ n) (s : S n) → f s ≡ hub f (S→D s)

isOfHLevel : ℕ → Type ℓ → Type ℓ
isOfHLevel 0 A = A
isOfHLevel (suc n) A = (x y : A) → isOfHLevel n (x ≡ y)

sphereFill : (n : ℕ) (A : Type ℓ) (f : S n → A) → Type ℓ
sphereFill n A f = Σ (D n → A) (λ f' → (s : S n) → f s ≡ f' (S→D s))

isSphereFilled : ℕ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n A f

isSphereFilled∥∥ : (n : ℕ) (A : Type ℓ) → isSphereFilled n (∥ A ∥ n)
isSphereFilled∥∥ n A f = hub f , spoke f

isSphereFilledDesc : (n : ℕ) (A : Type ℓ)
  → isSphereFilled (suc n) A → (x y : A) → isSphereFilled n (x ≡ y)
isSphereFilledDesc n A h x y g = g' , r
  where
  f : S (suc n) → A
  f north = x
  f south = y
  f (merid u i) = g u i

  g' : D n → x ≡ y
  g' u i =
    hcomp
      (λ j →
        λ { (i = i0) → h f .snd north (~ j)
          ; (i = i1) → h f .snd south (~ j) })
      (h f .fst (merid u i))

  r : (s : S n) → g s ≡ g' (S→D s)
  r s i j =
    hcomp
      (λ k →
        λ { (i = i0) → g s j
          ; (j = i0) → h f .snd north (i ∧ ~ k)
          ; (j = i1) → h f .snd south (i ∧ ~ k) })
      (h f .snd (merid s j) i)

isSphereFilled→isOfHLevel : (n : ℕ) (A : Type ℓ)
  → isSphereFilled n A → isOfHLevel n A
isSphereFilled→isOfHLevel zero A h = h (λ ()) .fst ⋆
isSphereFilled→isOfHLevel (suc n) A h x y =
  isSphereFilled→isOfHLevel n (x ≡ y) (isSphereFilledDesc n A h x y)

isSphereFilledAsc : (n : ℕ) (A : Type ℓ)
  → ((x y : A) → isSphereFilled n (x ≡ y)) → isSphereFilled (suc n) A
isSphereFilledAsc n A h f = f' , r
  where
  g : S n → f north ≡ f south
  g s i = f (merid s i)
  
  f' : D (suc n) → A
  f' north = f north
  f' south = f south
  f' (merid u i) = h (f north) (f south) g .fst u i

  r : (s : S (suc n)) → f s ≡ f' (S→D s)
  r north = refl
  r south = refl
  r (merid s i) j = h (f north) (f south) g .snd s j i

isOfHLevel→isSphereFilled : (n : ℕ) (A : Type ℓ)
  → isOfHLevel n A → isSphereFilled n A
isOfHLevel→isSphereFilled 0 A h f = (λ _ → h) , λ ()
isOfHLevel→isSphereFilled (suc n) A h f =
  isSphereFilledAsc n A
    (λ x y → isOfHLevel→isSphereFilled n (x ≡ y) (h x y)) f

isOfHLevelTrunc : (n : ℕ) (A : Type ℓ) → isOfHLevel n (∥ A ∥ n)
isOfHLevelTrunc n A = isSphereFilled→isOfHLevel n (∥ A ∥ n) (isSphereFilled∥∥ n A)

rec : {n : ℕ} {A : Type ℓ} {B : Type ℓ₁}
  → isOfHLevel n B
  → (A → B) → ∥ A ∥ n → B
rec {n = n} {A = A} {B = B} hB g = helper
  where
  h : isSphereFilled n B
  h = isOfHLevel→isSphereFilled n B hB

  helper : ∥ A ∥ n → B
  helper ∣ x ∣ = g x
  helper (hub f u) = h (λ s → helper (f s)) .fst u
  helper (spoke f s i) = h (λ s → helper (f s)) .snd s i


sphereFillDep : (n : ℕ) (A : Type ℓ) (B : A → Type ℓ₁)
  (f₀' : D n → A)
  → ((s : S n) → B (f₀' (S→D s)))
  → Type _
sphereFillDep n A B f₀' f = Σ ((u : D n) → B (f₀' u)) (λ f' → (s : S n) → f s ≡ f' (S→D s))

isSphereFilledDep : ℕ → (A : Type ℓ) (B : A → Type ℓ₁) → Type _
isSphereFilledDep n A B =
  (f₀' : D n → A)
  (f : (s : S n) → B (f₀' (S→D s)))
  → sphereFillDep n A B f₀' f

isSphereFilledDepAsc : (n : ℕ) {A : Type ℓ} (B : A → Type ℓ₁)
  → ((x₀ y₀ : A) (x₁ : B x₀) (y₁ : B y₀) → isSphereFilledDep n (x₀ ≡ y₀) (λ p → PathP (λ i → B (p i)) x₁ y₁))
  → isSphereFilledDep (suc n) A B
isSphereFilledDepAsc n {A = A} B hB f₀' f = f' , r
  where
  g₀' : (u : D n) → f₀' north ≡ f₀' south 
  g₀' u i = f₀' (merid u i)

  g : (s : S n)  → PathP (λ i → B (g₀' (S→D s) i)) (f north) (f south)
  g s i = f (merid s i)

  f' : (u : D (suc n)) → B (f₀' u)
  f' north = f north
  f' south = f south
  f' (merid u i) = hB (f₀' north) (f₀' south) (f north) (f south) g₀' g .fst u i

  r : (s : S (suc n)) → f s ≡ f' (S→D s)
  r north = refl
  r south = refl
  r (merid s i) j = hB (f₀' north) (f₀' south) (f north) (f south) g₀' g .snd s j i

isOfHLevel→isSphereFilledDep : (n : ℕ) {A : Type ℓ} (B : A → Type ℓ₁)
  → ((a : A) → isOfHLevel n (B a)) → isSphereFilledDep n A B
isOfHLevel→isSphereFilledDep 0 B hB f₀' f = (λ u → hB (f₀' u)) , λ ()
isOfHLevel→isSphereFilledDep (suc n) {A = A} B hB =
  isSphereFilledDepAsc n B
    (λ x₀ y₀ x₁ y₁ →
      isOfHLevel→isSphereFilledDep n {A = x₀ ≡ y₀} (λ p → PathP (λ i → B (p i)) x₁ y₁)
        (λ p → J (λ y₀ p → (y₁ : B y₀) → isOfHLevel n (PathP (λ i → B (p i)) x₁ y₁)) (hB x₀ x₁) p y₁))

elim : {n : ℕ} {A : Type ℓ} {B : ∥ A ∥ n → Type ℓ₁}
  (hB : (x : ∥ A ∥ n) → isOfHLevel n (B x))
  (g : (a : A) → B (∣ a ∣)) (x : ∥ A ∥ n) → B x
elim {n = n} {A = A} {B = B} hB g = helper
  where
  h : isSphereFilledDep n (∥ A ∥ n) B
  h = isOfHLevel→isSphereFilledDep n B hB
  
  helper : (x : ∥ A ∥ n) → B x
  helper ∣ a ∣ = g a
  helper (hub f u) = h (hub f) (λ s → subst B (spoke f s) (helper (f s))) .fst u
  helper (spoke f s i) =
    hcomp
      (λ j →
        λ { (i = i0) → helper (f s)
          ; (i = i1) →  h (hub f) (λ s → subst B (spoke f s) (helper (f s))) .snd s j })
      (subst-filler B (spoke f s) (helper (f s)) i)
