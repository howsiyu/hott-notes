-- self-contained notes following https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html and relevant parts of HoTT book

open import Agda.Primitive public
  using (Level ; _⊔_)
  renaming (Set to Type ; lzero to 𝓾₀ ; lsuc to _⁺)

variable
  𝓁 𝓂 𝓃 : Level

Π : {X : Type 𝓁} (A : X → Type 𝓂) → Type (𝓁 ⊔ 𝓂)
Π A = (x : _) → A x

id : {X : Type 𝓁} → X → X
id x = x

_∘_ : {X : Type 𝓁} {Y : Type 𝓂} {Z : Y → Type 𝓃}
  → ((y : Y) → Z y) → (f : X → Y) → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

infixr 50 _∘_

data ⊥ : Type where

⊥-induction : (A : ⊥ → Type 𝓁) → Π A
⊥-induction A ()

data ⊤ : Type where
  ⋆ : ⊤

⊤-induction : (A : ⊤ → Type 𝓁) → A ⋆ → Π A
⊤-induction A a ⋆ = a

data _+_ (X : Type 𝓁) (Y : Type 𝓂) : Type (𝓁 ⊔ 𝓂)  where
  inl : X → X + Y
  inr : Y → X + Y

+-induction : {X : Type 𝓁} {Y : Type 𝓂} (A : X + Y → Type 𝓃)
  → ((x : X) → A (inl x))
  → ((y : Y) → A (inr y))
  → Π A
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

𝟚 : Type
𝟚 = ⊤ + ⊤

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

record Σ {X : Type 𝓁} (Y : X → Type 𝓂) : Type (𝓁 ⊔ 𝓂) where
  constructor _,_
  field
    fst : X
    snd : Y fst

open Σ

Σ-induction : {X : Type 𝓁} {Y : X → Type 𝓂} (A : Σ Y → Type 𝓃)
  → ((x : X) (y : Y x) → A (x , y))
  → Π A
Σ-induction A f (x , y) = f x y

_×_ : Type 𝓁 → Type 𝓂 → Type (𝓁 ⊔ 𝓂)
X × Y = Σ (λ (_ : X) → Y)


data Id (X : Type 𝓁) (x : X) : X → Type 𝓁 where
  refl : Id X x x

Id-induction : {X : Type 𝓁} {x : X} (A : (y : X) → Id X x y → Type 𝓂)
  → A x refl
  → (y : X) (p : Id X x y) → A y p
Id-induction A σ _ refl = σ

data Id2 (X : Type 𝓁) : X → X → Type 𝓁 where
  refl2 : (x : X) → Id2 X x x

Id2-induction : {X : Type 𝓁} (A : (x y : X) → Id2 X x y → Type 𝓂)
  → ((x : X) → A x x (refl2 x))
  → (x y : X) (p : Id2 X x y) → A x y p
Id2-induction A σ x x (refl2 x) = σ x

Id→Id2 : {X : Type 𝓁} → (x y : X) → Id X x y → Id2 X x y
Id→Id2 x x refl = refl2 x

Id2→Id : {X : Type 𝓁} → (x y : X) → Id2 X x y → Id X x y
Id2→Id x x (refl2 x) = refl

_≡_ : {X : Type 𝓁} (x y : X) → Type 𝓁
x ≡ y = Id _ x y

infix 1 _≡_

sym : {X : Type 𝓁} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

_∙_ : {X : Type 𝓁} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

_∙∙_∙∙_ : {X : Type 𝓁} {x y z t : X} → x ≡ y → y ≡ z → z ≡ t → x ≡ t
refl ∙∙ refl ∙∙ refl = refl

_≡⟨_⟩_ : {X : Type 𝓁 } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

infixr  0 _≡⟨_⟩_

_∎ : {X : Type 𝓁} (x : X) → x ≡ x
x ∎ = refl

infix 1 _∎

transport : {X Y : Type 𝓁} → X ≡ Y → X → Y
transport refl x = x

subst : {X : Type 𝓁} (A : X → Type 𝓂) {x y : X} → x ≡ y → A x → A y
subst A refl ax = ax

module _ {X : Type 𝓁} {x : X} where
  refl-left : {y : X} (p : x ≡ y) → refl ∙ p ≡ p
  refl-left refl = refl

  refl-right : {y : X} (p : x ≡ y) → p ∙ refl ≡ p
  refl-right refl = refl

  ∙-assoc : {y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
    → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
  ∙-assoc refl refl refl = refl

  sym-left : {y : X} (p : x ≡ y) → sym p ∙ p ≡ refl
  sym-left refl = refl

  sym-right : {y : X} (p : x ≡ y) → p ∙ sym p ≡ refl
  sym-right refl = refl

  sym-involutive : {y : X} (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl

∙-cancel-left : {X : Type 𝓁} {x y z : X} {p : x ≡ y} {q r : y ≡ z}
  → p ∙ q ≡ p ∙ r → q ≡ r
∙-cancel-left {p = refl} {q = q} {r = r} s =
  sym (refl-left q) ∙∙ s ∙∙ refl-left r

∙-cancel-right : {X : Type 𝓁} {x y z : X} {p q : x ≡ y} {r : y ≡ z}
  → p ∙ r ≡ q ∙ r → p ≡ q
∙-cancel-right {p = p} {q = q} {r = refl} s =
  sym (refl-right p) ∙∙ s ∙∙ refl-right q

module _ {X : Type 𝓁} {Y : Type 𝓂} (f : X → Y) where
  cong : {x y : X} → x ≡ y → f x ≡ f y
  cong refl = refl

  cong-refl : (x : X) → cong (refl {x = x}) ≡ refl
  cong-refl x = refl

  cong-sym : {x y : X} → (p : x ≡ y) → cong (sym p) ≡ sym (cong p)
  cong-sym refl = refl
  
  cong-∙ : {x y z : X} (p : x ≡ y) (q : y ≡ z)
    → cong (p ∙ q) ≡ cong p ∙ cong q
  cong-∙ refl refl = refl

cong-id : {X : Type 𝓁} {x y : X} (p : x ≡ y) → cong id p ≡ p
cong-id refl = refl

cong-∘ : {X : Type 𝓁} {Y : Type 𝓂} {Z : Type 𝓃}
  (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
  → cong (g ∘ f) p ≡ cong g (cong f p)
cong-∘ f g refl = refl
  
congd : {X : Type 𝓁} {Y : X → Type 𝓂} (f : Π Y) {x y : X} (p : x ≡ y)
  → subst Y p (f x) ≡ f y
congd f refl = refl

cong₂ : {X : Type 𝓁} {Y : Type 𝓂} {Z : Type 𝓃} (f : X → Y → Z)
  {x x' : X} → x ≡ x' → {y y' : Y} → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

¬_ : Type 𝓁 → Type 𝓁
¬ A = A → ⊥

contrapositive : {X : Type 𝓁} {Y : Type 𝓂} → (X → Y) → ¬ Y → ¬ X
contrapositive f p x = p (f x)

decidable : Type 𝓁 → Type 𝓁
decidable A = A + (¬ A)

onAllPaths : (Type 𝓁 → Type 𝓁) → Type 𝓁 → Type 𝓁
onAllPaths A X = (x y : X) → A (x ≡ y)

discrete : Type 𝓁 → Type 𝓁
discrete = onAllPaths decidable

₁≢₀ : ¬ (₁ ≡ ₀)
₁≢₀ p = subst (λ { ₀ → ⊥ ; ₁ → ⊤ }) p ⋆

𝟚-is-discrete : discrete 𝟚
𝟚-is-discrete ₀ ₀ = inl refl
𝟚-is-discrete ₀ ₁ = inr (contrapositive sym ₁≢₀)
𝟚-is-discrete ₁ ₀ = inr ₁≢₀
𝟚-is-discrete ₁ ₁ = inl refl

isCenter : (X : Type 𝓁) → X → Type 𝓁
isCenter X x = (y : X) → x ≡ y

isContr : (X : Type 𝓁) → Type 𝓁
isContr X = Σ (isCenter X) 

⊤-is-contr : isContr ⊤
⊤-is-contr = ⋆ , λ { ⋆ → refl }

surrounding : {X : Type 𝓁} (x : X) → Type 𝓁
surrounding x = Σ λ y → x ≡ y

surrounding-is-contr : {X : Type 𝓁} (x : X) → isContr (surrounding x)
surrounding-is-contr x = (x , refl) ,  λ { (.x , refl) → refl }

isProp : (X : Type 𝓁) → Type 𝓁
isProp X = Π (isCenter X)

⊥-is-prop : isProp ⊥
⊥-is-prop ()

⊤-is-prop : isProp ⊤
⊤-is-prop ⋆ ⋆ = refl

isContr→isProp : {X : Type 𝓁} → isContr X → isProp X
isContr→isProp (c , φ) x y = sym (φ x) ∙ φ y

no-unicorns : (X : Type 𝓁) → isProp X → ¬ (isContr X) → ¬ ¬ X → ⊥
no-unicorns X φ ns ne = ne empty where
  empty : ¬ X
  empty x = ns (x , φ x)


isSet : (X : Type 𝓁) → Type 𝓁
isSet = onAllPaths isProp

⊥-is-set : isSet ⊥
⊥-is-set ()

⊤-is-set : isSet ⊤
⊤-is-set ⋆ ⋆ refl refl = refl

⊤-is-set' : isSet ⊤
⊤-is-set' =
  ⊤-induction
    (λ x → (z : ⊤) → isProp (x ≡ z))
    (Id-induction
      (λ y → isCenter (⋆ ≡ y))
      (Id-induction
        refl-eq
        refl
        ⋆))
  where
  refl-eq : (x : ⊤) → ⋆ ≡ x → Type
  refl-eq =
    ⊤-induction
      (λ x → ⋆ ≡ x → Type)
      (Id (⋆ ≡ ⋆) refl)


wconstant : {X : Type 𝓁} {Y : Type 𝓂} → (X → Y) → Type (𝓁 ⊔ 𝓂)
wconstant {X = X} f = (x y : X) → f x ≡ f y

endo : Type 𝓁 → Type 𝓁
endo X = X → X

wconstant-endo : Type 𝓁 → Type 𝓁
wconstant-endo X = Σ λ (f : endo X) → wconstant f

Hedberg : {X : Type 𝓁} (x : X)
  → ((y : X) → wconstant-endo (x ≡ y))
  → (y : X) → isProp (x ≡ y)
Hedberg {X = X} x c y p q =
  p
  ≡⟨ sym (a y p) ⟩
  sym (f x refl) ∙ f y p
  ≡⟨ cong (λ r → sym (f x refl) ∙ r) (c y .snd p q) ⟩
  sym (f x refl) ∙ f y q
  ≡⟨ a y q ⟩
  q ∎
  where
  f : (z : X) → endo (x ≡ z)
  f z = c z .fst

  a : (z : X) (r : x ≡ z) → sym (f x refl) ∙ f z r ≡ r
  a x refl = sym-left (f x refl)

isProp→wconstant-endos : {X : Type 𝓁}
  → isProp X → onAllPaths wconstant-endo X
isProp→wconstant-endos φ x y = (λ _ → φ x y) , (λ _ _ → refl)

isSet→wconstant-endos : {X : Type 𝓁}
  → isSet X → onAllPaths wconstant-endo X
isSet→wconstant-endos φ x y = id , φ x y

wconstant-endos→isSet : {X : Type 𝓁}
  → onAllPaths wconstant-endo X → isSet X
wconstant-endos→isSet c x = Hedberg x (c x)

isProp→isSet : {X : Type 𝓁} → isProp X → isSet X
isProp→isSet = wconstant-endos→isSet ∘ isProp→wconstant-endos

pointed→wconstant-endo : {X : Type 𝓁} → X → wconstant-endo X
pointed→wconstant-endo x = (λ _ → x) , (λ _ _ → refl)

empty→wconstant-endo : {X : Type 𝓁} → ¬ X → wconstant-endo X
empty→wconstant-endo e = id , λ x → ⊥-induction _ (e x)

decidable→wconstant-endo : {X : Type 𝓁} → decidable X → wconstant-endo X
decidable→wconstant-endo (inl x) = pointed→wconstant-endo x
decidable→wconstant-endo (inr e) = empty→wconstant-endo e

discrete→wconstant-endos : {X : Type 𝓁}
  → discrete X → onAllPaths wconstant-endo X
discrete→wconstant-endos φ x y = decidable→wconstant-endo (φ x y)

discrete→isSet : {X : Type 𝓁} → discrete X → isSet X
discrete→isSet = wconstant-endos→isSet ∘ discrete→wconstant-endos

isContrΣ : {X : Type 𝓁} {Y : X → Type 𝓂}
  → isContr X → ((x : X) → isContr (Y x))
  → isContr (Σ Y)
isContrΣ {X = X} {Y = Y} (x₀ , c) cy =
  (x₀ , cy x₀ .fst) , λ { (x , y) → f (c x) (cy x .snd y) } 
  where
  f : {x : X} {y : Y x} → x₀ ≡ x → cy x .fst ≡ y → (x₀ , cy x₀ .fst) ≡ (x , y)
  f refl refl = refl

isPropΣ : {X : Type 𝓁} {Y : X → Type 𝓂}
  → isProp X → ((x : X) → isProp (Y x))
  → isProp (Σ Y)
isPropΣ {X = X} {Y = Y} φ ψ (x₀ , y₀) (x₁ , y₁) =
  f (φ x₀ x₁) (ψ x₁ (subst Y (φ x₀ x₁) y₀) y₁)
  where
  f : {x : X} {y : Y x} → (p : x₀ ≡ x) → subst Y p y₀ ≡ y → (x₀ , y₀) ≡ (x , y)
  f refl refl = refl

_∼_ : {X : Type 𝓁} {Y : X → Type 𝓂} (f g : Π Y) → Type (𝓁 ⊔ 𝓂)
f ∼ g = (x : _) → f x ≡ g x

infix 2 _∼_

deformation-induces-natural-iso : {X : Type 𝓁}
  {f : X → X} (H : f ∼ id)
  {x y : X} (p : x ≡ y)
  → H x ∙ p ≡ cong f p ∙ H y
deformation-induces-natural-iso H {x = x} refl =
  refl-right (H x) ∙ sym (refl-left (H x))

deformation-induces-iso : {X : Type 𝓁} (f : X → X) (H : f ∼ id)
  (x : X) → H (f x) ≡ cong f (H x)
deformation-induces-iso f H x =
 ∙-cancel-right (deformation-induces-natural-iso H (H x))
  
retraction : {X : Type 𝓁} {Y : Type 𝓂} → (X → Y) → Type (𝓁 ⊔ 𝓂)
retraction f = Σ λ g → g ∘ f ∼ id

section : {X : Type 𝓁} {Y : Type 𝓂} → (X → Y) → Type (𝓁 ⊔ 𝓂)
section f = Σ λ h → f ∘ h ∼ id

_◁_ : Type 𝓁 → Type 𝓂 → Type (𝓁 ⊔ 𝓂)
X ◁ Y = Σ λ (r : Y → X) → section r

isContrRetract : {X : Type 𝓁} {Y : Type 𝓂}
  → Y ◁ X → isContr X → isContr Y
isContrRetract {Y = Y} (r , (s , η)) (c , φ) = r c , d
  where
  d : isCenter Y (r c)
  d y = r c ≡⟨ cong r (φ (s y)) ⟩ r (s y) ≡⟨ η y ⟩ y ∎

isPropRetract : {X : Type 𝓁} {Y : Type 𝓂}
  → Y ◁ X → isProp X → isProp Y
isPropRetract {Y = Y} (r , (s , η)) φ y₀ y₁ =
  y₀
  ≡⟨ sym (η y₀) ⟩
  r (s y₀)
  ≡⟨ cong r (φ (s y₀) (s y₁)) ⟩
  r (s y₁)
  ≡⟨ η y₁ ⟩
  y₁ ∎

Σ-retract : {X : Type 𝓁} (A : X → Type 𝓂) (B : X → Type 𝓃)
  → ((x : X) → A x ◁ B x) → Σ A ◁ Σ B
Σ-retract A B ρ = r , (s , η)
  where
  r : Σ B → Σ A
  r (x , b) = x , (ρ x .fst b)

  s : Σ A → Σ B
  s (x , a) = x , ρ x .snd .fst a

  η : r ∘ s ∼ id
  η (x , a) = cong (_,_ x) (ρ x .snd .snd a)

subst-is-retraction : {X : Type 𝓁} (A : X → Type 𝓂) {x y : X} (p : x ≡ y)
  → subst A p ∘ subst A (sym p) ∼ id
subst-is-retraction A refl ay = refl

subst-is-section : {X : Type 𝓁} (A : X → Type 𝓂) {x y : X} (p : x ≡ y)
  → subst A (sym p) ∘ subst A p ∼ id
subst-is-section A refl ax = refl

module _ {X : Type 𝓁} {A : X → Type 𝓃} where
  to-Σ≡ : {σ τ : Σ A}
    →  Σ (λ (p : σ .fst ≡ τ .fst) → subst A p (σ .snd) ≡ τ .snd)
    → σ ≡ τ
  to-Σ≡ (refl , refl) = refl

  from-Σ≡ : {σ τ : Σ A}
    → σ ≡ τ
    →  Σ (λ (p : σ .fst ≡ τ .fst) → subst A p (σ .snd) ≡ τ .snd)
  from-Σ≡ refl = (refl , refl)

  to-Σ≡-is-retraction :  {σ τ : Σ A} → to-Σ≡ {σ} {τ} ∘ from-Σ≡ {σ} {τ} ∼ id
  to-Σ≡-is-retraction refl = refl

  to-Σ≡-is-section :  {σ τ : Σ A} → from-Σ≡ {σ} {τ} ∘ to-Σ≡ {σ} {τ} ∼ id
  to-Σ≡-is-section (refl , refl) = refl

  isSetΣ : isSet X → ((x : X) → isSet (A x)) → isSet (Σ A)
  isSetΣ φ ψ (x₀ , y₀) (x₁ , y₁) =
    isPropRetract
      (to-Σ≡ , (from-Σ≡ , to-Σ≡-is-retraction))
      (isPropΣ (φ x₀ x₁) (λ x → ψ x₁ (subst A x y₀) y₁))

Σ-reindexing-retract : {X : Type 𝓁} {Y : Type 𝓂} (A : X → Type 𝓃) (r : Y → X)
  → section r
  → Σ A ◁ Σ (A ∘ r)
Σ-reindexing-retract A r (s , η) = r' , (s' , η')
  where
  r' : Σ (A ∘ r) → Σ A
  r' (y , a) = r y , a

  s' : Σ A → Σ (A ∘ r)
  s' (x , a) = s x , subst A (sym (η x)) a

  η' : r' ∘ s' ∼ id
  η' (x , a) = to-Σ≡ (η x , subst-is-retraction A (η x) a)

module Equiv {X : Type 𝓁} {Y : Type 𝓂} (f : X → Y) where
  fiber : Y → Type (𝓁 ⊔ 𝓂)
  fiber y = Σ λ x → f x ≡ y
  
  isEquiv : Type (𝓁 ⊔ 𝓂)
  isEquiv = (y : Y) → isContr (fiber y)
  
  inverse : isEquiv → Y → X
  inverse eq y = eq y .fst .fst

  inverse-is-section : (eq : isEquiv) → f ∘ inverse eq ∼ id
  inverse-is-section eq y = eq y .fst .snd

  inverse-is-retraction : (eq : isEquiv) → inverse eq ∘ f ∼ id
  inverse-is-retraction eq x = cong fst p where
    p : Id (fiber (f x)) (eq (f x) .fst) (x , refl)
    p = eq (f x) .snd (x , refl)

  isInvertible : Type (𝓁 ⊔ 𝓂)
  isInvertible = retraction f × section f

  isEquiv→isInvertible : isEquiv → isInvertible
  isEquiv→isInvertible eq =
    (inverse eq , inverse-is-retraction eq)
    , (inverse eq , inverse-is-section eq)

  toFiberEq : {y : Y} {σ : fiber y} (τ : fiber y)
    →  Σ (λ (γ : σ .fst ≡ τ .fst) → (cong f γ ∙ τ .snd ≡ σ .snd))
    → σ ≡ τ
  toFiberEq τ (refl , refl) = cong (λ p → (τ .fst , p)) (refl-left (τ .snd))

  record isHAEquiv : Type (𝓁 ⊔ 𝓂) where
    field
      g : Y → X
      η : g ∘ f ∼ id
      ε : f ∘ g ∼ id
      ha : (x : X) → cong f (η x) ≡ ε (f x)

  open isHAEquiv
  
  isHAEquiv→isInvertible : isHAEquiv → isInvertible
  isHAEquiv→isInvertible eq = (eq .g , eq .η) , (eq .g , eq .ε)

  isInvertible→isHAEquiv : isInvertible → isHAEquiv
  isInvertible→isHAEquiv ((g₀ , η₀) , (h₀ , ε₀)) = record {
      g = g₀
      ; η = η₀
      ; ε = ε₂
      ; ha = λ x → sym (ha₀ x)
    } where
    ε₁ : f ∘ g₀ ∼ id
    ε₁ y = sym (cong (f ∘ g₀) (ε₀ y)) ∙ (cong f (η₀ (h₀ y)) ∙ ε₀ y)

    ε₂ : f ∘ g₀ ∼ id
    ε₂ y = sym (ε₁ (f (g₀ y))) ∙ (cong f (η₀ (g₀ y)) ∙ ε₁ y)

    ha₀ : (x : X) →  ε₂ (f x) ≡ cong f (η₀ x)
    ha₀ x =
      sym (ε₁ (f (g₀ (f x)))) ∙ (cong f (η₀ (g₀ (f x))) ∙ ε₁ (f x))
      ≡⟨ cong (λ p → sym (ε₁ (f (g₀ (f x)))) ∙ p)
        (
          cong f (η₀ (g₀ (f x))) ∙ ε₁ (f x)
          ≡⟨ cong (λ p → cong f p ∙ ε₁ (f x))
            (deformation-induces-iso (g₀ ∘ f) η₀ x) ⟩
          cong f (cong (g₀ ∘ f) (η₀ x)) ∙ ε₁ (f x)
          ≡⟨ cong (λ p → p ∙ ε₁ (f x))
            (
              cong f (cong (g₀ ∘ f) (η₀ x))
              ≡⟨ sym (cong-∘ (g₀ ∘ f) f (η₀ x)) ⟩
              cong (f ∘ g₀ ∘ f) (η₀ x)
              ≡⟨ cong-∘ f (f ∘ g₀) (η₀ x) ⟩
              cong (f ∘ g₀) (cong f (η₀ x)) ∎ ) ⟩
          cong (f ∘ g₀) (cong f (η₀ x)) ∙ ε₁ (f x)
          ≡⟨ sym (deformation-induces-natural-iso ε₁ (cong f (η₀ x))) ⟩
          ε₁ (f (g₀ (f x))) ∙ cong f (η₀ x) ∎ )
      ⟩
      sym (ε₁ (f (g₀ (f x)))) ∙ (ε₁ (f (g₀ (f x))) ∙ cong f (η₀ x))
      ≡⟨ sym (∙-assoc _ _ _) ⟩
      (sym (ε₁ (f (g₀ (f x)))) ∙ ε₁ (f (g₀ (f x)))) ∙ cong f (η₀ x)
      ≡⟨  cong (λ p → p ∙ cong f (η₀ x)) (sym-left _) ⟩
      refl ∙ cong f (η₀ x)
      ≡⟨ refl-left _ ⟩
      cong f (η₀ x) ∎

  isHAEquiv→isEquiv : isHAEquiv → isEquiv
  isHAEquiv→isEquiv eq y =
    (eq .g y , eq .ε y)
    , λ τ → toFiberEq τ (γ τ , lem τ)
    where
    γ : (τ : fiber y) → eq .g y ≡ τ .fst
    γ (x , p) = cong (eq .g) (sym p) ∙ eq .η x

    natural : {h : Y → Y} (e : h ∼ id) {z z' : Y} (q : z ≡ z')
      → (sym (cong h q) ∙ e z) ∙ q ≡ e z'
    natural e {z = z} refl  = refl-right (refl ∙ e z) ∙ refl-left (e z)

    lem : (τ : fiber y) → cong f (γ τ) ∙ τ .snd ≡ eq .ε y
    lem (x , p) =
       cong f (cong (eq .g) (sym p) ∙ eq .η x) ∙ p
       ≡⟨ cong (λ q → q ∙ p) 
         (
           cong f (cong (eq .g) (sym p) ∙ eq .η x)
           ≡⟨ cong-∙ f (cong (eq .g) (sym p)) (eq .η x) ⟩
           cong f (cong (eq .g) (sym p)) ∙ cong f (eq .η x)
           ≡⟨ cong₂ _∙_
              (sym (cong-∘ (eq .g) f (sym p)) ∙ cong-sym (f ∘ eq .g) p)
              (eq .ha x) ⟩
           sym (cong (f ∘ eq .g) p) ∙ eq .ε (f x) ∎ ) ⟩
       (sym (cong (f ∘ eq .g) p) ∙ eq .ε (f x)) ∙ p
       ≡⟨ natural (eq .ε) p ⟩
       eq .ε y ∎

open Equiv
open isHAEquiv

_≃_ : Type 𝓁 → Type 𝓂 → Type (𝓁 ⊔ 𝓂)
X ≃ Y = Σ λ (f : (X → Y)) → isHAEquiv f

idIsHAEquiv : (X : Type 𝓁) → isHAEquiv (id {X = X})
idIsHAEquiv X = record {
  g = id
  ; η = λ x → refl
  ; ε = λ x → refl
  ; ha = λ x → refl }

id-≃ : (X : Type 𝓁) → X ≃ X
id-≃ X = (id , idIsHAEquiv X)

∘-≃ : {X : Type 𝓁} {Y : Type 𝓂} {Z : Type 𝓃} → X ≃ Y → Y ≃ Z → X ≃ Z
∘-≃ {X = X} {Y = Y} {Z = Z} (f , eqf) (h , eqh) =
  (h ∘ f)
  , record { g = g₀ ; η = η₀ ; ε = ε₀ ; ha = ha₀ }
  where
  g₀ : Z → X
  g₀ = eqf .g ∘ eqh .g

  η₀ : g₀ ∘ (h ∘ f) ∼ id
  η₀ x = cong (eqf .g) (eqh .η (f x)) ∙ eqf .η x

  ε₀ : (h ∘ f) ∘ g₀ ∼ id
  ε₀ z = cong h (eqf .ε (eqh .g z)) ∙ eqh .ε z

  ha₀ : (x : X) → cong (h ∘ f) (η₀ x) ≡ ε₀ (h (f x))
  ha₀ x =
    cong (h ∘ f) (cong (eqf .g) (eqh .η (f x)) ∙ eqf .η x)
    ≡⟨ cong-∙ (h ∘ f) _ _ ⟩
    cong (h ∘ f) (cong (eqf .g) (eqh .η (f x))) ∙ cong (h ∘ f) (eqf .η x)
    ≡⟨ cong₂ _∙_
       (sym (cong-∘ (eqf .g) (h ∘ f) (eqh .η (f x))))
       (cong-∘ f h (eqf .η x)) ⟩
    cong (h ∘ f ∘ eqf .g) (eqh .η (f x)) ∙ cong h (cong f (eqf .η x))
    ≡⟨ cong₂ _∙_
       (cong-∘ (f ∘ eqf .g) h (eqh .η (f x)))
       (cong (cong h) (eqf .ha x)) ⟩
    cong h (cong (f ∘ eqf .g) (eqh .η (f x))) ∙ cong h (eqf .ε (f x))
    ≡⟨ sym (cong-∙ h _ _) ⟩
    cong h (cong (f ∘ eqf .g) (eqh .η (f x)) ∙ eqf .ε (f x))
    ≡⟨ cong (cong h) (sym (deformation-induces-natural-iso (eqf .ε) (eqh .η (f x)))) ⟩
    cong h (eqf .ε (eqh .g (h (f x))) ∙ eqh .η (f x))
    ≡⟨ cong-∙ h _ _ ⟩
    cong h (eqf .ε (eqh .g (h (f x)))) ∙ cong h (eqh .η (f x))
    ≡⟨ cong (λ p → _ ∙ p) (eqh .ha (f x)) ⟩
    cong h (eqf .ε (eqh .g (h (f x)))) ∙ eqh .ε (h (f x)) ∎

sym-≃ : {X : Type 𝓁} {Y : Type 𝓂} → X ≃ Y → Y ≃ X
sym-≃ {X = X} {Y = Y} (f , eq) =
  eq .g , record { g = f ; η = eq .ε ; ε = eq .η ; ha = ha₀ }
  where
  p : (y : Y)
    → cong (eq .g ∘ f ∘ eq .g) (eq .ε y) ∙ eq .η (eq .g y)
    ≡ cong (eq .g ∘ f ∘ eq .g) (eq .ε y) ∙ cong (eq .g) (eq .ε y)
  p y =
    cong (eq .g ∘ f ∘ eq .g) (eq .ε y) ∙ eq .η (eq .g y)
    ≡⟨ cong (λ p → p ∙ _) (cong-∘ (eq .g) (eq .g ∘ f) (eq .ε y)) ⟩
    cong (eq .g ∘ f) (cong (eq .g) (eq .ε y)) ∙ eq .η (eq .g y)
    ≡⟨ sym (deformation-induces-natural-iso (eq .η) (cong (eq .g) (eq .ε y))) ⟩
    eq .η (eq .g (f (eq .g y))) ∙ cong (eq .g) (eq .ε y)
    ≡⟨ cong (λ p → p ∙ _) (deformation-induces-iso (eq .g ∘ f) (eq .η) (eq .g y)) ⟩
    cong (eq .g ∘ f) (eq .η (eq .g y)) ∙ cong (eq .g) (eq .ε y)
    ≡⟨ cong (λ p → p ∙ cong (eq .g) (eq .ε y)) (cong-∘ f (eq .g) (eq .η (eq .g y))) ⟩
    cong (eq .g) (cong f (eq .η (eq .g y))) ∙ cong (eq .g) (eq .ε y)
    ≡⟨ cong (λ p → cong (eq .g) p ∙ cong (eq .g) (eq .ε y)) (eq .ha (eq .g y)) ⟩
    cong (eq .g) (eq .ε (f (eq .g y))) ∙ cong (eq .g) (eq .ε y)
    ≡⟨ sym (cong-∙ (eq .g) (eq .ε (f (eq .g y))) (eq .ε y)) ⟩
    cong (eq .g) (eq .ε (f (eq .g y)) ∙ eq .ε y)
    ≡⟨ cong (cong (eq .g)) (deformation-induces-natural-iso (eq .ε) (eq .ε y)) ⟩
    cong (eq .g) (cong (f ∘ eq .g) (eq .ε y) ∙ eq .ε y)
    ≡⟨ cong-∙ (eq .g) (cong (f ∘ eq .g) (eq .ε y)) (eq .ε y) ⟩
    cong (eq .g) (cong (f ∘ eq .g) (eq .ε y)) ∙ cong (eq .g) (eq .ε y)
    ≡⟨ cong (λ p → p ∙ cong (eq .g) (eq .ε y)) (sym (cong-∘ (f ∘ eq .g) (eq .g) (eq .ε y))) ⟩
    cong (eq .g ∘ f ∘ eq .g) (eq .ε y) ∙ cong (eq .g) (eq .ε y) ∎

  ha₀ :  (y : Y) → cong (eq .g) (eq .ε y) ≡ eq .η (eq .g y)
  ha₀ y = ∙-cancel-left (sym (p y))

cong-const : {X : Type 𝓁} {Y : Type 𝓂} (y : Y) {x x' : X} {p : x ≡ x'}
  → cong (λ _ → y) p ≡ refl
cong-const y {p = refl} = refl

contr-fiber : {X : Type 𝓁} (A : X → Type 𝓂) → ((x : X) → isContr (A x))
  → isHAEquiv (λ (a : Σ A) → a .fst)
contr-fiber {X = X} A c = record { g = g₀ ; η = η₀ ; ε = ε₀ ; ha = ha₀ }
  where
  g₀ : X → Σ A
  g₀ x = x , c x .fst

  η₀ : g₀ ∘ fst ∼ id
  η₀ (x , a) = cong (_,_ x) (c x .snd a)

  ε₀ : fst ∘ g₀ ∼ id
  ε₀ x = refl

  ha₀ : (a : Σ A) → cong fst (η₀ a) ≡ ε₀ (fst a)
  ha₀ (x , a) = cong fst (cong (_,_ x) (c x .snd a))
    ≡⟨ sym (cong-∘ (_,_ x) fst (c x .snd a)) ⟩
    cong (λ _ → x) (c x .snd a)
    ≡⟨ cong-const x ⟩
    refl
    ≡⟨ refl ⟩
    ε₀ x ∎

Id→Eq : (X Y : Type 𝓁) → X ≡ Y → X ≃ Y
Id→Eq X X refl = id-≃ X

isUnivalent : (𝓁 : Level) → Type (𝓁 ⁺)
isUnivalent 𝓁 = (X Y : Type 𝓁) → isHAEquiv (Id→Eq X Y)

