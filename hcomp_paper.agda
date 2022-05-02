-- Following A CUBICAL TYPE THEORY FOR HIGHER INDUCTIVE TYPES
-- by Simon Huber at https://simhu.github.io/misc/hcomp.pdf
-- as closely as possible.

open import Cubical.Core.Primitives
open import Cubical.Core.Glue
import Agda.Builtin.Cubical.HCompU as HCompU
open HCompU using (primFaceForall)
open HCompU.Helpers using (refl)

private
  variable
    ℓ ℓ₁ : Level
    ℓ′ ℓ₁′ : I → Level


-- Section 2 : New Primitives

-- This is just a special case of transp where φ = i0. I include it as it
-- has a far simpler type.
transport : (A : ∀ i → Type (ℓ′ i)) → A i0 → A i1
transport A u₀ = transp A i0 u₀

transp' :
  (φ : I)
  {ℓ' : I → Level [ φ ↦ (λ _ → ℓ) ]}
  {a : PartialP φ (λ _ → Type ℓ)}
  (A : (i : I) → Type (outS (ℓ' i)) [ φ ↦ (λ { (φ = i1) → a 1=1 }) ])
  (u₀ : outS (A i0))
  → outS (A i1) [ φ ↦ (λ { (φ = i1) → u₀ }) ]
transp' φ A u₀ = inS (transp (λ i → outS (A i)) φ u₀)

transportFill :
  (A : ∀ i → Type (ℓ′ i))
  (u₀ : A i0)
  (i : I)
  → A i
transportFill A u₀ i = transp (λ j → A (i ∧ j)) (~ i) u₀

-- Note that I fix the universe of A to make the type simpler. From now on we
-- are going to do that for all code involving transp where φ is not just i0.
transpFill :
  (φ : I)
  {a : Partial φ (Type ℓ)}
  (A : I → Type ℓ [ φ ↦ a ])
  (u₀ : outS (A i0))
  (i : I)
  → outS (A i)
transpFill φ A u₀ i = transp (λ j → outS (A (i ∧ j))) (φ ∨ ~ i) u₀


forward :
  (A : ∀ i → Type (ℓ′ i))
  (r : I)
  (u : A r)
  → A i1
forward A r u = transp (λ i → A (i ∨ r)) r u


hcomp' :
  {A : Type ℓ}
  {φ : I}
  (u : ∀ i → Partial φ A)
  (u₀ : A [ φ ↦ u i0 ])
  → A [ φ ↦ u i1 ]
hcomp' u u₀ = inS (hcomp u (outS u₀))


module Comp
  (A : ∀ i → Type (ℓ′ i))
  {φ : I}
  (u : ∀ i → Partial φ (A i))
  (u₀ : A i0 [ φ ↦ u i0 ])
  where
  comp' : A i1 [ φ ↦ u i1 ]
  comp' =
    inS
      (hcomp
        (λ i o → forward A i (u i o))
        (forward A i0 (outS u₀)))

  compId : comp A {φ = φ} u (outS u₀) ≡ outS comp'
  compId = refl


-- Section 3 : Recursive definition of transport

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

transpZeroId : (φ : I) → transp (λ _ → ℕ) φ zero ≡ zero
transpZeroId φ = refl

transpSucId : (φ : I) (u₀ : ℕ)
  → transp (λ _ → ℕ) φ (suc u₀) ≡ suc (transp (λ _ → ℕ) φ u₀)
transpSucId φ u₀ = refl

transpℕId : (φ : I) (u₀ : ℕ) → transp (λ _ → ℕ) φ u₀ ≡ u₀
transpℕId φ u₀ = refl


transportPathPId :
  (A : (i j : I) → Type (ℓ′ i))
  (v : (i : I) → A i i0)
  (w : (i : I) → A i i1)
  (u₀ : PathP (A i0) (v i0) (w i0))
  → transport (λ i → PathP (A i) (v i) (w i)) u₀
    ≡ λ j → comp
        (λ i → A i j)
        (λ i → λ
          { (j = i0) → v i
          ; (j = i1) → w i })
        (u₀ j)
transportPathPId A v w u₀ = refl

transpPathPId :
  (φ : I)
  {a : I → Partial φ (Type ℓ)}
  (A : (i j : I) → Type ℓ [ φ ↦ a j ])
  {vφ : PartialP φ (a i0)}
  (v : (i : I) → outS (A i i0) [ φ ↦ (λ { (φ = i1) → vφ 1=1 }) ])
  {wφ : PartialP φ (a i1)}
  (w : (i : I) → outS (A i i1) [ φ ↦ (λ { (φ = i1) → wφ 1=1 }) ])
  (u₀ : PathP (λ j → outS (A i0 j)) (outS (v i0)) (outS (w i0)))
  → transp (λ i → PathP (λ j → outS (A i j)) (outS (v i)) (outS (w i))) φ u₀
    ≡ λ j → comp
        (λ i → outS (A i j))
        (λ i → λ
          { (φ = i1) → u₀ j
          ; (j = i0) → outS (v i)
          ; (j = i1) → outS (w i) })
        (u₀ j)
transpPathPId φ A v w u₀ = refl


transportΣId :
  (A : ∀ i → Type (ℓ′ i))
  (B : ∀ i → A i → Type (ℓ₁′ i))
  (u₀ : Σ (A i0) (B i0))
  → transport (λ i → Σ (A i) (B i)) u₀
    ≡ (transport A (u₀ .fst) ,
      let v = transportFill A (u₀ .fst)
      in transport (λ i → B i (v i)) (u₀ .snd))
transportΣId A B u₀ = refl

transpΣId :
  (φ : I)
  {a : Partial φ (Type ℓ)}
  (A : I → Type ℓ [ φ ↦ a ])
  {b : Partial φ (Type ℓ₁)}
  (B : (i : I) → outS (A i) → Type ℓ₁ [ φ ↦ b ])
  (u₀ : Σ (outS (A i0)) (λ x → outS (B i0 x)))
  → transp (λ i → Σ (outS (A i)) (λ x → outS (B i x))) φ u₀
    ≡ (transp (λ i → outS (A i)) φ (u₀ .fst) ,
      let v = transpFill φ A (u₀ .fst)
      in transp (λ i → outS (B i (v i))) φ (u₀ .snd))
transpΣId φ A B u₀ = refl


transportΠId :
  (A : ∀ i → Type (ℓ′ i))
  (B : ∀ i → A i → Type (ℓ₁′ i))
  (u₀ : (x : A i0) → B i0 x)
  → transport (λ i → (x : A i) → B i x) u₀
    ≡ λ v →
      let
      w : (i : I) → A i
      w i = transportFill (λ j → A (~ j)) v (~ i)
      in
      transport (λ i → B i (w i)) (u₀ (w i0))
transportΠId A B u₀ = refl

transpΠId :
  (φ : I)
  {a : Partial φ (Type ℓ)}
  (A : I → Type ℓ [ φ ↦ a ])
  {b : Partial φ (Type ℓ₁)}
  (B : (i : I) → outS (A i) → Type ℓ₁ [ φ ↦ b ])
  (u₀ : ((x : outS (A i0))  → outS (B i0 x)))
  → transp (λ i → (x : outS (A i)) → outS (B i x)) φ u₀
    ≡ λ v →
      let
      w : (i : I) → outS (A i)
      w i = transpFill φ (λ j → (A (~ j))) v (~ i)
      in
      transp (λ i → outS (B i (w i))) φ (u₀ (w i0))
transpΠId φ A B u₀ = refl


transpUniverseId : (φ : I) (A : Type ℓ) → transp (λ _ → Type ℓ) φ A ≡ A
transpUniverseId φ A = refl


module TransportGlue
  (A : ∀ i → Type (ℓ′ i))
  (φ : I → I)
  (T : (i : I) → Partial (φ i) (Type (ℓ₁′ i)))
  (w : (i : I) → PartialP (φ i) (λ o → T i o ≃ A i))
  (u₀ : primGlue (A i0) (T i0) (w i0))
  where
  B : (i : I) → Type (ℓ₁′ i)
  B i = primGlue (A i) (T i) (w i)

  ∀φ : I
  ∀φ = primFaceForall φ
  
  t : (i : I) → PartialP ∀φ (λ { (∀φ = i1) → T i 1=1 })
  t i (∀φ = i1) = {!!}
  
  transportGlue : B i1
  transportGlue = {!!}

  transportGlueId : transport B u₀ ≡ transportGlue
  transportGlueId = {!!}


-- Section 4 : Recursive Definition of Homogeneous Composition

hcompZeroId : {φ : I} → hcomp (λ i → λ { (φ = i1) → zero }) zero ≡ zero
hcompZeroId = refl

hcompSucId :
  {φ : I}
  (u : I → Partial φ ℕ)
  (u₀ : ℕ [ φ ↦ u i0 ])
  → hcomp (λ i o → suc (u i o)) (suc (outS u₀)) ≡ suc (hcomp u (outS u₀))
hcompSucId u u₀ = refl

hcompPathPId :
  (A : I → Type ℓ)
  (v : A i0)
  (w : A i1)
  {φ : I}
  (u : I → Partial φ (PathP A v w))
  (u₀ : PathP A v w [ φ ↦ u i0 ])
  → hcomp u (outS u₀)
  ≡ λ j →
    hcomp
      (λ i → λ { (φ = i1) → u i 1=1 j ; (j = i0) → v ; (j = i1) → w })
      (outS u₀ j)
hcompPathPId A v w u u₀ = refl

hcompΣId :
  (A : Type ℓ)
  (B : (x : A) → Type ℓ₁)
  {φ : I}
  (u : I → Partial φ (Σ A B))
  (u₀ : Σ A B [ φ ↦ u i0 ])
  → hcomp u (outS u₀)
  ≡ let
    v : (i : I) → A
    -- should use hfill instead
    v = fill (λ _ → A) (λ i o → u i o .fst) (inS (outS u₀ .fst))
    in
    (v i1 ,
    comp (λ i → B (v i)) (λ i → λ { (φ = i1) → u i 1=1 .snd }) (outS u₀ .snd))
hcompΣId A B u u₀ = refl

hcompΠId :
  (A : Type ℓ)
  (B : (x : A) → Type ℓ₁)
  {φ : I}
  (u : I → Partial φ ((x : A) →  B x))
  (u₀ : ((x : A) →  B x) [ φ ↦ u i0 ])
  → hcomp u (outS u₀)
  ≡ λ v → hcomp (λ i o → u i o v) (outS u₀ v)
hcompΠId A B u u₀ = refl


-- Unfortunately  hcomp E (outS A) is not judgmentally equal to
-- outS (hcompUniverse E A) which I don't know why.
hcompUniverse :
  {φ : I}
  (E : I → Partial φ (Type ℓ))
  (A : Type ℓ [ φ ↦ E i0 ])
  → Type ℓ [ φ ↦ E i1 ]
hcompUniverse {φ = φ} E A =
  inS
    (primGlue
      (outS A)
      (E i1)
      (λ { (φ = i1) → lineToEquiv (λ i → E (~ i) 1=1) }))


module HcompGlue
  (A : Type ℓ)
  {φ : I}
  (T : Partial φ (Type ℓ₁))
  (w : PartialP φ (λ o → T o ≃ A))
  {ψ : I}
  (u : I → Partial ψ (primGlue A T w))
  (u₀ : primGlue A T w [ ψ ↦ u i0 ])
  where
  t : (i : I) → PartialP φ T
  t i (φ = i1) = hfill u u₀ i

  a₁ : A
  a₁ = hcomp (λ i → λ
    { (ψ = i1) → unglue φ (u i 1=1)
    ; (φ = i1) → w 1=1 .fst (t i 1=1) })
    (unglue φ (outS u₀))

  hcompGlue : primGlue A T w [ ψ ↦ u i1 ]
  hcompGlue = inS (glue (t i1) a₁)

  hcompGlueId : hcomp u (outS u₀) ≡ outS hcompGlue
  hcompGlueId = refl
