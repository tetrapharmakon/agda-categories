{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Data.Product

module G2M2 {o ℓ e} (ℂ : Category o ℓ e) where

open Category ℂ
open HomReasoning
open Equiv

open import Level

open import Categories.Adjoint
open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian as c
open import Categories.Category.Cocartesian as cc
open import Categories.Category.Cocomplete.Finitely ℂ
open import Categories.Diagram.Coequalizer ℂ
open import Categories.Functor.Core
open import Categories.Morphism.Reasoning ℂ
open import Categories.Object.Coproduct


{-
CATEGORIES
===

-}
-- G(2)
record G2Obj : Set (o ⊔ ℓ ⊔ e) where
  constructor g2obj
  field
    {E V} : Obj
    s t : E ⇒ V
    i : V ⇒ E
    σ τ : E ⇒ E
    si=1 : s ∘ i ≈ id
    ti=1 : s ∘ i ≈ id
    is=σ : i ∘ s ≈ σ
    it=τ : i ∘ t ≈ τ
    --

open G2Obj

record G2Mor (G H : G2Obj) : Set (ℓ ⊔ e) where
  constructor g2mor
  private
    module G = G2Obj G
    module H = G2Obj H
  field
    fE : G.E ⇒ H.E
    fV : G.V ⇒ H.V
    --
    s-eqv : fV ∘ G.s ≈ H.s ∘ fE
    t-eqv : fV ∘ G.t ≈ H.t ∘ fE
    i-eqv : H.i ∘ fV ≈ fE ∘ G.i
    σ-eqv : fE ∘ G.σ ≈ H.σ ∘ fE
    τ-eqv : fE ∘ G.τ ≈ H.τ ∘ fE

open G2Mor

-- M(2)
record M2Obj : Set (o ⊔ ℓ ⊔ e) where
  constructor m2obj
  field
    {X} : Obj
    s t : X ⇒ X
    --
    ss=s : s ∘ s ≈ s
    tt=t : t ∘ t ≈ t
    st=t : s ∘ t ≈ t
    ts=s : t ∘ s ≈ s

open M2Obj

record M2Mor (G H : M2Obj) : Set (ℓ ⊔ e) where
  constructor m2mor
  private
    module G = M2Obj G
    module H = M2Obj H
  field
    f : G.X ⇒ H.X
    --
    s-eqv : f ∘ G.s ≈ H.s ∘ f
    t-eqv : f ∘ G.t ≈ H.t ∘ f

open M2Mor


M2 : Category _ _ _
M2 = record
  { Obj = M2Obj
  ; _⇒_ = λ G H → M2Mor G H
  ; _≈_ = λ u v → M2Mor.f u ≈ M2Mor.f v
  ; id = record { f = id ; s-eqv = id-comm-sym ; t-eqv = id-comm-sym }
  ; _∘_ = comp
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp-≈
  } where comp : {A B C : M2Obj} → M2Mor B C → M2Mor A B → M2Mor A C
          comp {A} {B} {C} (m2mor f eqs eqt) (m2mor g eqs' eqt') = m2mor (f ∘ g)
            (begin (f ∘ g) ∘ s A  ≈⟨ pullʳ eqs' ○ sym assoc ⟩
                   (f ∘ s B) ∘ g  ≈⟨ pushˡ eqs ⟩
                   s C ∘ f ∘ g    ∎)
            (begin (f ∘ g) ∘ t A  ≈⟨ pullʳ eqt' ○ sym assoc ⟩
                   (f ∘ t B) ∘ g  ≈⟨ pushˡ eqt ⟩
                   t C ∘ f ∘ g    ∎)

G2 : Category _ _ _
G2 = record
  { Obj = G2Obj
  ; _⇒_ = λ G H → G2Mor G H
  ; _≈_ = λ u v → (fE u ≈ fE v) × (fV u ≈ fV v)
  ; id = g2mor id id id-comm-sym id-comm-sym id-comm id-comm-sym id-comm-sym
  ; _∘_ = comp
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  } where comp : {A B C : G2Obj} → G2Mor B C → G2Mor A B → G2Mor A C
          comp {A} {B} {C} (g2mor fE fV eqs eqt _ _ _) (g2mor gE gV eqs' eqt' _ _ _) = g2mor (fE ∘ gE) (fV ∘ gV)
            {!   !}
            {!   !}
            {!   !}
            {!   !}
            {!   !}
