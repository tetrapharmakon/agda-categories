{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_; lift; lower)

module Categories.Rosen.Coherent.Tabulator {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Tabulator of MRS-Profunctor: a canonical category 𝕋MRS attached to the
-- profunctor MRS-Profunctor : C^op × C → Sets, equipped with a universal
-- 2-cell. This is the heart of the Rosen fibration.
-- Exports: 𝕋MRS, π, þ, [_]f, ϵ.

open import Data.Product using (_,_; proj₁)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Profunctor.Tabulator
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Rosen.Coherent.IdCore Cl

import Reason
open Reason C
open HomReasoning
open MR

-- Arrow(C).  Coherent/Core exported this because it needs it to state Cod;
-- Coherent/IdCore has no use for it, so consumers declare it themselves.
-- Private, so that a module importing several of these does not see the same
-- alias arrive from two directions at once.
private
  module Arr = Categories.Category.Construction.Arrow C

-- `lift`/`lower` below strip IdCore's Level.Lift on the setoid relation.  They
-- are Agda universe bookkeeping with no mathematical content; see the comment
-- at the top of Coherent/IdCore.agda.

-- The tabulator category of MRS-Profunctor.
𝕋MRS = Tabulator MRS-Profunctor

-- Left projection 𝕋MRS → C.
π  = projection {p = MRS-Profunctor}
-- The universal terminal 2-cell of the tabulator.
þ  = cell {p = MRS-Profunctor}

-- [_]f: the first edge functor.  Extracts the process map f from a coherent
-- (M,R)-system; this is the paper's ⦇-⦈_f of definition_first_edge_functor.
[_]f : Functor 𝕋MRS Arr.Arrow
[_]f = record
  { F₀ = λ { ((A , B) ∣ ξ) → record { arr = MR2.f ξ } }
  ; F₁ = λ { {(A , B) ∣ ⟪ f , Φ ⟫} {(A′ , B′) ∣ ⟪ g , Φ′ ⟫} (l , r ∥ E) → mor⇒ {dom⇒ = l} {cod⇒ = r}
    (let eq = proj₁ (lower E) in
     begin r ∘ f      ≈˘⟨ id-2 ⟩
           r ∘ f ∘ id ≈⟨ eq ○ identityˡ ⟩
           g ∘ l      ∎) }
  ; identity =
      Equiv.refl
    , Equiv.refl
  ; homomorphism =
      Equiv.refl
    , Equiv.refl
  ; F-resp-≈ = λ { x → x }
  }

-- ϵ: natural transformation from MRS-Profunctor to the lifted hom functor.
ϵ  : NaturalTransformation MRS-Profunctor (LiftSetoids (o ⊔ e) (o ⊔ ℓ) ∘F Hom[ C ][-,-])
ϵ = ntHelper record
  { η = λ { (A , B) → record
    { _⟨$⟩_ = λ {⟪ f , Φ ⟫ → lift f }
    ; cong = λ { {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} eq → lift (proj₁ (lower eq)) }
    } }
  ; commute = λ { {(A , B)} {(A′ , B′)} (u , v) {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} eq →
      lift (∘-resp-≈ʳ (∘-resp-≈ˡ (proj₁ (lower eq)))) }
  }
