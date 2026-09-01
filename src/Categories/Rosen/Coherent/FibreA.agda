{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Coherent.FibreA {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Fibre-at-A: alternative construction for higher (M,R)-systems by
-- fixing the domain object A, which simplifies the definitions.
-- The fibre over A is the category totalAtA A; ∇ sends it into Arrow;
-- commaNablaV is a weaker comma-object invariant (historical).
-- Also includes commaNablaV, a weaker comma-object invariant (historical).
-- Exports: totalAtA₀, totalAtA₁, totalAtA, ∇, commaNablaV.

open import Data.Product using (_,_)
open import Relation.Binary using () renaming (Setoid to S)

open import Categories.Category.Construction.Arrow C using (Morphism; Morphism⇒; mor⇒)
import Categories.Category.Construction.Arrow
-- Arrow(C); see the note in Coherent/ProElements.agda.
module Arr = Categories.Category.Construction.Arrow C
open import Categories.Category.Construction.Comma
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Rosen.Coherent.IdCore Cl
open import Categories.Rosen.Coherent.Tabulator Cl using (𝕋MRS; ⟅_⟆f)

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

-- Objects of the fibre at A: a codomain B plus an element ξ of MRS-Profunctor (A, B).
record totalAtA₀ (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  constructor _∣_
  field
    B : Obj
    ξ : S.Carrier (Functor.F₀ MRS-Profunctor (A , B))


-- Morphisms of the fibre at A: a map r : x.B ⇒ y.B compatible with Φ.
record totalAtA₁ {A : Obj} (x y : totalAtA₀ A) : Set (o ⊔ ℓ ⊔ e) where
  module x = totalAtA₀ x
  module y = totalAtA₀ y
  field
    r : x.B ⇒ y.B

  f = MR2.f x.ξ
  g = MR2.f y.ξ

  module Φ = NaturalTransformation (MR2.Φ x.ξ)
  module ψ = NaturalTransformation (MR2.Φ y.ξ)
  field
    eqΦ : [ id , r ]₁ ∘ Φ.η x.B ≈ ψ.η y.B ∘ r


-- totalAtA A: the category of (M,R)-systems whose metabolic domain is the
-- fixed object A.
-- Category totalAtA A: the fibre over A of the MRS profunctor.
totalAtA : (A : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
totalAtA A = record
  { Obj = totalAtA₀ A
  ; _⇒_ = λ { s t → totalAtA₁ s t}
  ; _≈_ = λ x y → let module x = totalAtA₁ x
                      module y = totalAtA₁ y in x.r ≈ y.r
  ; id = record
      { r = id
      ; eqΦ = cancel [-,-].identity ∙ sym-id-1
      }
  ; _∘_ = λ u v → let module u = totalAtA₁ u
                      module v = totalAtA₁ v
                  in record
                    { r = u.r ∘ v.r
                    ; eqΦ = rw-1-2 (Functor.homomorphism [ A ,-]) ∙ skip v.eqΦ ∙ rw-2 u.eqΦ
                    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = Equiv.refl
    ; sym = Equiv.sym
    ; trans = Equiv.trans
    }
  ; ∘-resp-≈ = λ f≈g h≈i → ∘-resp-≈ f≈g h≈i
  }

-- ∇: functor from the fibre to Arrow, sending (B, ξ) to the Φ-component B → [A,B].
∇ : {A : Obj} → Functor (totalAtA A) Arr.Arrow
∇ {A} = record
  { F₀ = λ (B ∣ ξ) →
  let module phi = NaturalTransformation (MR2.Φ ξ)
  in record { dom = B ; cod = [ A , B ]₀ ; arr = phi.η B }
  ; F₁ = λ { {X ∣ ⟪ f , Φ ⟫} {Y ∣ ⟪ g , ψ ⟫} (record { r = r ; eqΦ = eqΦ }) → mor⇒ {dom⇒ = r} {cod⇒ = Functor.F₁ [ A ,-] r} eqΦ }
  ; identity = λ { {X} → Equiv.refl , (Functor.identity [ A ,-])}
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} → Equiv.refl , Functor.homomorphism [ A ,-] }
  ; F-resp-≈ = λ {X} {Y} {f} {g} z → z , Functor.F-resp-≈ [ A ,-] z
  }

-- The same construction of HigherMRS.agda, but with a comma category instead of PB.
-- Objects are commutative squares in Arrow(C):  ∇ x ⇒ ⟅_⟆f y.

-- commaNablaV: comma category ∇ ↓ ⟅_⟆f.  Weaker than the pullback in HigherMRS.
commaNablaV : {T : Obj} → Category (ℓ ⊔ e ⊔ (o ⊔ ℓ ⊔ e)) (e ⊔ (o ⊔ ℓ ⊔ e)) e
commaNablaV {T} = (∇ {T} ↓ ⟅_⟆f)


