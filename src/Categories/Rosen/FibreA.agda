{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Data.Product using (_,_)
open import Relation.Binary using () renaming (Setoid to S)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.NaturalTransformation using (NaturalTransformation)
module Categories.Rosen.FibreA {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

import Categories.Morphism.Reasoning as MR

open import Categories.Category.Construction.Arrow C using (Morphism; Morphism⇒; mor⇒)
open import Categories.Rosen.Core Cl
open import Categories.Rosen.Tabulator Cl using (𝕋MRS; V₁)

MRS[1,-] = appˡ MRS-Profunctor

MRS[-,1] = appʳ MRS-Profunctor

-- last attempt

record totalAtA₀ (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  constructor _∣_
  field
    B : Obj
    ξ : S.Carrier (Functor.F₀ MRS-Profunctor (A , B))

record totalAtA₁ {A : Obj} (x y : totalAtA₀ A) : Set (o ⊔ ℓ ⊔ e) where
  module x = totalAtA₀ x
  module y = totalAtA₀ y
  field
    r : x.B ⇒ y.B

  f = MR2.f x.ξ
  g = MR2.f y.ξ

  module ϕ = NaturalTransformation (MR2.ϕ x.ξ)
  module ψ = NaturalTransformation (MR2.ϕ y.ξ)
  field
    eqϕ : [ id , r ]₁ ∘ ϕ.η (record { dom = A ; cod = x.B ; arr = f }) ≈ ψ.η (record { dom = A ; cod = y.B ; arr = g }) ∘ r


totalAtA : (A : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
totalAtA A = record
  { Obj = totalAtA₀ A
  ; _⇒_ = λ { s t → totalAtA₁ s t}
  ; _≈_ = λ x y → let module x = totalAtA₁ x
                      module y = totalAtA₁ y in x.r ≈ y.r
  ; id = record
      { r = id
      ; eqϕ = cancel [-,-].identity ∙ sym-id-1
      }
  ; _∘_ = λ u v → let module u = totalAtA₁ u
                      module v = totalAtA₁ v
                  in record
                    { r = u.r ∘ v.r
                    ; eqϕ = rw-1-2 (Functor.homomorphism [ A ,-]) ∙ skip v.eqϕ ∙ rw-2 u.eqϕ
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

∇ : {A : Obj} → Functor (totalAtA A) Arr.Arrow
∇ {A} = record
  { F₀ = λ (B ∣ ξ) →
  let module phi = NaturalTransformation (MR2.ϕ ξ)
  in record { dom = B ; cod = [ A , B ]₀ ; arr = phi.η (record { dom = A ; cod = B ; arr = MR2.f ξ }) }
  ; F₁ = λ { {X ∣ ⟪ f , ϕ ⟫} {Y ∣ ⟪ g , ψ ⟫} (record { r = r ; eqϕ = eqϕ }) → mor⇒ {dom⇒ = r} {cod⇒ = Functor.F₁ [ A ,-] r} eqϕ }
  ; identity = λ { {X} → Equiv.refl , (Functor.identity [ A ,-])}
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} → Equiv.refl , Functor.homomorphism [ A ,-] }
  ; F-resp-≈ = λ {X} {Y} {f} {g} z → z , Functor.F-resp-≈ [ A ,-] z
  }

-- The same construction of HigherMRS.agda, but with a comma category instead of PB.
-- Objects are commutative squares in Arrow(C):  ∇ x ⇒ V₁ y.

open import Categories.Category.Construction.Comma
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

commaNablaV : {T : Obj} → Category (ℓ ⊔ e ⊔ (o ⊔ ℓ ⊔ e)) (e ⊔ (o ⊔ ℓ ⊔ e)) e
commaNablaV {T} = (∇ {T} ↓ V₁)

_ : {T : Obj} → (Category.Obj (commaNablaV {T})) ≡ CommaObj ∇ V₁
_ = _≡_.refl

_ : {T : Obj} → (Category._⇒_ (commaNablaV {T})) ≡ Comma⇒
_ = _≡_.refl
