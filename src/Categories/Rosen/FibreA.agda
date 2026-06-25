{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary using (IsEquivalence) renaming (Setoid to S)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category;_[_,_])
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.NaturalTransformation using (NaturalTransformation;_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,_])
module Categories.Rosen.FibreA {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

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

-- Pullback of two functors, ∇ and V₁.
-- In Cats, the categorical pullback is (in general) a pseudo-pullback; concretely this
-- is the “iso-comma” construction: objects are pairs plus an isomorphism in Arrow(C).

reindex : {A A' : Obj} → (u : A ⇒ A') → Functor (totalAtA A') (totalAtA A)
reindex u = record
  { F₀ = λ { (B ∣ ξ) → B ∣ ⟪ MR2.f ξ ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ MR2.ϕ ξ ⟫}
  ; F₁ = λ { {(B ∣ ξ)} {(B' ∣ ξ')} (record { r = r ; eqϕ = eq}) → record 
      { r = r 
      ; eqϕ = {!   !} 
      }}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }

module _ (A : Obj) where
  private
    module TA = Category (totalAtA A)
    module TM = Category 𝕋MRS
    module Ar = Category Arr.Arrow
    module F  = Functor (∇ {A})
    module G  = Functor V₁

  import Categories.Morphism as M using (_≅_)
  open M Arr.Arrow using (_≅_)
  record FibreA₀ : Set (o ⊔ ℓ ⊔ e) where
    field
      x   : TA.Obj
      y   : TM.Obj
      iso : (F.F₀ x) ≅ (G.F₀ y)

  record FibreA⇒ (P Q : FibreA₀) : Set (o ⊔ ℓ ⊔ e) where
    module P = FibreA₀ P
    module Q = FibreA₀ Q
    module iP = _≅_ P.iso
    module iQ = _≅_ Q.iso
    field
      f : TA._⇒_ P.x Q.x
      g : TM._⇒_ P.y Q.y
      commute : (G.F₁ g Ar.∘ iP.from) Ar.≈ iQ.from Ar.∘ F.F₁ f

  MRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
  MRS3 = record
    { Obj = FibreA₀
    ; _⇒_ = FibreA⇒
    ; _≈_ = λ { u v → FibreA⇒.f u TA.≈ FibreA⇒.f v × FibreA⇒.g u TM.≈ FibreA⇒.g v }
    ; id = λ { {P} →
        let module P = FibreA₀ P
            module iP = _≅_ P.iso
        in record
          { f = TA.id
          ; g = TM.id
          ; commute = sym-id-swap , id-0 ∙ sym-id-1 ∙ skip (sym [-,-].identity)
          }
          }
    ; _∘_ = λ { {P} {Q} {R} u v →
        let module P  = FibreA₀ P
            module Q  = FibreA₀ Q
            module R  = FibreA₀ R
            module u  = FibreA⇒ u
            module v  = FibreA⇒ v
            module iP = _≅_ P.iso
            module iQ = _≅_ Q.iso
            module iR = _≅_ R.iso
            open Ar.HomReasoning
        in record
          { f = u.f TA.∘ v.f
          ; g = u.g TM.∘ v.g
          ; commute = assoc ∙ skip (proj₁ v.commute) ∙ rw-2 (proj₁ u.commute)
                    , assoc ∙ skip (proj₂ v.commute) ∙ rw-2 (proj₂ u.commute) ∙ skip (sym (Functor.homomorphism [ _ ,-]))
          } }
    ; assoc     = assoc     , assoc     , assoc
    ; sym-assoc = sym-assoc , sym-assoc , sym-assoc
    ; identityˡ = identityˡ , identityˡ , identityˡ
    ; identityʳ = identityʳ , identityʳ , identityʳ
    ; identity² = identity² , identity² , identity²
    ; equiv = record
      { refl = refl , refl , refl
      ; sym = λ { (p , q , r) → sym p , sym q , sym r }
      ; trans = λ { (p₁ , q₁ , r₁) (p₂ , q₂ , r₂) → trans p₁ p₂ , trans q₁ q₂ , trans r₁ r₂ }
      }
    ; ∘-resp-≈ = λ { (p₁ , q₁ , r₁) (p₂ , q₂ , r₂) → ∘-resp-≈ p₁ p₂ , ∘-resp-≈ q₁ q₂ , ∘-resp-≈ r₁ r₂ }
    }
-- But also, a comma category.
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
