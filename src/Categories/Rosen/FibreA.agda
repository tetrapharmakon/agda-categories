{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category;_[_,_])
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Relation.Binary.Bundles renaming (Setoid to S)
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

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

import Categories.Morphism.Reasoning as MR
open HomReasoning 
open MR

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
    eqϕ : Functor.F₁ [ A ,-] r ∘ ϕ.η (record { arr = f }) ≈ ψ.η (record { arr = g }) ∘ r


totalAtA : (A : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
totalAtA A = record
  { Obj = totalAtA₀ A
  ; _⇒_ = λ { s t → totalAtA₁ s t}
  ; _≈_ = λ x y → let module x = totalAtA₁ x 
                      module y = totalAtA₁ y in x.r ≈ y.r
  ; id = record 
      { r = id 
      ; eqϕ = elimˡ C (Functor.identity [ A ,-]) ○ introʳ C Equiv.refl 
      }
  ; _∘_ = λ u v → let module u = totalAtA₁ u 
                      module v = totalAtA₁ v 
                  in record 
                    { r = u.r ∘ v.r 
                    ; eqϕ = Functor.homomorphism [ A ,-] ⟩∘⟨refl ○ pullʳ C v.eqϕ  ○ pullˡ C u.eqϕ ○ assoc 
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
  in record { arr = phi.η (record { arr = MR2.f ξ }) }
  ; F₁ = λ { {X ∣ ⟪ f , ϕ ⟫} {Y ∣ ⟪ g , ψ ⟫} (record { r = r ; eqϕ = eqϕ }) → mor⇒ eqϕ }
  ; identity = λ { {X} → Equiv.refl , (Functor.identity [ A ,-])}
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} → Equiv.refl , Functor.homomorphism [ A ,-] }
  ; F-resp-≈ = λ {X} {Y} {f} {g} z → z , Functor.F-resp-≈ [ A ,-] z
  }

-- Pullback of two functors, ∇ and V₁.
-- In Cats, the categorical pullback is (in general) a pseudo-pullback; concretely this
-- is the “iso-comma” construction: objects are pairs plus an isomorphism in Arrow(C).

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
    constructor ⟨_,_,_⟩
    field
      x   : TA.Obj
      y   : TM.Obj
      iso : (F.F₀ x) ≅ (G.F₀ y)

  record FibreA⇒ (P Q : FibreA₀) : Set (o ⊔ ℓ ⊔ e) where
    constructor ⟪_,_,_⟫
    module P = FibreA₀ P
    module Q = FibreA₀ Q
    module iP = _≅_ P.iso
    module iQ = _≅_ Q.iso
    field
      f : TA._⇒_ P.x Q.x
      g : TM._⇒_ P.y Q.y
      commute : (G.F₁ g Ar.∘ iP.from) Ar.≈ {!  !} -- Ar._∘_ (iQ.from (F.F₁ f)) -- Ar._≈_ (Ar._∘_ (G.F₁ g) iP.from) ≈ Ar._∘_ (iQ.from (F.F₁ f))

  MRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e 
  MRS3 = record
    { Obj = FibreA₀
    ; _⇒_ = FibreA⇒
    ; _≈_ = λ { u v → FibreA⇒.f u TA.≈ FibreA⇒.f v × FibreA⇒.g u TM.≈ FibreA⇒.g v }
    ; id = λ { {P} →
        let module P = FibreA₀ P
            module iP = _≅_ P.iso
            open Ar.HomReasoning
        in {!  !} }
        -- ⟪ TA.id , TM.id ,
        --   (begin
        --      Ar._∘_ (G.F₁ TM.id) iP.from   ≈⟨ Ar.∘-resp-≈ (G.identity) Ar.Equiv.refl ⟩
        --      Ar._∘_ Ar.id iP.from          ≈⟨ Ar.identityˡ ⟩
        --      iP.from                       ≈˘⟨ Ar.identityʳ ⟩
        --      Ar._∘_ iP.from Ar.id          ≈˘⟨ Ar.∘-resp-≈ Ar.Equiv.refl (F.identity) ⟩
        --      Ar._∘_ iP.from (F.F₁ TA.id)   ∎) ⟫ }
    ; _∘_ = λ { {P} {Q} {R} u v →
        let module P = FibreA₀ P
            module Q = FibreA₀ Q
            module R = FibreA₀ R
            module u = FibreA⇒ u
            module v = FibreA⇒ v
            module iP = _≅_ P.iso
            module iQ = _≅_ Q.iso
            module iR = _≅_ R.iso
            open Ar.HomReasoning
        in {!  !} }
        -- ⟪ TA [ u.f TA.∘ v.f ] , TM [ u.g TM.∘ v.g ] ,
        --   (begin
        --      Ar._∘_ (G.F₁ (TM [ u.g TM.∘ v.g ])) iP.from
        --        ≈⟨ Ar.∘-resp-≈ (G.homomorphism) Ar.Equiv.refl ⟩
        --      Ar._∘_ (Ar._∘_ (G.F₁ u.g) (G.F₁ v.g)) iP.from
        --        ≈⟨ Ar.assoc ⟩
        --      Ar._∘_ (G.F₁ u.g) (Ar._∘_ (G.F₁ v.g) iP.from)
        --        ≈⟨ Ar.∘-resp-≈ Ar.Equiv.refl v.commute ⟩
        --      Ar._∘_ (G.F₁ u.g) (Ar._∘_ iQ.from (F.F₁ v.f))
        --        ≈˘⟨ Ar.assoc ⟩
        --      Ar._∘_ (Ar._∘_ (G.F₁ u.g) iQ.from) (F.F₁ v.f)
        --        ≈⟨ Ar.∘-resp-≈ u.commute Ar.Equiv.refl ⟩
        --      Ar._∘_ (Ar._∘_ iR.from (F.F₁ u.f)) (F.F₁ v.f)
        --        ≈⟨ Ar.assoc ⟩
        --      Ar._∘_ iR.from (Ar._∘_ (F.F₁ u.f) (F.F₁ v.f))
        --        ≈˘⟨ Ar.∘-resp-≈ Ar.Equiv.refl (F.homomorphism) ⟩
        --      Ar._∘_ iR.from (F.F₁ (TA [ u.f TA.∘ v.f ]))
        --      ∎) ⟫ }
    ; assoc = TA.assoc , TM.assoc
    ; sym-assoc = TA.sym-assoc , TM.sym-assoc
    ; identityˡ = TA.identityˡ , TM.identityˡ
    ; identityʳ = TA.identityʳ , TM.identityʳ
    ; identity² = TA.identity² , TM.identity²
    ; equiv = record
      { refl = TA.Equiv.refl , TM.Equiv.refl
      ; sym = λ { (p , q) → TA.Equiv.sym p , TM.Equiv.sym q }
      ; trans = λ { (p₁ , q₁) (p₂ , q₂) → TA.Equiv.trans p₁ p₂ , TM.Equiv.trans q₁ q₂ }
      }
    ; ∘-resp-≈ = λ { (p₁ , q₁) (p₂ , q₂) → TA.∘-resp-≈ p₁ p₂ , TM.∘-resp-≈ q₁ q₂ }
    }


-- But also, a comma category.
-- Objects are commutative squares in Arrow(C):  ∇ x ⇒ V₁ y.

open import Categories.Category.Construction.Comma
FibreA : (A : Obj) → Category _ _ _
FibreA A = (∇ {A} ↓ V₁)