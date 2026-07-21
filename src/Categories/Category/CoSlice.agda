{-# OPTIONS --without-K --allow-unsolved-metas --warning=noUnsupportedIndexedMatch --warning=noUserWarning #-}
open import Categories.Category.Core

-- slice category (https://ncatlab.org/nlab/show/over+category)
-- TODO: Forgetful Functor from coSlice to 𝒞
module Categories.Category.CoSlice {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open Equiv

open import Level
open import Function.Base using (_$_)
open import Relation.Binary.Core using (Rel)

open import Categories.Morphism.Reasoning 𝒞

record coSliceObj (X : Obj) : Set (o ⊔ ℓ) where
  constructor sliceobj
  field
    {Y} : Obj
    arr : X ⇒ Y

private
  variable
    A : Obj
    X Y Z : coSliceObj A

record coSlice⇒ {A : Obj} (X Y : coSliceObj A) : Set (ℓ ⊔ e) where
  constructor slicearr
  private
    module X = coSliceObj X
    module Y = coSliceObj Y
  field
    {h} : X.Y ⇒ Y.Y
    ∇   : h ∘ X.arr ≈ Y.arr

coSlice : Obj → Category (o ⊔ ℓ) (ℓ ⊔ e) e
coSlice A       = record
  { Obj = coSliceObj A
  ; _⇒_ = coSlice⇒
  ; _≈_ = λ where
    (slicearr {f} _) (slicearr {g} _) → f ≈ g
  ; id = slicearr identityˡ
  ; _∘_ = _∘′_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record -- must be expanded to get levels to work out
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  } where _∘′_ : coSlice⇒ Y Z → coSlice⇒ X Y → coSlice⇒ X Z
          _∘′_ {Y = sliceobj y} {Z = sliceobj z} {X = sliceobj x} (slicearr {g} ∇) (slicearr {f} ∇′) = slicearr {h = g ∘ f} (pullʳ ∇′ ○ ∇)


open import Categories.Functor using (Functor; _∘F_)
Cod : (A : Obj) → Functor (coSlice A) 𝒞
Cod A = record
  { F₀           = coSliceObj.Y
  ; F₁           = coSlice⇒.h
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ z → z
  }


reindex : ∀ {A A'} (u : A ⇒ A') → Functor (coSlice A') (coSlice A)
reindex u = record
  { F₀ = λ x → let module x = coSliceObj x in sliceobj (x.arr ∘ u)
  ; F₁ = λ f → let module f = coSlice⇒ f in slicearr (sym-assoc ○ ∘-resp-≈ˡ f.∇)
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ z → z
  }

open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism;niHelper; _ⓘˡ_; _ⓘʳ_)


commute : ∀ {A A'} (u : A ⇒ A') → NaturalIsomorphism (Cod A') (Cod A ∘F reindex u)
commute u = niHelper (record 
  { η = λ X → id 
  ; η⁻¹ = λ X → id 
  ; commute = λ {X} {Y} f → trans identityˡ (sym identityʳ) 
  ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identity² } 
  })


open import Categories.Diagram.Pushout 𝒞
open import Categories.Adjoint using (Adjoint; _⊣_)

private
  coSlice⇒-≈-h : ∀ {A X Y} {f g : coSlice⇒ {A} X Y} → Category._≈_ (coSlice A) f g → coSlice⇒.h f ≈ coSlice⇒.h g
  coSlice⇒-≈-h {f = slicearr {h} _} {slicearr {h'} _} h≈h' = h≈h'

module LeftAdjoint ⦃ pushout : ∀ {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) → Pushout f g ⦄ where
  S : ∀ {A A'} (u : A ⇒ A') → Functor (coSlice A) (coSlice A')
  S u = record
    { F₀ = λ { (sliceobj {Y} f) →
        let module P = Pushout (pushout f u)
        in sliceobj (P.i₂) }
    ; F₁ = λ {M} {N} (slicearr {h} ∇) →
        let module P' = Pushout (pushout (coSliceObj.arr M) u)
            module P  = Pushout (pushout (coSliceObj.arr N) u)
        in slicearr {h = P'.universal {h₁ = P.i₁ ∘ h} {h₂ = P.i₂}
          (pullʳ ∇ ○ P.commute)} P'.universal∘i₂≈h₂
    ; identity = λ {M} →
        let module P = Pushout (pushout (coSliceObj.arr M) u)
            eq : (P.i₁ ∘ id) ∘ coSliceObj.arr M ≈ P.i₂ ∘ u
            eq = pullʳ identityˡ ○ P.commute
        in sym (P.unique {j = id} {eq = eq}
                (begin id ∘ P.i₁ ≈⟨ identityˡ ⟩ P.i₁ ≈⟨ sym identityʳ ⟩ P.i₁ ∘ id ∎)
                identityˡ)
    ; homomorphism = λ {X} {Y} {Z} {f₁} {g₁} →
        let h   = coSlice⇒.h f₁
            ∇   = coSlice⇒.∇ f₁
            k   = coSlice⇒.h g₁
            ∇'  = coSlice⇒.∇ g₁
            g∘f = Category._∘_ (coSlice _) g₁ f₁
            ∇″  = coSlice⇒.∇ g∘f
            module PX = Pushout (pushout (coSliceObj.arr X) u)
            module PY = Pushout (pushout (coSliceObj.arr Y) u)
            module PZ = Pushout (pushout (coSliceObj.arr Z) u)
            eq₁ : (PY.i₁ ∘ h) ∘ coSliceObj.arr X ≈ PY.i₂ ∘ u
            eq₁ = pullʳ ∇ ○ PY.commute
            eq₂ : (PZ.i₁ ∘ k) ∘ coSliceObj.arr Y ≈ PZ.i₂ ∘ u
            eq₂ = pullʳ ∇' ○ PZ.commute
            eq₃ : (PZ.i₁ ∘ (k ∘ h)) ∘ coSliceObj.arr X ≈ PZ.i₂ ∘ u
            eq₃ = pullʳ ∇″ ○ PZ.commute
            u₁ : PX.Q ⇒ PY.Q
            u₁ = PX.universal {h₁ = PY.i₁ ∘ h} {h₂ = PY.i₂} eq₁
            u₂ : PY.Q ⇒ PZ.Q
            u₂ = PY.universal {h₁ = PZ.i₁ ∘ k} {h₂ = PZ.i₂} eq₂
        in sym (PX.unique {j = u₂ ∘ u₁} {eq = eq₃}
                (begin
                  (u₂ ∘ u₁) ∘ PX.i₁ ≈⟨ pullʳ (PX.universal∘i₁≈h₁ {h₁ = PY.i₁ ∘ h} {h₂ = PY.i₂} {eq = eq₁}) ⟩
                  u₂ ∘ (PY.i₁ ∘ h)  ≈⟨ pullˡ (PY.universal∘i₁≈h₁ {h₁ = PZ.i₁ ∘ k} {h₂ = PZ.i₂} {eq = eq₂}) ⟩
                  (PZ.i₁ ∘ k) ∘ h   ≈⟨ assoc ⟩
                  PZ.i₁ ∘ (k ∘ h)   ∎)
                (begin
                  (u₂ ∘ u₁) ∘ PX.i₂ ≈⟨ pullʳ (PX.universal∘i₂≈h₂ {h₁ = PY.i₁ ∘ h} {h₂ = PY.i₂} {eq = eq₁}) ⟩
                  u₂ ∘ PY.i₂        ≈⟨ PY.universal∘i₂≈h₂ {h₁ = PZ.i₁ ∘ k} {h₂ = PZ.i₂} {eq = eq₂} ⟩
                  PZ.i₂             ∎))
    ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g →
        let h    = coSlice⇒.h f
            h'   = coSlice⇒.h g
            ∇    = coSlice⇒.∇ f
            ∇'   = coSlice⇒.∇ g
            module PX = Pushout (pushout (coSliceObj.arr X) u)
            module PY = Pushout (pushout (coSliceObj.arr Y) u)
            eq₁ : (PY.i₁ ∘ h) ∘ coSliceObj.arr X ≈ PY.i₂ ∘ u
            eq₁ = pullʳ ∇ ○ PY.commute
            eq₂ : (PY.i₁ ∘ h') ∘ coSliceObj.arr X ≈ PY.i₂ ∘ u
            eq₂ = pullʳ ∇' ○ PY.commute
        in PX.unique {j = PX.universal {h₁ = PY.i₁ ∘ h} {h₂ = PY.i₂} eq₁} {eq = eq₂}
             (begin
               (PX.universal eq₁) ∘ PX.i₁ ≈⟨ PX.universal∘i₁≈h₁ {h₁ = PY.i₁ ∘ h} {h₂ = PY.i₂} {eq = eq₁} ⟩
                PY.i₁ ∘ h                 ≈⟨ ∘-resp-≈ refl f≈g ⟩
               PY.i₁ ∘ h'                 ∎)
             (PX.universal∘i₂≈h₂ {h₁ = PY.i₁ ∘ h} {h₂ = PY.i₂} {eq = eq₁})
    }

  S⊣reindex : ∀ {A A'} (u : A ⇒ A') → Adjoint (S u) (reindex u)
  S⊣reindex u = record
    { unit = {!!}
    ; counit = {!!}
    ; zig = {!!}
    ; zag = {!!}
    }

open LeftAdjoint