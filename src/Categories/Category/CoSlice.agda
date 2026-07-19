{-# OPTIONS --without-K --safe --warning=noUnsupportedIndexedMatch --warning=noUserWarning #-}
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