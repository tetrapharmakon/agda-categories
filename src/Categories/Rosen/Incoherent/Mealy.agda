{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level
open import Categories.Category
open import Categories.Object.Terminal
import Categories.Morphism.Reasoning as MR
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.Mealy {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Category.Product using (Product;_⁂_;πʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C

open Closed Cl using (adjoint; unitorˡ;unitorʳ-commute-to; unitorʳ-commute-from;unitorʳ; [-,-]; unit; [_,_]₀; [_,-]; [-,_]; [_,_]₁;⊗;_⊗₀_;_⊗₁_;_⊗-;-⊗_)

record Mealy A B : Set (o ⊔ ℓ ⊔ e) where
  field
    E : Obj
    d : E ⊗₀ A ⇒ E
    s : E ⊗₀ A ⇒ B

record Mealy₀ : Set (o ⊔ ℓ ⊔ e) where
  field
    A B : Obj 
    m : Mealy A B

record Mealy⇒ (X Y : Mealy₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = Mealy₀ X
  module Y = Mealy₀ Y
  module mX = Mealy X.m
  module mY = Mealy Y.m
  field
    l : X.A ⇒ Y.A 
    r : X.B ⇒ Y.B 
    u : mX.E ⇒ mY.E 
    d-eq : u ∘ mX.d ≈ mY.d ∘ u ⊗₁ l
    s-eq : r ∘ mX.s ≈ mY.s ∘ u ⊗₁ l

Mealy⇒-≈ : {A B : Mealy₀} → Mealy⇒ A B → Mealy⇒ A B → Set e
Mealy⇒-≈ f g = 
  let module f = Mealy⇒ f 
      module g = Mealy⇒ g
  in
 f.l ≈ g.l × f.l ≈ g.l × f.u ≈ g.u

totalMealy : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
totalMealy = record
  { Obj = Mealy₀
  ; _⇒_ = λ s t → Mealy⇒ s t
  ; _≈_ = Mealy⇒-≈
  ; id = record 
    { l = id ; r = id ; u = id 
    ; d-eq = id-0 ∙ intro-1 ⊗.identity ; s-eq = id-0 ∙ intro-1 ⊗.identity }
  ; _∘_ = λ f g → 
    let module f = Mealy⇒ f 
        module g = Mealy⇒ g
    in record { l = f.l ∘ g.l ; r = f.r ∘ g.r ; u = f.u ∘ g.u 
              ; d-eq = {!   !} ; s-eq = {!   !} }
  ; assoc = assoc , (assoc , assoc)
  ; sym-assoc = sym-assoc , (sym-assoc , sym-assoc)
  ; identityˡ = identityˡ , (identityˡ , identityˡ)
  ; identityʳ = identityʳ , (identityʳ , identityʳ)
  ; identity² = identity² , (identity² , identity²)
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }