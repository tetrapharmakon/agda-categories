{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.Object.Terminal
open import Level

module Categories.Rosen.Incoherent.Mealy {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product;_⁂_;πʳ)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
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
    l : Y.A ⇒ X.A 
    r : X.B ⇒ Y.B 
    u : mX.E ⇒ mY.E 
    d-eq : u ∘ mX.d ∘ id ⊗₁ l ≈ mY.d ∘ u ⊗₁ id
    s-eq : r ∘ mX.s ∘ id ⊗₁ l ≈ mY.s ∘ u ⊗₁ id

Mealy⇒-≈ : {A B : Mealy₀} → Mealy⇒ A B → Mealy⇒ A B → Set e
Mealy⇒-≈ f g = 
  let module f = Mealy⇒ f 
      module g = Mealy⇒ g
  in
 f.l ≈ g.l × f.l ≈ g.l × f.u ≈ g.u


open HomReasoning
open MR

-- !!! This is not the total category of Mealy automata that 
-- is usually recorded in the literature \cite{foo,bar}
totalMealy : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
totalMealy = record
  { Obj = Mealy₀
  ; _⇒_ = λ s t → Mealy⇒ s t
  ; _≈_ = Mealy⇒-≈
  ; id = record 
    { l = id ; r = id ; u = id 
    ; d-eq = identityˡ ; s-eq = identityˡ }
  ; _∘_ = λ f g → 
    let module f = Mealy⇒ f 
        module g = Mealy⇒ g
    in record { l = g.l ∘ f.l ; r = f.r ∘ g.r ; u = f.u ∘ g.u 
              ; d-eq = (refl⟩∘⟨ pushʳ C (Functor.homomorphism (_ ⊗-))) 
                     ∙ sym-assoc ∙ anti-assoc-4 
                     ∙ (refl⟩∘⟨ pullˡ C g.d-eq) 
                     ∙ (refl⟩∘⟨ pullʳ C (Equiv.sym [ ⊗ ]-commute)) 
                     ∙ sym-assoc-3 ∙ (f.d-eq ⟩∘⟨refl) 
                     ∙ pullʳ C (Equiv.sym (Functor.homomorphism (-⊗ _))) 
              ; s-eq = (refl⟩∘⟨ pushʳ C (Functor.homomorphism (_ ⊗-))) 
                     ∙ sym-assoc ∙ anti-assoc-4 
                     ∙ (refl⟩∘⟨ pullˡ C g.s-eq) 
                     ∙ (refl⟩∘⟨ pullʳ C (Equiv.sym [ ⊗ ]-commute)) 
                     ∙ sym-assoc-3 ∙ (f.s-eq ⟩∘⟨refl) 
                     ∙ pullʳ C (Equiv.sym (Functor.homomorphism (-⊗ _)))  }
  ; assoc = sym-assoc , sym-assoc , assoc
  ; sym-assoc = assoc , assoc , sym-assoc
  ; identityˡ = identityʳ , identityʳ , identityˡ
  ; identityʳ = identityˡ , identityˡ , identityʳ
  ; identity² = identityˡ , identity² , identity²
  ; equiv = record 
    { refl = λ {x} → refl , refl , refl
    ; sym = λ x → (sym (x .proj₁)) , sym (x .proj₁) , sym (x .proj₂ .proj₂)
    ; trans = λ x x₁ → (trans (x .proj₁) (x₁ .proj₁)) , trans (x .proj₁) (x₁ .proj₁) , (trans (x .proj₂ .proj₂) (x₁ .proj₂ .proj₂))
    } 
  ; ∘-resp-≈ = λ x x₁ → (∘-resp-≈ (x₁ .proj₁) (x .proj₁)) , (∘-resp-≈ (x₁ .proj₁) (x .proj₁)) , ∘-resp-≈ (x .proj₂ .proj₂) (x₁ .proj₂ .proj₂)
  }