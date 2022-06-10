{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Coproduct.Indexed.Properties {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.Construction.StrictDiscrete
open import Categories.Category.Cocomplete
open import Categories.Category.Construction.Cocones
open import Categories.Category.Lift
open import Categories.Object.Coproduct.Indexed C
open import Categories.Diagram.Colimit
open import Categories.Functor

import Relation.Binary.PropositionalEquality as ≡

private
  variable
    o′ ℓ′ e′ : Level
  open Category C

module _ {i} (Cocom : Cocomplete (i ⊔ o′) (i ⊔ ℓ′) (i ⊔ e′) C) where

  module _ {I : Set i} (P : I → Obj) where
    private
      Z = liftC o′ ℓ′ e′ (Discrete I)
      F = lift-func C P ∘F unliftF o′ ℓ′ e′ (Discrete I)
      module L = Colimit (Cocom F)

      K : ∀ {Y} → (∀ i → P i ⇒ Y) → Cocone F
      K f = record
        { coapex = record
          { ψ       = λ i → f (lower i)
          ; commute = λ { (lift ≡.refl) → identityʳ }
          }
        }

    Cocomplete⇒IndexedCoproductOf : IndexedCoproductOf P
    Cocomplete⇒IndexedCoproductOf = record
      { X       = L.coapex
      ; ι       = λ i → L.proj (lift i)
      ; ⟨_⟩     = λ f → L.rep (K f)
      ; commute = λ f _ → Cocone⇒.commute (L.rep-cocone (K f))
      ; unique  = λ f g eq → L.initial.!-unique {A = K g} record
        { arr     = f
        ; commute = eq _
        }
      }
