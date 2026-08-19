{-# OPTIONS --without-K --safe #-}

-- The product category Set × Set: objects are pairs of sets, morphisms
-- are pairs of functions, everything else computed pointwise. It is
-- Cartesian monoidal because Sets itself is: since Product C D builds
-- all of its structure componentwise, exhibiting a terminal object and
-- binary products on Set × Set is pure bookkeeping (pairing Sets' own
-- terminal object and binary products), and the real work -- associator/
-- unitor/triangle/pentagon coherence for the induced tensor -- is
-- discharged for free by `CartesianMonoidal.monoidal`.

module Categories.Rosen.SetSet where

open import Level using (Level; suc)

open import Categories.Category using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Instance.Sets using (module Product)
import Categories.Category.Product as CatProduct
open import Categories.Object.Terminal using (Terminal)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong₂)

-- The product category Set × Set.
SetSet : (o : Level) → Category (suc o) o o
SetSet o = CatProduct.Product (Sets o) (Sets o)

module _ (o : Level) where
  module cart = Cartesian (Product.Sets-is {o})
  open cart using (terminal; products)

  module terminal = Terminal terminal
  open terminal

  module products = BinaryProducts products
  open products

  open import Categories.Object.Product (SetSet o) using (Product)

  pairProduct : ∀ {A B} → Product A B
  pairProduct {A , A′} {B , B′} = record
    { A×B      = A × B , A′ × B′
    ; π₁       = π₁ , π₁
    ; π₂       = π₂ , π₂
    ; ⟨_,_⟩    = λ (f , f′) (g , g′) → ⟨ f , g ⟩ , ⟨ f′ , g′ ⟩
    ; project₁ = refl , refl
    ; project₂ = refl , refl
    ; unique   = λ { (p , p′) (q , q′) →
        (λ {x} → sym (cong₂ _,_ (p {x}) (q {x}))) , (λ {x} → sym (cong₂ _,_ (p′ {x}) (q′ {x})))
      }
    }

  SetSet-BinaryProducts : BinaryProducts (SetSet o)
  SetSet-BinaryProducts = record { product = pairProduct }

  SetSet-Terminal : Terminal (SetSet o)
  SetSet-Terminal = record
    { ⊤ = ⊤ , ⊤
    ; ⊤-is-terminal = record
      { ! = ! , !
      ; !-unique = pairUnique
      }
    }
    where
    open Category (SetSet o) using (_⇒_; _≈_)

    pairUnique : ∀ {A} (f : A ⇒ (⊤ , ⊤)) → (! , !) ≈ f
    pairUnique (f , g) = refl , refl

  SetSet-Cartesian : Cartesian (SetSet o)
  SetSet-Cartesian = record
    { terminal = SetSet-Terminal
    ; products = SetSet-BinaryProducts
    }

  -- Set × Set is Cartesian monoidal.
  SetSet-Monoidal : Monoidal (SetSet o)
  SetSet-Monoidal = CartesianMonoidal.monoidal SetSet-Cartesian

  -- Set × Set is Cartesian closed. (stub: Sets itself is CCC, with
  -- exponentials built componentwise the same way products were above;
  -- not proved here.)
  SetSet-CartesianClosed : CartesianClosed (SetSet o)
  SetSet-CartesianClosed = {! !}
