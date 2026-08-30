{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

-- The category of Sets as a Cartesian closed monoidal category.
-- Everything is built from the standard categorical structure on Sets:
-- products, exponentials, evaluation and currying.
-- Used to instantiate the Rosen constructions concretely.
-- Exports: Sets-CCC, Sets-Monoidal, Sets-Closed.

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; sym; trans)

open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.CartesianClosed as CCC
open import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed
open import Categories.Functor.Bifunctor using (Bifunctor)

module Categories.Rosen.Cartesian.Sets where

-- Function extensionality: a standard axiom for reasoning about Sets (two
-- pointwise-equal functions are equal).  This is an ordinary axiom, not a
-- *sorry*-style placeholder.
postulate
  extensionality : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
                 → (∀ x → f x ≡ g x) → f ≡ g

module _ {o : Level} where
  private
    S = Sets o

  -- The evident canonical Cartesian-closed structure on Sets: products,
  -- terminal object, exponentials, evaluation and currying.
  Sets-Canonical : Canonical.CartesianClosed S
  Sets-Canonical = record
    { ⊤    = ⊤
    ; _×_  = λ A B → A × B
    ; !    = λ _ → tt
    ; π₁   = proj₁
    ; π₂   = proj₂
    ; ⟨_,_⟩ = λ f g x → (f x , g x)
    ; !-unique = λ f {x} → refl
    ; π₁-comp  = λ {x} → refl
    ; π₂-comp  = λ {x} → refl
    ; ⟨,⟩-unique = λ {f g h} p₁ p₂ {x} →
        cong₂ _,_ (sym (p₁ {x})) (sym (p₂ {x}))
    ; _^_   = λ A B → B → A
    ; eval  = λ { (f , a) → f a }
    ; curry = λ f c a → f (c , a)
    ; eval-comp    = λ {f} {x} → refl
    ; curry-resp-≈ = λ eq {c} → extensionality λ a → eq {c , a}
    ; curry-unique = λ {f g} h {c} → extensionality λ a → h {(c , a)}
    }

  -- The Cartesian-closed structure on Sets derived from the canonical one.
  Sets-CCC : CCC.CartesianClosed S
  Sets-CCC = Canonical.Equivalence.fromCanonical _ Sets-Canonical


module Sets-MonoidalClosed {o : Level} where
  private
    S = Sets o
    module CMC = CCC.CartesianMonoidalClosed S (Sets-CCC {o})
    open CMC using (closedMonoidal)
    open CartesianMonoidal (CCC.CartesianClosed.cartesian (Sets-CCC {o})) using (monoidal)

  -- The induced monoidal structure on Sets, with the Cartesian product.
  Sets-Monoidal : Monoidal S
  Sets-Monoidal = monoidal

  -- The induced closed structure: exponentiating by the product (function
  -- types).
  Sets-Closed : Closed Sets-Monoidal
  Sets-Closed = closedMonoidal
