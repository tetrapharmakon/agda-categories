{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Coherent.CodCoherentEqualIdCoherent
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- cod-coherent (M,R)-systems are the same thing as id-coherent ones.
--
-- This module is the Agda content of the lemma the paper calls `cod_lax_epi`.
-- The paper states there that cod : Arr(C) → C is a lax epimorphism and, "as a
-- consequence", that id-natural and cod-natural (M,R)-systems correspond.  What
-- is actually needed downstream --- and what is proved here --- is that second
-- statement, directly and without going through the general one.
--
-- WHY IT IS NOT A TRIVIALITY.  A cod-coherent Φ has a component at every ARROW
-- of C and is natural over the whole of Arr(C); an id-coherent Φ has a component
-- at every OBJECT and is natural over C.  The former is a priori more data.  The
-- decomposition in Core's `Naturalities` module makes the difference precise:
-- naturality over Arr(C) splits into three specialisations, and only `nat-1⇒1`
-- is id-naturality.  The surplus is `nat-u⇒1`, which says that Φ's component at
-- an arrow u depends on nothing but cod u --- that is, that Φ is constant on
-- each slice C/Y.  The correspondence holds because that surplus is forced, not
-- because the two notions are the same by definition.
--
-- Exports: Φ-const-on-slices (the surplus, named), cod⇒id, id⇒cod, the two
-- round-trips, and the packaged bijection MR2 A B ≅ (A ⇒ B) × Nat(id,[A,-]).

open import Data.Product using (_,_; proj₁; proj₂; _×_; Σ)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

open import Categories.Rosen.Coherent.Core Cl
import Categories.Rosen.Coherent.IdCore
module Id = Categories.Rosen.Coherent.IdCore Cl

------------------------------------------------------------------------
-- The surplus of cod-naturality over id-naturality, isolated and named.

-- Φ-const-on-slices: the component of a cod-coherent Φ at an arrow u : X ⇒ Y
-- coincides with its component at id_Y.  Equivalently: Φ factors through the
-- codomain, so that whiskering with cod loses nothing.
--
-- This is `Naturalities.nat-u⇒1` of Core, re-exported under a name that says
-- what it means.  It is the whole content of the paper's `cod_lax_epi`: every
-- statement below is a formal consequence of it.
Φ-const-on-slices : ∀ {A B} (ξ : MR2 A B) {X Y} (u : X ⇒ Y) →
                    MR2.Φη ξ (record { arr = id {Y} }) ≈ MR2.Φη ξ (record { arr = u })
Φ-const-on-slices ξ u = Naturalities.nat-u⇒1 ξ u

------------------------------------------------------------------------
-- The two directions.  Both already live in Core; they are given local
-- names here so that this module reads as the statement of the bijection.

-- Read a cod-coherent system at the identity arrows: an id-coherent Φ.
cod⇒id : ∀ {A B} (ξ : MR2 A B) → NaturalTransformation idF ([_,-] A)
cod⇒id = NICod⇒NIid

-- Extend an id-coherent Φ along cod: its component at an arrow is its
-- component at that arrow's codomain.
id⇒cod : ∀ {A B} → (f : A ⇒ B) → NaturalTransformation idF ([_,-] A) → MR2 A B
id⇒cod = NIid⇒NICod

------------------------------------------------------------------------
-- Round trip one: extending and then restricting is the identity.
--
-- This direction is formal.  The extension's component at the arrow id_X is by
-- definition φ's component at cod (id_X) = X, so the two sides are the same
-- term and nothing has to be proved.

cod⇒id∘id⇒cod : ∀ {A B} (f : A ⇒ B) (φ : NaturalTransformation idF ([_,-] A)) →
                cod⇒id (id⇒cod f φ) ≃ φ
cod⇒id∘id⇒cod f φ = Equiv.refl

------------------------------------------------------------------------
-- Round trip two: restricting and then extending is the identity.
--
-- This is the direction with content.  The extension's component at an arrow
-- u : X ⇒ Y is Φ's component at id_Y, and recovering Φ's component at u itself
-- is exactly Φ-const-on-slices.

id⇒cod∘cod⇒id : ∀ {A B} (ξ : MR2 A B) →
                MR2.Φ (id⇒cod (MR2.f ξ) (cod⇒id ξ)) ≃ MR2.Φ ξ
id⇒cod∘cod⇒id ξ {m} = Φ-const-on-slices ξ (Arr.Morphism.arr m)

-- ... and the process map is untouched, so the round trip is the identity on
-- the whole system, not merely on its repair component.
id⇒cod∘cod⇒id-f : ∀ {A B} (ξ : MR2 A B) → MR2.f (id⇒cod (MR2.f ξ) (cod⇒id ξ)) ≈ MR2.f ξ
id⇒cod∘cod⇒id-f ξ = Equiv.refl

------------------------------------------------------------------------
-- The bijection, packaged.
--
-- MR2 A B --- a process map together with a cod-coherent repair family --- is
-- in bijection with a process map together with an id-coherent one.  The two
-- setoids below are the carriers of the two profunctors of coherent
-- (M,R)-systems, so this is the object part of their comparison.

IdMR2 : Obj → Obj → Set (o ⊔ ℓ ⊔ e)
IdMR2 A B = (A ⇒ B) × NaturalTransformation idF ([_,-] A)

-- NOTE ON LEVELS, which matters for anything built on top of this module.
-- The carriers agree: MR2 A B and IdMR2 A B both live in Set (o ⊔ ℓ ⊔ e).
-- The EQUALITIES do not.  Cod-world Φ ≃ Φ′ quantifies over Obj (Arrow C), which
-- is Set (o ⊔ ℓ), so it lands in Set (o ⊔ ℓ ⊔ e); id-world φ ≃ ψ quantifies over
-- Obj C only, so it lands in Set (o ⊔ e).  The id-world relation is strictly
-- smaller --- which is the point, there is less data --- but Agda levels do not
-- subsume, so a profunctor of id-coherent systems lands in
-- Setoids (o ⊔ ℓ ⊔ e) (o ⊔ e), NOT in Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e).
-- Downstream modules whose level parameters are hard-wired to the latter
-- (Coherent/ProElements.agda) must be generalised, not merely re-pointed.
IdMR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ e)
IdMR2-Setoid A B = record
  { Carrier = IdMR2 A B
  ; _≈_ = λ (f , φ) (g , ψ) → (f ≈ g) × (φ ≃ ψ)
  ; isEquivalence = record
    { refl  = Equiv.refl , (λ {x} → Equiv.refl)
    ; sym   = λ (p , k) → Equiv.sym p , Equiv.sym k
    ; trans = λ (p₁ , h) (p₂ , k) → Equiv.trans p₁ p₂ , Equiv.trans h k
    }
  }

to   : ∀ {A B} → MR2 A B → IdMR2 A B
to ξ = MR2.f ξ , cod⇒id ξ

from : ∀ {A B} → IdMR2 A B → MR2 A B
from (f , φ) = id⇒cod f φ

to∘from : ∀ {A B} (x : IdMR2 A B) →
          (proj₁ (to (from x)) ≈ proj₁ x) × (proj₂ (to (from x)) ≃ proj₂ x)
to∘from (f , φ) = Equiv.refl , cod⇒id∘id⇒cod f φ

from∘to : ∀ {A B} (ξ : MR2 A B) →
          (MR2.f (from (to ξ)) ≈ MR2.f ξ) × (MR2.Φ (from (to ξ)) ≃ MR2.Φ ξ)
from∘to ξ = id⇒cod∘cod⇒id-f ξ , id⇒cod∘cod⇒id ξ

------------------------------------------------------------------------
-- The same bijection, stated between the two actual definitions.
--
-- Above, the id-coherent side was a bare product; here it is the record
-- Coherent/IdCore.agda defines.  This is the statement the migration of the
-- rest of the tree relies on: a cod-coherent (M,R)-system and an id-coherent
-- one are the same thing, so re-proving a downstream module in the id world
-- cannot change which theorems are available --- only how they are proved.

toId : ∀ {A B} → MR2 A B → Id.MR2 A B
toId ξ = Id.⟪ MR2.f ξ , cod⇒id ξ ⟫

fromId : ∀ {A B} → Id.MR2 A B → MR2 A B
fromId ζ = id⇒cod (Id.MR2.f ζ) (Id.MR2.Φ ζ)

toId∘fromId : ∀ {A B} (ζ : Id.MR2 A B) →
              (Id.MR2.f (toId (fromId ζ)) ≈ Id.MR2.f ζ)
            × (Id.MR2.Φ (toId (fromId ζ)) ≃ Id.MR2.Φ ζ)
toId∘fromId ζ = Equiv.refl , cod⇒id∘id⇒cod (Id.MR2.f ζ) (Id.MR2.Φ ζ)

fromId∘toId : ∀ {A B} (ξ : MR2 A B) →
              (MR2.f (fromId (toId ξ)) ≈ MR2.f ξ)
            × (MR2.Φ (fromId (toId ξ)) ≃ MR2.Φ ξ)
fromId∘toId ξ = id⇒cod∘cod⇒id-f ξ , id⇒cod∘cod⇒id ξ
