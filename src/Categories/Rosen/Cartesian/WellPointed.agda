{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level

module Categories.Rosen.Cartesian.WellPointed (o : Level) where

-- Well-pointedness of Sets, and the one consequence the Rosen development
-- needs from it.
--
-- This module is deliberately separate from Cartesian/Adjoints.agda.  Nothing
-- here mentions (M,R)-systems: it is a fact about Sets and about natural
-- transformations id ⇒ [A,-], and it was only ever stated inside the adjunction
-- file because that is where it happened to be needed.  Keeping it apart makes
-- visible which hypothesis the adjunctions actually rest on, which is the whole
-- point --- see the note below.
--
-- THE FACT.  1 is a generator of Sets: a map is determined by its action on
-- points.  Consequently a natural transformation α : id ⇒ [A,-] is determined
-- by naturality at points, and is forced to be the constant family
-- z ↦ (λ _ → z).  Any two such transformations therefore agree.
--
-- WHY THIS MATTERS, and why it is not a technicality.  In the earlier
-- cod-coherent development the corresponding statement --- that
-- Nat(Cod, [A,-]∘Cod) is a singleton --- was proved by representability: Cod is
-- represented in Arr(Sets) by the terminal arrow ∅ → 1.  That argument is an
-- accident of the shape of Arr(Sets) and it concealed which hypothesis was
-- doing the work.  Stated as below, the hypothesis is explicit, and one can
-- read off immediately why the paper's lem_onset_trivials is a statement about
-- Set in particular, and why cartesian_w_nontrivial_MRs can exhibit a genuine
-- counterexample in the topos of C₂-sets: there 1 is not a generator, so
-- nothing below applies.
--
-- Exports: point, α-is-const, Nat-id-hom-unique.

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Rosen.Cartesian.Sets

open Sets-MonoidalClosed {o}

private
  S : Category (suc o) o o
  S = Sets o

  Cl : Closed Sets-Monoidal
  Cl = Sets-Closed

open Category S
open Closed Cl using ([_,-])

open NaturalTransformation using (η; commute)

-- The one-point set at level o, and the point of X that names an element.
𝟙 : Obj
𝟙 = Lift o ⊤

point : {X : Obj} → X → (𝟙 ⇒ X)
point z _ = z

-- Every natural transformation id ⇒ [A,-] is the constant family.
--
-- Naturality at `point z : 1 ⇒ X` reads α_X (z) = point z ∘ α_𝟙(•); the
-- right-hand side ignores its argument, so α_X (z) is the constant map at z.
-- That single square is the whole proof: no extensionality is needed, because
-- the two sides are already equal as functions.
α-is-const : ∀ {A X : Obj} (α : NaturalTransformation idF ([ A ,-])) (z : X) →
             η α X z ≡ (λ _ → z)
α-is-const α z = commute α (point z) {lift tt}

-- Hence Nat(id, [A,-]) has at most one element.
Nat-id-hom-unique : ∀ (A : Obj) (Φ ψ : NaturalTransformation idF ([ A ,-])) → Φ ≃ ψ
Nat-id-hom-unique A Φ ψ {X} {z} = ≡.trans (α-is-const Φ z) (≡.sym (α-is-const ψ z))
