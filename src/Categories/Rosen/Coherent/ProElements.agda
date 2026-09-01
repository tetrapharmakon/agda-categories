{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Level using (Level; _⊔_; lower)

module Categories.Rosen.Coherent.ProElements {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) {c′ e′ : Level} {F : Bifunctor (Category.op C) C (Setoids c′ e′)} where

-- Modified category of elements for a bifunctor F : C^op × C → Sets, specialised to MRS-Profunctor.
-- EltsCat is a generic (modified) category-of-elements construction; ElMRS is its instance.
-- Exports: EltsCat, ElMRS, ⟅_⟆Φ, ⟅_⟆f.

open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.TwistedArrow C renaming (Morphism to tMorphism; Morphism⇒ to tMorphism⇒)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Rosen.Coherent.IdCore Cl
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Function.Equality using (_⟨$⟩_; cong)

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₁)

-- Arrow(C).  Coherent/Core exported this because it needs it to state Cod;
-- Coherent/IdCore has no use for it, so consumers declare it themselves.
-- Private, so that a module importing several of these does not see the same
-- alias arrive from two directions at once.
private
  module Arr = Categories.Category.Construction.Arrow C

{- Modified category of elements for a bifunctor Fᵉ : C^op × C → Sets. -}
-- Level-generalised: Fᵉ may land in Setoids at any levels.  This is needed
-- because the profunctor of id-coherent (M,R)-systems lands in
-- Setoids (o ⊔ ℓ ⊔ e) (o ⊔ e) while the cod-coherent one lands in
-- Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e); both give Elts at the SAME levels, since
-- o ⊔ (o ⊔ ℓ ⊔ e) = ℓ ⊔ (o ⊔ e) = o ⊔ ℓ ⊔ e, so no consumer of ElMRS sees a
-- change.
module EltsCat {c₀ e₀ : Level} (Fᵉ : Bifunctor (Category.op C) C (Setoids c₀ e₀)) where
  -- Objects of the category of elements: (A, B, el) with el ∈ Fᵉ(A, B).
  record Elts₀ : Set (o ⊔ c₀) where
    field
      A : Obj
      B : Obj
      el : Setoid.Carrier (Functor.F₀ Fᵉ (A , B))
  -- Morphisms: (l : Y.A ⇒ X.A, r : X.B ⇒ Y.B) such that Fᵉ(l, r)(X.el) ≈ Y.el.
  record Elts⇒ (X Y : Elts₀) : Set (ℓ ⊔ e₀) where
    module X = Elts₀ X
    module Y = Elts₀ Y
    field
      l : Y.A ⇒ X.A
      r : X.B ⇒ Y.B
      eqElts : Setoid._≈_ (Functor.F₀ Fᵉ (Y.A , Y.B)) (Functor.F₁ Fᵉ (l , r) ⟨$⟩ X.el) Y.el
  -- The modified category of elements of Fᵉ.
  Elts : Category (o ⊔ c₀) (ℓ ⊔ e₀) e
  Elts = record
    { Obj       = Elts₀
    ; _⇒_       = λ X Y → Elts⇒ X Y
    ; _≈_       = λ f g → let module f = Elts⇒ f
                              module g = Elts⇒ g
                          in f.l ≈ g.l × f.r ≈ g.r
    ; id        = λ { {A} → record
      { l = id
      ; r = id
      ; eqElts = Functor.identity Fᵉ (Setoid.refl (Functor.F₀ Fᵉ (Elts₀.A A , Elts₀.B A)))
      }}
    ; _∘_       = λ { {A} {B} {C} f g →
      let module f = Elts⇒ f
          module g = Elts⇒ g
          module F = Functor Fᵉ
          Fff = F.F₀ (f.Y.A , f.Y.B)
          Fgg = F.F₀ (g.X.A , g.X.B)
      in let module SR = SetoidR Fff
             open SR
         in record
         { l = g.l ∘ f.l
         ; r = f.r ∘ g.r
         ; eqElts = begin F.F₁ (g.l ∘ f.l , f.r ∘ g.r) ⟨$⟩ g.X.el ≈⟨ F.homomorphism (Setoid.sym Fgg (Setoid.refl Fgg)) ⟩
                          F.F₁ (f.l , f.r) ⟨$⟩ (F.F₁ (g.l , g.r) ⟨$⟩ g.X.el) ≈⟨ cong (F.F₁ (f.l , f.r)) g.eqElts ⟩
                          F.F₁ (f.l , f.r) ⟨$⟩ f.X.el ≈⟨ f.eqElts ⟩
                          f.Y.el ∎
      } }
    ; assoc     = sym-assoc , assoc
    ; sym-assoc = assoc , sym-assoc
    ; identityˡ = identityʳ , identityˡ
    ; identityʳ = identityˡ , identityʳ
    ; identity² = identity² , identity²
    ; equiv = record
    { refl = refl , refl
    ; sym = λ x → (sym (proj₁ x)) , (sym (proj₂ x))
    ; trans = λ eq eq′ → (trans (proj₁ eq) (proj₁ eq′)) , (trans (proj₂ eq) (proj₂ eq′))
    }
    ; ∘-resp-≈ = λ {(fst , snd) (fst′ , snd′) → (∘-resp-≈ fst′ fst) , (∘-resp-≈ snd snd′)}
    }

open EltsCat F public

-- Instantiate the category of elements for MRS-Profunctor.
module MRS = EltsCat MRS-Profunctor

-- The category of elements of MRS-Profunctor.
ElMRS : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
ElMRS = MRS.Elts


-- ⟅_⟆Φ: the last edge functor.  Extracts the repair map Φ_B from a coherent
-- (M,R)-system, without fixing the domain; this is the paper's ⦇-⦈_Φ of
-- definition_last_edge_functor.
--
-- The cod-coherent version of the square below could not be proved by
-- naturality alone.  Φ's components were indexed by ARROWS, and the four that
-- occur here -- at XE.f, at XE.f ∘ l, at r ∘ XE.f ∘ l, and at YE.f -- are four
-- different indices, so the proof had to build three morphisms of Arr(C)
-- (t₁, t₂, t₃, none of them of the degenerate `1⇒1` shape) and three lemmas to
-- travel between them.  With id-coherent repair data there is one component per
-- OBJECT, all four collapse to the components at X.B and Y.B, and what remains
-- is a single naturality square in C.  The proof is shorter, but it is not the
-- old proof shortened: the reason it works is different.
⟅_⟆Φ : Functor ElMRS Arr.Arrow
⟅_⟆Φ = record
  { F₀ = λ x → let module x = MRS.Elts₀ x in record { arr = MR2.Φη x.el x.B }
  ; F₁ = λ { {X} {Y} f →
    let module X = MRS.Elts₀ X
        module Y = MRS.Elts₀ Y
        module f = MRS.Elts⇒ f
    in let
      open NaturalTransformation
      open HomReasoning

      module XE = MR2 X.el
      module YE = MR2 Y.el

      -- The Φ-component of the element equation, at the object Y.B.
      -- (`lower` strips IdCore's Level.Lift; it has no mathematical content.)
      eqΦ : ∀ (Z : Obj) → [ f.l , id ]₁ ∘ η XE.Φ Z ≈ η YE.Φ Z
      eqΦ Z = proj₂ (lower f.eqElts) {Z}

      decompose : [ f.l , f.r ]₁ ≈ [ f.l , id ]₁ ∘ [ id , f.r ]₁
      decompose = [ [-,-] ]-decompose₁

    in record
    { dom⇒ = f.r
    ; cod⇒ = [ f.l , f.r ]₁
    ; square = begin
      [ f.l , f.r ]₁ ∘ η XE.Φ X.B
        ≈⟨ decompose ⟩∘⟨refl ○ assoc ⟩
      [ f.l , id ]₁ ∘ ([ id , f.r ]₁ ∘ η XE.Φ X.B)
        ≈˘⟨ refl⟩∘⟨ commute XE.Φ f.r ⟩
      [ f.l , id ]₁ ∘ (η XE.Φ Y.B ∘ f.r)
        ≈⟨ sym-assoc ⟩
      ([ f.l , id ]₁ ∘ η XE.Φ Y.B) ∘ f.r
        ≈⟨ ∘-resp-≈ (eqΦ Y.B) refl ⟩
      η YE.Φ Y.B ∘ f.r
        ∎
    } }
  ; identity = Equiv.refl , [-,-].identity
  ; homomorphism = Equiv.refl , [-,-].homomorphism
  ; F-resp-≈ = λ (f≈gL , f≈gR) → f≈gR , ([-,-].F-resp-≈ (f≈gL , f≈gR))
  }

-- ⟅_⟆f: the left leg of the twisted-elements span.  Like Tabulator's [_]f it
-- selects the process map, but it lands in Tw(C) rather than Arr(C), which is
-- what the twisting of ElMRS forces.  Coherent counterpart of
-- Incoherent/Elements.⟅_⟆f.
⟅_⟆f : Functor ElMRS TwistedArrow
⟅_⟆f = record
  { F₀ = λ {record { A = A ; B = B ; el = el } →
   record { arr = MR2.f el }}
  ; F₁ = λ {record { l = l ; r = r ; eqElts = eqElts } → mor⇒ {dom⇐ = l} {cod⇒ = r} (proj₁ (lower eqElts)) }
  ; identity = let open HomReasoning in
    (sym identityˡ ○ identityʳ) , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z
  }
