{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)

module Categories.Rosen.Functorial.ProElements {o ℓ e} {C : Category o ℓ e} {E : Category (o ⊔ ℓ) (ℓ ⊔ e) e} {M : Monoidal C} (Cl : Closed M) (U : Functor E C) {F : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where

-- Modified category of elements for a bifunctor F : C^op × C → Sets, specialised to MRS-Profunctor.
-- EltsCat is a generic (modified) category-of-elements construction; ElMRS is its instance.
-- Exports: EltsCat, ElMRS, ℝ, U₁.

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Construction.Arrow
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Categories.Category.Construction.TwistedArrow C renaming (Morphism to tMorphism; Morphism⇒ to tMorphism⇒)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁;[_]-commute)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Rosen.Functorial.Core Cl U

open import Function.Equality using (_⟨$⟩_; cong)

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₁)

{- Modified category of elements for a bifunctor Fᵉ : C^op × C → Sets. -}
module EltsCat (Fᵉ : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))) where
  -- Objects of the category of elements: (A, B, el) with el ∈ Fᵉ(A, B).
  record Elts₀ : Set (o ⊔ ℓ ⊔ e) where
    field
      A : Obj
      B : Obj
      el : Setoid.Carrier (Functor.F₀ Fᵉ (A , B))
  -- Morphisms: (l : Y.A ⇒ X.A, r : X.B ⇒ Y.B) such that Fᵉ(l, r)(X.el) ≈ Y.el.
  record Elts⇒ (X Y : Elts₀) : Set (o ⊔ ℓ ⊔ e) where
    module X = Elts₀ X 
    module Y = Elts₀ Y
    field 
      l : Y.A ⇒ X.A 
      r : X.B ⇒ Y.B 
      eqElts : Setoid._≈_ (Functor.F₀ Fᵉ (Y.A , Y.B)) (Functor.F₁ Fᵉ (l , r) ⟨$⟩ X.el) Y.el 
  -- The modified category of elements of Fᵉ.
  Elts : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
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
    ; trans = λ eq eq' → (trans (proj₁ eq) (proj₁ eq')) , (trans (proj₂ eq) (proj₂ eq')) 
    }
    ; ∘-resp-≈ = λ {(fst , snd) (fst' , snd') → (∘-resp-≈ fst' fst) , (∘-resp-≈ snd snd')}
    } 

open EltsCat F public

-- Instantiate the category of elements for MRS-Profunctor.
module MRS = EltsCat MRS-Profunctor

-- The category of elements of MRS-Profunctor.
ElMRS : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
ElMRS = MRS.Elts


-- A functor from ElMRS to Arrow(C) extracting repair maps (without fixing the domain).
ℝ : Functor ElMRS Arr.Arrow
ℝ = record
  { F₀ = λ x → let module x = MRS.Elts₀ x in record { arr = MR2.Φη₀ x.el }
  ; F₁ = λ { {X} {Y} f → 
    let module X = MRS.Elts₀ X 
        module Y = MRS.Elts₀ Y
        module f = MRS.Elts⇒ f 
        open NaturalTransformation
        open HomReasoning
        module XE = MR2 X.el
        module YE = MR2 Y.el
        module Hom  {A} = Functor (appʳ [-,-] A)

        eqΦ : ∀ (m : E.Obj) → [ f.l , id ]₁ ∘ η XE.Φ m ≈ η YE.Φ m
        eqΦ m = proj₂ f.eqElts {x = m}

        lem2 : η XE.Φ XE.e₁ ∘ U.F₁ XE.h ≈ [ id , U.F₁ XE.h ]₁ ∘ η XE.Φ XE.e₀
        lem2 = commute XE.Φ XE.h
  
    in record 
      { dom⇒ = f.r
      ; cod⇒ = [ f.l , f.r ]₁ 
      ; square = begin [ f.l , f.r ]₁ ∘ MR2.Φη₀ f.X.el ≈⟨ ([ [-,-] ]-decompose₁ ⟩∘⟨refl ○ assoc) ⟩ 
                       [ f.l , id ]₁ ∘ [ id , f.r ]₁ ∘ MR2.Φη₀ f.X.el ≈⟨ refl⟩∘⟨ {!    !} ⟩
                       {!   !} ≈⟨ {!  lem2 !} ⟩ 
                       {!   !} ≈⟨ {!   !} ⟩ 
                       MR2.Φη₀ f.Y.el ∘ f.r ∎ }
  }
  ; identity = refl , [-,-].identity
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl , [-,-].homomorphism
  ; F-resp-≈ = λ (f≈gL , f≈gR) → f≈gR , ([-,-].F-resp-≈ (f≈gL , f≈gR))
  } -- record
--   { F₀ = λ x → let module x = MRS.Elts₀ x in record { arr = MR2.Φη₀ x.el }
--   ; F₁ = λ { {X} {Y} f → 
--     let module X = MRS.Elts₀ X 
--         module Y = MRS.Elts₀ Y
--         module f = MRS.Elts⇒ f 
--     in let
--       open NaturalTransformation
--       open HomReasoning

--       module XE = MR2 X.el
--       module YE = MR2 Y.el
--       a = record { arr = XE.f }
--       b = record { arr = XE.f ∘ f.l }
--       c = record { arr = f.r ∘ XE.f ∘ f.l }
--       d = record { arr = YE.f }
--       module Hom  {A} = Functor (appʳ [-,-] A)

--       t₁ : Arr.Morphism⇒ b a
--       t₁ = record { dom⇒ = f.l ; cod⇒ = id ; square = identityˡ }
--       t₂ : Arr.Morphism⇒ b c
--       t₂ = record { dom⇒ = id ; cod⇒ = f.r ; square = Equiv.sym identityʳ }
--       t₃ : Arr.Morphism⇒ d c
--       t₃ = record { dom⇒ = id ; cod⇒ = id ; square = identityˡ ○ Equiv.sym (proj₁ f.eqElts) ○ Equiv.sym identityʳ }

--       eqΦ : ∀ (m : E.Obj) → [ f.l , id ]₁ ∘ η XE.Φ m ≈ η YE.Φ m
--       eqΦ m = proj₂ f.eqElts {x = m}

--       lem1 : η XE.Φ a ≈ η XE.Φ b
--       lem1 = begin
--         η XE.Φ a           ≈˘⟨ identityʳ ⟩
--         η XE.Φ a ∘ id     ≈⟨ commute XE.Φ t₁ ⟩
--         [ id , id ]₁ ∘ η XE.Φ b  ≈⟨ (Hom.identity ⟩∘⟨refl) ⟩ 
--         id ∘ η XE.Φ b     ≈⟨ identityˡ ⟩
--         η XE.Φ b          ∎

--       lem2 : η XE.Φ c ∘ f.r ≈ [ id , f.r ]₁ ∘ η XE.Φ b
--       lem2 = commute XE.Φ t₂

--       lem3 : η YE.Φ c ≈ η YE.Φ d
--       lem3 = begin
--         η YE.Φ c           ≈˘⟨ identityʳ ⟩
--         η YE.Φ c ∘ id     ≈⟨ commute YE.Φ t₃ ⟩
--         [ id , id ]₁ ∘ η YE.Φ d ≈⟨ Hom.identity ⟩∘⟨refl ⟩ 
--         id ∘ η YE.Φ d     ≈⟨ identityˡ ⟩
--         η YE.Φ d          ∎

--       decompose : [ f.l , f.r ]₁ ≈ [ f.l , id ]₁ ∘ [ id , f.r ]₁
--       decompose = [ [-,-] ]-decompose₁

--     in record 
--     { dom⇒ = f.r
--     ; cod⇒ = [ f.l , f.r ]₁  
--     ; square = begin
--       [ f.l , f.r ]₁ ∘ η XE.Φ a
--         ≈⟨ decompose ⟩∘⟨refl ○ assoc ⟩
--       [ f.l , id ]₁ ∘ ([ id , f.r ]₁ ∘ η XE.Φ a)
--         ≈˘⟨ refl⟩∘⟨ Equiv.trans lem2 (refl⟩∘⟨ Equiv.sym lem1) ⟩
--       [ f.l , id ]₁ ∘ (η XE.Φ c ∘ f.r)
--         ≈⟨ sym-assoc ⟩
--       ([ f.l , id ]₁ ∘ η XE.Φ c) ∘ f.r
--         ≈⟨ ∘-resp-≈ (eqΦ c) refl ⟩
--       (η YE.Φ c) ∘ f.r
--         ≈⟨ ∘-resp-≈ lem3 refl ⟩
--       η YE.Φ d ∘ f.r
--         ∎
--     } }
--   ; identity = Equiv.refl , [-,-].identity
--   ; homomorphism = Equiv.refl , [-,-].homomorphism
--   ; F-resp-≈ = λ (f≈gL , f≈gR) → f≈gR , ([-,-].F-resp-≈ (f≈gL , f≈gR))
--   }

-- -- U₁: forgetful functor from ElMRS to the twisted arrow category of C.
-- U₁ : Functor ElMRS TwistedArrow
-- U₁ = record
--   { F₀ = λ {record { A = A ; B = B ; el = el } → 
--    record { arr = MR2.f el }}
--   ; F₁ = λ {record { l = l ; r = r ; eqElts = eqElts } → mor⇒ {dom⇐ = l} {cod⇒ = r} (proj₁ eqElts) }
--   ; identity = let open HomReasoning in 
--     (sym identityˡ ○ identityʳ) , refl
--   ; homomorphism = refl , refl
--   ; F-resp-≈ = λ {A} {B} {f} {g} z → z
--   }