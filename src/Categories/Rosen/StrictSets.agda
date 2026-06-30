{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_;Σ)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong) renaming (_∘_ to _∗_)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute; [_]-decompose₁)
open import Categories.NaturalTransformation using (NaturalTransformation;_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,_])
module Categories.Rosen.StrictSets {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

-- open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

-- import Categories.Morphism.Reasoning as MR
-- open HomReasoning 
-- open MR

import Reason
open Reason C

open import Categories.Rosen.Core Cl
open import Categories.Functor.Profunctor.Tabulator

-- open import Categories.Category.Instance.Sets

{-
MRS-SetP : Bifunctor (Category.op C) C (Sets (o ⊔ ℓ ⊔ e))
MRS-SetP = record
  { F₀ = λ {(A , B) → MR2 A B}
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) ⟪ f , ϕ ⟫ → let module ϕ = NaturalTransformation ϕ in
    ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ ϕ ⟫}
  ; identity = λ { {(X , Y)} {⟪ f , phi ⟫} →  {! identityˡʳ !}}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }
-}
-- open import Categories.Category.Construction.Elements using (Elements)

-- a modified category of elements definition


module EltsMod {F : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where

  record Elts₀ : Set (o ⊔ ℓ ⊔ e) where
    field
      A : Obj
      B : Obj
      el : Setoid.Carrier (Functor.F₀ F (A , B))

  record Elts⇒ (X Y : Elts₀) : Set (o ⊔ ℓ ⊔ e) where
    module X = Elts₀ X 
    module Y = Elts₀ Y
    field 
      l : Y.A ⇒ X.A 
      r : X.B ⇒ Y.B 
      eqElts : Setoid._≈_ (Functor.F₀ F (Y.A , Y.B)) (Functor.F₁ F (l , r) ⟨$⟩ X.el) Y.el 

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
      ; eqElts = Functor.identity F (Setoid.refl (Functor.F₀ F (Elts₀.A A , Elts₀.B A)))
      }}
    ; _∘_       = λ { {A} {B} {C} f g → 
      let module f = Elts⇒ f 
          module g = Elts⇒ g
          module F = Functor F
          Fff = F.F₀ (f.Y.A , f.Y.B)
          Fgg = F.F₀ (g.X.A , g.X.B)
          open SetoidR Fff
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

ElMRS : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
ElMRS = EltsMod.Elts {F = MRS-Profunctor}


-- a functor that extracts repair maps without the assumption to fix the domain
ℝ : Functor ElMRS Arr.Arrow
ℝ = record
  { F₀ = λ x → let module x = EltsMod.Elts₀ x in record { arr = MR2.ϕη₀ x.el }
  ; F₁ = λ { {X} {Y} f → 
    let module X = EltsMod.Elts₀ X 
        module Y = EltsMod.Elts₀ Y
        module f = EltsMod.Elts⇒ f 
    in let
      open NaturalTransformation
      open HomReasoning

      module XE = MR2 X.el
      module YE = MR2 Y.el
      a = record { arr = XE.f }
      b = record { arr = XE.f ∘ f.l }
      c = record { arr = f.r ∘ XE.f ∘ f.l }
      d = record { arr = YE.f }
      module Hom  {A} = Functor (appʳ [-,-] A)
      module Hom' {A} = Functor (appˡ [-,-] A)

      t₁ : Arr.Morphism⇒ b a
      t₁ = record { dom⇒ = f.l ; cod⇒ = id ; square = identityˡ }
      t₂ : Arr.Morphism⇒ b c
      t₂ = record { dom⇒ = id ; cod⇒ = f.r ; square = Equiv.sym identityʳ }
      t₃ : Arr.Morphism⇒ d c
      t₃ = record { dom⇒ = id ; cod⇒ = id ; square = identityˡ ○ Equiv.sym (proj₁ f.eqElts) ○ Equiv.sym identityʳ }

      eqϕ : ∀ (m : Arr.Morphism) → [ f.l , id ]₁ ∘ η XE.ϕ m ≈ η YE.ϕ m
      eqϕ m = proj₂ f.eqElts {x = m}

      lem1 : η XE.ϕ a ≈ η XE.ϕ b
      lem1 = begin
        η XE.ϕ a           ≈˘⟨ identityʳ ⟩
        η XE.ϕ a ∘ id     ≈⟨ commute XE.ϕ t₁ ⟩ -- commute XE.ϕ t₁ ⟩
        [ id , id ]₁ ∘ η XE.ϕ b  ≈⟨ (Hom.identity ⟩∘⟨refl) ⟩ 
        id ∘ η XE.ϕ b     ≈⟨ identityˡ ⟩
        η XE.ϕ b          ∎

      lem2 : η XE.ϕ c ∘ f.r ≈ [ id , f.r ]₁ ∘ η XE.ϕ b
      lem2 = commute XE.ϕ t₂

      lem3 : η YE.ϕ c ≈ η YE.ϕ d
      lem3 = begin
        η YE.ϕ c           ≈˘⟨ identityʳ ⟩
        η YE.ϕ c ∘ id     ≈⟨ commute YE.ϕ t₃ ⟩ -- commute YE.ϕ t₃ ⟩
        [ id , id ]₁ ∘ η YE.ϕ d ≈⟨ Hom.identity ⟩∘⟨refl ⟩ 
        id ∘ η YE.ϕ d     ≈⟨ identityˡ ⟩
        η YE.ϕ d          ∎

      decompose : [ f.l , f.r ]₁ ≈ [ f.l , id ]₁ ∘ [ id , f.r ]₁
      decompose = [ [-,-] ]-decompose₁

    in record 
    { dom⇒ = f.r
    ; cod⇒ = [ f.l , f.r ]₁  
    ; square = begin
      [ f.l , f.r ]₁ ∘ η XE.ϕ a
        ≈⟨ decompose ⟩∘⟨refl ○ assoc ⟩
      [ f.l , id ]₁ ∘ ([ id , f.r ]₁ ∘ η XE.ϕ a)
        ≈˘⟨ refl⟩∘⟨ Equiv.trans lem2 (refl⟩∘⟨ Equiv.sym lem1) ⟩
      [ f.l , id ]₁ ∘ (η XE.ϕ c ∘ f.r)
        ≈⟨ sym-assoc ⟩
      ([ f.l , id ]₁ ∘ η XE.ϕ c) ∘ f.r
        ≈⟨ ∘-resp-≈ (eqϕ c) refl ⟩
      (η YE.ϕ c) ∘ f.r
        ≈⟨ ∘-resp-≈ lem3 refl ⟩
      η YE.ϕ d ∘ f.r
        ∎
    } }
  ; identity = Equiv.refl , [-,-].identity
  ; homomorphism = Equiv.refl , [-,-].homomorphism
  ; F-resp-≈ = λ (f≈gL , f≈gR) → f≈gR , ([-,-].F-resp-≈ (f≈gL , f≈gR))
  }