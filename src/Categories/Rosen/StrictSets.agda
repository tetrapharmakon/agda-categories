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
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
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


module _ {F : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))} where

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

