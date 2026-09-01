{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Adjunction.TotRep {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open Category C

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor;_∘F_)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Rosen.Coherent.IdCore Cl
open import Categories.Rosen.Coherent.ProElements Cl {F = MRS-Profunctor}
open import Categories.Rosen.Coherent.Repairs Cl
open import Categories.Rosen.Coherent.TotalCategory Cl using (tot⇒; total; [_,_∥_,_])

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)
open HomReasoning
open MR


-- The coreflection between the total category (see TotalCategory.agda)
-- and the repair fibration (see Repairs.agda).
--   K   : total → repairs  forgets the metabolic map f, keeping only Φ;
--   𝕁   : repairs → total  includes a repair system as the (M,R)-system
--                          with identity metabolic map (l = r = u);
--   𝕁⊣K : these are adjoint (𝕁 ⊣ K), the unit being the identity, so
--                          repairs coreflects into the total category.
-- Exports: K, 𝕁, 𝕁⊣K.

-- The coreflector of total on the category of repairs
-- (drops the metabolic map f, keeping only the repair component Φ).
K : Functor total repairs
K = record
  { F₀ = λ x →
      let module x = tab₀ x
          module ξx = MR2 x.ξ
      in record { A = x.L ; Φ = ξx.Φ }
  ; F₁ = λ { {x} {y} f →
      let module x = tab₀ x
          module y = tab₀ y
          module f = tot⇒ f
      in record { u = f.l ; eq = f.eqΦ } }
  ; identity = λ {A} → Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = proj₁
  }

-- (The former `[_,Cod]₁`, the precomposition of nHom with Cod, is gone: with
--  id-coherent repair data there is nothing to whisker with, and `nHom u` is
--  already the natural transformation [ A′ ,-] ⇒ [ A ,-] that is wanted.)

-- the inclusion of repairs in total
-- (a repair system (A, Φ) becomes the (M,R)-system (A, A) with identity
--  metabolic map id : A ⇒ A and repair Φ).
𝕁 : Functor repairs total
𝕁 = record
  { F₀ = λ {(record { A = A ; Φ = Φ }) → (A , A) ∣ ⟪ id , Φ ⟫}
  ; F₁ = λ { {X} {Y} f → let module f = rep⇒ f in
  [ f.u , f.u
  -- Naturality is now over C: one square per morphism h : X ⇒ Y, where before
  -- there was one per morphism of Arr(C).  The chain has the same three steps,
  -- but each is a different square.
  ∥ id-comm C , (λ {P} {Q} h →
      let module X₀ = rep₀ X
          module Y₀ = rep₀ Y
          module ΦX = NT X₀.Φ
          module ΦY = NT Y₀.Φ
      in
      begin
        (NT.η (nHom f.u ∘ᵥ Y₀.Φ) Q) ∘ h                          ≈⟨ assoc ○ (refl⟩∘⟨ ΦY.commute h) ○ sym-assoc ⟩
        (NT.η (nHom f.u) Q ∘ Functor.F₁ [ Y₀.A ,-] h) ∘ ΦY.η P   ≈⟨ (∘-resp-≈ (NT.commute (nHom f.u) h) Equiv.refl) ○ assoc ⟩
        Functor.F₁ [ X₀.A ,-] h ∘ (NT.η (nHom f.u) P ∘ ΦY.η P)   ≈⟨ refl⟩∘⟨ f.eq {x = P} ⟩
        Functor.F₁ [ X₀.A ,-] h ∘ ΦX.η P                         ∎) ]}
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x , x
  }

-- 𝕁 and K are adjoint; since the unit is the identity, 𝕁 is full and
-- faithful, so total coreflects onto the category of repairs.
-- J and K are adjoint
𝕁⊣K : 𝕁 ⊣ K
-- note that J is full and faithful (unit is id)
𝕁⊣K = record
 { unit = ntHelper (record
   { η = λ {record { A = A ; Φ = Φ } → record
      { u = id
      ; eq =  elimˡ C [-,-].identity
      } }
    ; commute = λ f →
        let module f = rep⇒ f in
        begin
          id ∘ f.u ≈⟨ identityˡ ⟩
          f.u      ≈⟨ Equiv.sym identityʳ ⟩
          f.u ∘ id ∎ })
  ; counit = ntHelper (record
    { η = λ {((L , R) ∣ ξ) →
      [ id , MR2.f ξ
      ∥ Equiv.refl
     , (λ {X} {Y} h →
           let module Φ = NT (MR2.Φ ξ)
           in
           begin
             (([ id , id ]₁ ∘ Φ.η Y) ∘ h) ≈⟨ assoc ○ (elimˡ C [-,-].identity) ⟩
             Φ.η Y ∘ h                    ≈⟨ Φ.commute h ⟩
             Functor.F₁ [ L ,-] h ∘ Φ.η X ∎) ] }
    ; commute = λ f →
        let module f = tot⇒ f in
        ( Equiv.trans identityˡ (Equiv.sym identityʳ)
        , Equiv.sym f.eqf ) })
  ; zig = identity² , identity²
  ; zag = λ {B} → identity²
  }
