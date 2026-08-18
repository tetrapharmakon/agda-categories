{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ʳ_)
open import Level using (_⊔_)

module Categories.Rosen.MetabolicClosure
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Categories.Rosen.Coherent.Core Cl using
  (MR2; Cod; nHom; NICod⇒NIid; u⇒1)

import Reason
open Reason C
open HomReasoning
open Closed Cl using
  (adjoint; unit; unitorˡ; [-,-]; [_,_]₀; [_,_]₁; [_,-]; _⊗₁_; -⊗_)
open MR2

-- A generalized element
-- b₀ : I ⇒ B is a closure point when evaluating the uncurried repair at
-- b₀ recovers the process f.
-- For convenience we state the closure condition in two ways (equivalent under adjunction identities)
record MetabolicClosure {A B : Obj} (ξ : MR2 A B) : Set (ℓ ⊔ e) where
  field
    b₀ : unit ⇒ B
    closureL : Φη₀ ξ ∘ b₀ ≈ adjoint.Ladjunct (f ξ ∘ unitorˡ.from)

open MetabolicClosure

fact : {A B : Obj} {ξ : MR2 A B} → (𝕓 : MetabolicClosure ξ) → adjoint.Radjunct (Φη₀ ξ) ∘ (b₀ 𝕓 ⊗₁ id) ≈ f ξ ∘ unitorˡ.from
fact {A} {ξ = ξ} 𝕓 =
  let module 𝕓 = MetabolicClosure 𝕓
      module -⊗A = Functor (-⊗ A)
  in begin
    adjoint.Radjunct (Φη₀ ξ) ∘ (𝕓.b₀ ⊗₁ id)                  ≈⟨ assoc ⟩
    adjoint.counit.η _ ∘ (Φη₀ ξ ⊗₁ id) ∘ (𝕓.b₀ ⊗₁ id)        ≈˘⟨ refl⟩∘⟨ -⊗A.homomorphism ⟩
    adjoint.Radjunct (Φη₀ ξ ∘ 𝕓.b₀)                          ≈⟨ adjoint.Radjunct-resp-≈ 𝕓.closureL ⟩
    adjoint.Radjunct (adjoint.Ladjunct (f ξ ∘ unitorˡ.from)) ≈⟨ adjoint.RLadjunct≈id ⟩
    f ξ ∘ unitorˡ.from
      ∎

-- The component of the repair family at the identity process on X.
Φ-id : ∀ {A B : Obj} → MR2 A B → (X : Obj) → X ⇒ [ A , X ]₀
Φ-id ξ X = NaturalTransformation.η (NICod⇒NIid ξ) X

-- The repair component at f agrees with the component at id_B.
Φ-id≈Φ-f : ∀ {A B : Obj} (ξ : MR2 A B) → Φ-id ξ B ≈ Φη₀ ξ
Φ-id≈Φ-f ξ =
  sym identityʳ
    ∙ Φcommute ξ (u⇒1 (f ξ))
    ∙ ∘-resp-≈ˡ [-,-].identity
    ∙ identityˡ

-- Currying commutes with postcomposition by the process.
curry-process : ∀ {A B : Obj} (g : A ⇒ B) →
  [ id , g ]₁ ∘ adjoint.Ladjunct unitorˡ.from
    ≈ adjoint.Ladjunct (g ∘ unitorˡ.from)
curry-process {A} g =
  let module HomA = Functor ([_,-] A)
  in begin
    [ id , g ]₁ ∘ adjoint.Ladjunct unitorˡ.from               ≈⟨ sym-assoc ⟩
    ([ id , g ]₁ ∘ [ id , unitorˡ.from ]₁) ∘ adjoint.unit.η _ ≈˘⟨ HomA.homomorphism ⟩∘⟨refl ⟩
    adjoint.Ladjunct (g ∘ unitorˡ.from)                       ∎
            
-- A universal closure point is sent to the identity process by the repair
-- component at id_A.  This condition depends only on A and the repair family.
record UnivClosurePoint {A B : Obj} (ξ : MR2 A B) : Set (ℓ ⊔ e) where
  field
    a₀ : unit ⇒ A
    univClosure : Φ-id ξ A ∘ a₀ ≈ adjoint.Ladjunct unitorˡ.from

Univ⇒Metabolic : {A B : Obj} {ξ : MR2 A B} (𝕒 : UnivClosurePoint ξ) → MetabolicClosure ξ
Univ⇒Metabolic {A} {B} {ξ} 𝕒 =
  let module 𝕒 = UnivClosurePoint 𝕒
      φ = NICod⇒NIid ξ
  in record
  { b₀ = f ξ ∘ 𝕒.a₀
  ; closureL = begin
      Φη₀ ξ ∘ f ξ ∘ 𝕒.a₀                            ≈⟨ ∘-resp-≈ˡ (sym (Φ-id≈Φ-f ξ)) ⟩
      Φ-id ξ B ∘ f ξ ∘ 𝕒.a₀                         ≈⟨ sym-assoc ⟩
      (Φ-id ξ B ∘ f ξ) ∘ 𝕒.a₀                       ≈⟨ NaturalTransformation.commute φ (f ξ) ⟩∘⟨refl ⟩
      ([ id , f ξ ]₁ ∘ Φ-id ξ A) ∘ 𝕒.a₀             ≈⟨ assoc ⟩
      [ id , f ξ ]₁ ∘ Φ-id ξ A ∘ 𝕒.a₀               ≈⟨ refl⟩∘⟨ 𝕒.univClosure ⟩
      [ id , f ξ ]₁ ∘ adjoint.Ladjunct unitorˡ.from ≈⟨ curry-process (f ξ) ⟩
      adjoint.Ladjunct (f ξ ∘ unitorˡ.from)
        ∎
  }

-- Reindexing of coherent systems, matching MRS-Profunctor on elements.
reindexMR2 : ∀ {A A′ B B′ : Obj} →
  A′ ⇒ A → B ⇒ B′ → MR2 A B → MR2 A′ B′
reindexMR2 u v ξ = record
  { f = v ∘ f ξ ∘ u
  ; Φ = (nHom u ∘ʳ Cod) ∘ᵥ Φ ξ
  }

-- Proposition to inhabit: reindexing sends a closure point b₀ to v ∘ b₀.
ReindexingPreservesClosure : {A A′ B B′ : Obj} (u : A′ ⇒ A) (v : B ⇒ B′) {ξ : MR2 A B} → MetabolicClosure ξ → MetabolicClosure (reindexMR2 u v ξ)
ReindexingPreservesClosure u v {ξ} x = record 
  { b₀ = v ∘ b₀ x 
  ; closureL = let module Φ = NaturalTransformation (Φ ξ)
                   Φvfu = Φ.η (record { arr = v ∘ f ξ ∘ u }) 
               in begin
      ([ u , id ]₁ ∘ Φvfu) ∘ v ∘ b₀ x ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!  !} ⟩
      {!   !} ≈⟨ {!  !} ⟩
      {!   !} ≈⟨ {!  !} ⟩
      adjoint.Ladjunct ((v ∘ f ξ ∘ u) ∘ unitorˡ.from) ∎ 
  }