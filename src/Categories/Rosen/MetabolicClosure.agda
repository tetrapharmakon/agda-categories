{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ʳ_)
open import Level using (_⊔_)

module Categories.Rosen.MetabolicClosure
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Categories.Adjoint.Mate using (Mate)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)

open import Categories.Rosen.Coherent.IdCore Cl using (MR2; nHom)

import Reason
open Reason C
open HomReasoning
open Closed Cl using
  (adjoint; mate; unit; unitorˡ; unitorˡ-commute-from
  ; [-,-]; [_,_]₀; [_,_]₁; [_,-]; _⊗₀_; _⊗₁_; -⊗_)
open MR2

-- The component "at the process f" is simply the component at B = cod f.
-- Kept under its old name so that the closure conditions below read unchanged.
Φη₀ : ∀ {A B : Obj} → MR2 A B → B ⇒ [ A , B ]₀
Φη₀ {B = B} ξ = Φη ξ B


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

-- The component of the repair family at an object X.
Φ-id : ∀ {A B : Obj} → MR2 A B → (X : Obj) → X ⇒ [ A , X ]₀
Φ-id ξ X = Φη ξ X

-- In the cod-coherent presentation these two were genuinely different terms ---
-- a component indexed by the arrow f versus one indexed by the object id_B ---
-- and identifying them took an argument (the former `Φ-id≈Φ-g`, an instance of
-- the surplus of cod-naturality over id-naturality).  That argument has not
-- disappeared: it has moved to `Φ-const-on-slices` in
-- Coherent/CodCoherentEqualIdCoherent.agda, where it is what makes the two
-- notions of (M,R)-system agree.  Here, with a single family indexed by
-- objects, the identification is definitional.
Φ-id≈Φ-f : ∀ {A B : Obj} (ξ : MR2 A B) → Φ-id ξ B ≈ Φη₀ ξ
Φ-id≈Φ-f ξ = Equiv.refl

-- Currying commutes with postcomposition.
curry-post : ∀ {A X Y Z : Obj} (g : Y ⇒ Z) (h : X ⊗₀ A ⇒ Y) →
  [ id , g ]₁ ∘ adjoint.Ladjunct h ≈ adjoint.Ladjunct (g ∘ h)
curry-post {A} g h =
  let module HomA = Functor ([_,-] A)
  in begin
    [ id , g ]₁ ∘ adjoint.Ladjunct h               ≈⟨ sym-assoc ⟩
    ([ id , g ]₁ ∘ [ id , h ]₁) ∘ adjoint.unit.η _ ≈˘⟨ HomA.homomorphism ⟩∘⟨refl ⟩
    adjoint.Ladjunct (g ∘ h)                        ∎

-- Currying commutes with postcomposition by the process.
curry-process : ∀ {A B : Obj} (g : A ⇒ B) →
  [ id , g ]₁ ∘ adjoint.Ladjunct unitorˡ.from
    ≈ adjoint.Ladjunct (g ∘ unitorˡ.from)
curry-process g = curry-post g unitorˡ.from

-- Reindexing the exponent: [u,id] postcomposed with a currying is the currying
-- of the reindexed map.  This is exactly the mate condition for [-,-].
curry-reindex : ∀ {A A′ X Y : Obj} (u : A′ ⇒ A) (k : X ⊗₀ A ⇒ Y) →
  [ u , id ]₁ ∘ adjoint.Ladjunct k ≈ adjoint.Ladjunct (k ∘ (id ⊗₁ u))
curry-reindex {A} {A′} u k =
  let module HomA′ = Functor ([_,-] A′)
  in begin
    [ u , id ]₁ ∘ [ id , k ]₁ ∘ adjoint.unit.η _            ≈⟨ sym-assoc ⟩
    ([ u , id ]₁ ∘ [ id , k ]₁) ∘ adjoint.unit.η _          ≈˘⟨ [ [-,-] ]-commute ⟩∘⟨refl ⟩
    ([ id , k ]₁ ∘ [ u , id ]₁) ∘ adjoint.unit.η _          ≈⟨ assoc ⟩
    [ id , k ]₁ ∘ [ u , id ]₁ ∘ adjoint.unit.η _            ≈˘⟨ refl⟩∘⟨ Mate.commute₁ (mate u) ⟩
    [ id , k ]₁ ∘ [ id , id ⊗₁ u ]₁ ∘ adjoint.unit.η _      ≈⟨ sym-assoc ⟩
    ([ id , k ]₁ ∘ [ id , id ⊗₁ u ]₁) ∘ adjoint.unit.η _    ≈˘⟨ HomA′.homomorphism ⟩∘⟨refl ⟩
    adjoint.Ladjunct (k ∘ (id ⊗₁ u))                        ∎

-- A universal closure point is sent to the identity process by the repair
-- component at id_A.  This condition depends only on A and the repair family.
record UnivClosurePoint {A B : Obj} (ξ : MR2 A B) : Set (ℓ ⊔ e) where
  field
    a₀ : unit ⇒ A
    univClosure : Φ-id ξ A ∘ a₀ ≈ adjoint.Ladjunct unitorˡ.from

Univ⇒Metabolic : {A B : Obj} {ξ : MR2 A B} (𝕒 : UnivClosurePoint ξ) → MetabolicClosure ξ
Univ⇒Metabolic {A} {B} {ξ} 𝕒 =
  let module 𝕒 = UnivClosurePoint 𝕒
  in record
  { b₀ = f ξ ∘ 𝕒.a₀
  ; closureL = begin
      Φη₀ ξ ∘ f ξ ∘ 𝕒.a₀                            ≈⟨ ∘-resp-≈ˡ (sym (Φ-id≈Φ-f ξ)) ⟩
      Φ-id ξ B ∘ f ξ ∘ 𝕒.a₀                         ≈⟨ sym-assoc ⟩
      (Φ-id ξ B ∘ f ξ) ∘ 𝕒.a₀                       ≈⟨ Φcommute ξ (f ξ) ⟩∘⟨refl ⟩
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
  ; Φ = nHom u ∘ᵥ Φ ξ
  }

-- Proposition to inhabit: reindexing sends a closure point b₀ to v ∘ b₀.
ReindexingPreservesClosure : {A A′ B B′ : Obj} (u : A′ ⇒ A) (v : B ⇒ B′) {ξ : MR2 A B} → MetabolicClosure ξ → MetabolicClosure (reindexMR2 u v ξ)
ReindexingPreservesClosure {A} {A′} {B} {B′} u v {ξ} x = record
  { b₀ = v ∘ b₀ x
  -- The cod-coherent version of this chain needed an extra step here: the
  -- reindexed system's repair component was indexed by the ARROW v ∘ f ξ ∘ u,
  -- and had to be identified with the component at the identity of its
  -- codomain B′ (that was the step `Φ-id≈Φ-g`).  With id-coherent repair data
  -- the component simply IS the one at B′, so the step disappears --- not
  -- because it was redundant, but because the indexing that made it necessary
  -- is gone.  The argument it carried now lives, once and for all, in
  -- Coherent/CodCoherentEqualIdCoherent.agda.
  ; closureL = let module Φ = NaturalTransformation (Φ ξ)
                   Φvfu = Φ.η B′
                   λ⇒ = unitorˡ.from
               in begin
      ([ u , id ]₁ ∘ Φvfu) ∘ v ∘ b₀ x                    ≈⟨ assoc ⟩
      [ u , id ]₁ ∘ Φ-id ξ B′ ∘ v ∘ b₀ x                 ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      [ u , id ]₁ ∘ (Φ-id ξ B′ ∘ v) ∘ b₀ x               ≈⟨ refl⟩∘⟨ Φcommute ξ v ⟩∘⟨refl ⟩
      [ u , id ]₁ ∘ ([ id , v ]₁ ∘ Φ-id ξ B) ∘ b₀ x      ≈⟨ refl⟩∘⟨ assoc ⟩
      [ u , id ]₁ ∘ [ id , v ]₁ ∘ Φ-id ξ B ∘ b₀ x        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Φ-id≈Φ-f ξ ⟩∘⟨refl ⟩
      [ u , id ]₁ ∘ [ id , v ]₁ ∘ Φη₀ ξ ∘ b₀ x           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ closureL x ⟩
      [ u , id ]₁ ∘ [ id , v ]₁ ∘ adjoint.Ladjunct (f ξ ∘ λ⇒)
                                                         ≈⟨ refl⟩∘⟨ curry-post v (f ξ ∘ λ⇒) ⟩
      [ u , id ]₁ ∘ adjoint.Ladjunct (v ∘ f ξ ∘ λ⇒)      ≈⟨ curry-reindex u (v ∘ f ξ ∘ λ⇒) ⟩
      adjoint.Ladjunct ((v ∘ f ξ ∘ λ⇒) ∘ (id ⊗₁ u))
        ≈⟨ adjoint.Ladjunct-resp-≈
             (assoc ∙ ∘-resp-≈ʳ (assoc ∙ ∘-resp-≈ʳ unitorˡ-commute-from ∙ sym-assoc) ∙ sym-assoc) ⟩
      adjoint.Ladjunct ((v ∘ f ξ ∘ u) ∘ unitorˡ.from) ∎
  }
