{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_; Lift; lift; lower)

module Categories.Rosen.Coherent.IdCore {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- id-coherent (M,R)-systems: the notion the paper settles on.
--
-- An (M,R)-system is a pair (f, Φ) where f : A ⇒ B is the metabolic process
-- and Φ : id ⇒ [A,-] is a natural family of repair maps, one component
-- Φ_X : X ⇒ [A,X] for every OBJECT X.
--
-- Contrast Coherent/Core.agda, where Φ : Cod ⇒ [A,-]∘Cod has a component at
-- every ARROW.  The two notions are equivalent --- that is the content of
-- Coherent/CodCoherentEqualIdCoherent.agda, which is the paper's `cod_lax_epi`
-- --- but they are not the same definition, and the proofs below are not the
-- proofs of Core with a whiskering deleted: naturality here is over C, not over
-- Arr(C), so every naturality step is a different step.
--
-- ===========================================================================
-- THE `Lift` BELOW IS AGDA BOOKKEEPING AND HAS NO MATHEMATICAL CONTENT.
--
-- Read this before being puzzled by it, and mentally erase every `lift` and
-- `lower` in this file and downstream: in the human-readable mathematics there
-- is nothing there.  Two (M,R)-systems are equal when their process maps are
-- equal and their repair families are pointwise equal.  Full stop.
--
-- Why it is nevertheless there.  Agda stratifies types by universe LEVEL, and
-- levels do not subsume: a Set at level a is not usable where a Set at level
-- a ⊔ b is expected, even though morally "smaller" is fine.  Now:
--
--   * the CARRIER of this setoid, MR2 A B, sits at o ⊔ ℓ ⊔ e --- the same as
--     the cod-coherent one in Coherent/Core.agda;
--   * the EQUALITY does not.  Cod-coherent Φ ≃ Φ′ quantifies over the objects
--     of Arr(C), a Set (o ⊔ ℓ), so it lands at o ⊔ ℓ ⊔ e.  Id-coherent φ ≃ ψ
--     quantifies over the objects of C only, so it lands at o ⊔ e.
--
-- So the id-coherent equality is genuinely SMALLER --- which is exactly the
-- content of the migration, there is less data --- and that is the problem:
-- the upstream tabulator, Categories.Functor.Profunctor.Tabulator, hard-wires
-- its profunctor to land in Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e), and upstream is
-- outside the perimeter of this development.
--
-- Level.Lift raises the relation back to o ⊔ ℓ ⊔ e by wrapping it in a record
-- with a single field.  Wrapping and unwrapping is `lift` and `lower`.  The
-- pay-off is worth the noise: MRS-Profunctor here then has EXACTLY the type of
-- Core's, so every downstream module migrates as a pure proof-level exercise
-- with no level surprises at all.
--
-- If upstream is ever made level-polymorphic, delete the Lift and the `lift`/
-- `lower` calls that follow it here and in Coherent/TabEquivalence.agda;
-- nothing else changes, and no proof gets harder.
-- ===========================================================================
--
-- Exports: nHom, nHom-identity, MR2, MR2-Setoid, MRS-Profunctor.

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ᵥ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)

open HomReasoning
open MR

-- nHom sends f : A ⇒ B to the induced natural transformation [-,f] : [B,-] ⇒ [A,-].
nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record
  { η = λ X → [ f , id ]₁
  ; commute = λ h → Equiv.sym [ [-,-] ]-commute
  ; sym-commute = λ h → [ [-,-] ]-commute
  }

-- nHom-identity: nHom respects identity.
nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
nHom-identity = [-,-].identity

-- An id-coherent (M,R)-system: the process f together with a natural family
-- Φ_X : X ⇒ [A,X] of repair maps indexed by the objects of C.
record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    Φ : NaturalTransformation idF ([_,-] A)

  Φη = NaturalTransformation.η Φ
  Φcommute = λ {X Y : Obj} (u : X ⇒ Y) → NaturalTransformation.commute Φ {X} {Y} u

-- MR2 as a Setoid: equal f components and pointwise ≃-equal Φ components.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , Φ ⟫) (⟪ g , Φ′ ⟫) → Lift (o ⊔ ℓ ⊔ e) ((f ≈ g) × (Φ ≃ Φ′))
  ; isEquivalence = record
    { refl  = lift (Equiv.refl , (λ {x} → Equiv.refl))
    ; sym   = λ x → let (p , k) = lower x in lift (Equiv.sym p , Equiv.sym k)
    ; trans = λ x y → let (p₁ , h) = lower x
                          (p₂ , k) = lower y
                      in lift (Equiv.trans p₁ p₂ , Equiv.trans h k)
    }
  }

-- MRS-Profunctor reindexes an (M,R)-system along (u : A′ ⇒ A, v : B ⇒ B′):
-- f ↦ v ∘ f ∘ u, and Φ ↦ nHom u ∘ᵥ Φ.  No whiskering with Cod is involved,
-- because Φ is already indexed by the objects of C.
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A′ , B′)} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , Φ ⟫ → ⟪ v ∘ f ∘ u , nHom u ∘ᵥ Φ ⟫ }
    ; cong = λ { {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} x →
        let (f≈g , Φ≈Φ′) = lower x in
        lift ( (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
             , (λ {X} → ∘-resp-≈ʳ (Φ≈Φ′ {X})) )
      }
    }}
  ; identity = λ { {(A , B)} {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} →
      let module Hom = Functor [-,-] in
        ( λ x → let (f≈g , Φ≈Φ′) = lower x in
                lift ( Equiv.trans identityˡʳ f≈g
                     , λ { {X} → Equiv.trans (elimˡ C Hom.identity) (Φ≈Φ′ {X}) }))
     }
  ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} →
       let module Hom[-1] {A} = Functor (appʳ [-,-] A) in
         ( λ w → let (f≈g , Φ≈Φ′) = lower w in
             lift ( (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
                    (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
                    (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
                    (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
                    v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
        , λ { {X} →
            let module Φ  = NaturalTransformation Φ
                module Φ′ = NaturalTransformation Φ′
            in
            begin [ u₁ ∘ u₂ , id ]₁ ∘ Φ.η X              ≈⟨ ∘-resp-≈ Equiv.refl (Φ≈Φ′ {X}) ⟩
                  [ u₁ ∘ u₂ , id ]₁ ∘ Φ′.η X             ≈⟨ Hom[-1].homomorphism ⟩∘⟨refl ⟩
                  ([ u₂ , id ]₁ ∘ [ u₁ , id ]₁) ∘ Φ′.η X ≈⟨ assoc ⟩
                  [ u₂ , id ]₁ ∘ ([ u₁ , id ]₁ ∘ Φ′.η X) ∎ } ))
     }
  ; F-resp-≈ = λ { {(A , B)} {(A′ , B′)} {f = (u , v)} {g = (u′ , v′)} (u≈u′ , v≈v′) {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} →
       let module Hom = Functor [-,-] in
         ( λ w → let (f≈g , Φ≈Φ′) = lower w in
             lift ( ∘-resp-≈ v≈v′ (∘-resp-≈ f≈g u≈u′)
        , λ { {X} →
            let module Φ  = NaturalTransformation Φ
                module Φ′ = NaturalTransformation Φ′
            in ∘-resp-≈ (Hom.F-resp-≈ (u≈u′ , Equiv.refl)) (Φ≈Φ′ {X})
              } ))
     }
  }
