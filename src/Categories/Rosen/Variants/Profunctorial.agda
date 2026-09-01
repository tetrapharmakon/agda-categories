{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Level using (_⊔_;suc)

module Categories.Rosen.Variants.Profunctorial {o ℓ e} {C E : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Categories.Category.CoSlice C
open import Categories.Category.Slice C

-- Profunctorial natural MR systems

open import Data.Product using (Σ;_,_;proj₁;proj₂;_×_)
open import Function.Equality using (Π)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Product using (Product;_⁂_;πʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Hom
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_;F⇒F∘id) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
import Reason
open Reason C

-- The codomain of every profunctor below.  Equality of Setoids-morphisms is the
-- "cong"-shaped relation ∀ {x y} → x ≈ y → f ⟨$⟩ x ≈ g ⟨$⟩ y, which mentions the
-- two objects only inside their own carriers and relations.  So the categorical
-- combinators (Equiv.trans, ∘-resp-≈ˡ, assoc, …) leave their objects as
-- unsolvable metas here, and these three lemmas are proved pointwise instead.
-- Read them as: the twisting isomorphism of MR2-Setoid is reflexive / symmetric
-- / transitive.  Everything is explicit so that call sites infer nothing.
private
  module S = Category (Setoids ℓ e)

  twist-refl : ∀ {P R : Setoid ℓ e} (φ : P S.⇒ R) → φ S.≈ φ S.∘ S.id
  twist-refl φ = Π.cong φ

  twist-sym : ∀ {P Q R : Setoid ℓ e} (φ : P S.⇒ R) (ψ : Q S.⇒ R)
                (τ : P S.⇒ Q) (τ⁻¹ : Q S.⇒ P)
            → τ S.∘ τ⁻¹ S.≈ S.id → φ S.≈ ψ S.∘ τ → ψ S.≈ φ S.∘ τ⁻¹
  twist-sym {P} {Q} {R} φ ψ τ τ⁻¹ inv eq e = Setoid.sym R
    (Setoid.trans R (eq (Setoid.refl P)) (Π.cong ψ (inv (Setoid.sym Q e))))

  twist-trans : ∀ {P Q R T : Setoid ℓ e} (φ : P S.⇒ T) (ψ : Q S.⇒ T) (χ : R S.⇒ T)
                  (τ : P S.⇒ Q) (τ′ : Q S.⇒ R)
              → φ S.≈ ψ S.∘ τ → ψ S.≈ χ S.∘ τ′ → φ S.≈ χ S.∘ (τ′ S.∘ τ)
  twist-trans {Q = Q} {T = T} φ ψ χ τ τ′ eq eq′ e =
    Setoid.trans T (eq e) (eq′ (Setoid.refl Q))

open Closed Cl using (adjoint; unitorˡ;unitorʳ-commute-to; unitorʳ-commute-from;unitorʳ; [-,-]; unit; [_,_]₀; [_,-]; [-,_]; [_,_]₁; _⊗₁_)

conjoint[_,-] : (A : Obj) {B : Obj} → Bifunctor (Category.op (coSlice A)) (Slice B)  (Setoids ℓ e)
conjoint[ A ,-] {B} = (Hom[ C ][-,-] ∘F (Functor.op (Cod A)  ⁂ ([_,-] A ∘F Dom B)))

C/B×A/C : {A B : Obj} → Category (o ⊔ ℓ) (ℓ ⊔ e) (e ⊔ e)
C/B×A/C {A} {B} = Product (Category.op (coSlice A)) (Slice B)

-- definition of a profunctorial (M,R)-system
record MR2 (A B : Obj) : Set (o ⊔ suc ℓ ⊔ suc e) where
  constructor ⟪_,_,_⟫
  field
    f : A ⇒ B
    p : Bifunctor (Category.op (coSlice A)) (Slice B) (Setoids ℓ e)
    Φ : NaturalTransformation p (conjoint[ A ,-] {B})
  Φη = NaturalTransformation.η Φ


open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism;niHelper; _ⓘˡ_; _ⓘʳ_)

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal, their associated profunctors are isomorphic,
-- and their Φ components are ≃-equal.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ suc ℓ ⊔ suc e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , p , Φ ⟫) (⟪ g , q , Φ′ ⟫) →
   (f ≈ g) × (Σ (NaturalIsomorphism p q)
     (λ t → let τ = NI.NaturalIsomorphism.F⇒G t
            in Φ ≃ Φ′ ∘ᵥ τ))
  -- Every twist below has to be spelled out: the goal is an equality in Setoids,
  -- which Agda eta-expands into its pointwise "cong" form, so nothing about the
  -- intermediate morphisms survives to be inferred.
  ; isEquivalence = record
    -- F⇒G NI.refl is the identity, so the twist is just a unitor
    { refl = λ { {⟪ f , p , Φ ⟫} → refl , NI.refl ,
        (λ {X} → twist-refl (NaturalTransformation.η Φ X)) }
    -- F⇒G (NI.sym b) is b's inverse: cancel it against b on the right
    ; sym = λ { {⟪ f , p , Φ ⟫} {⟪ g , q , Ψ ⟫} (a , b , c) → sym a , NI.sym b ,
        (λ {X} → twist-sym (NaturalTransformation.η Φ X)
                           (NaturalTransformation.η Ψ X)
                           (NI.NaturalIsomorphism.⇒.η b X)
                           (NI.NaturalIsomorphism.⇐.η b X)
                           (NI.NaturalIsomorphism.iso.isoʳ b X) c) }
    -- F⇒G (NI.trans b b′) is F⇒G b′ ∘ᵥ F⇒G b: paste and reassociate
    ; trans = λ { {⟪ f , p , Φ ⟫} {⟪ g , q , Ψ ⟫} {⟪ h , r , Θ ⟫}
                  (a , b , c) (a′ , b′ , c′) → trans a a′ , NI.trans b b′ ,
        (λ {X} → twist-trans (NaturalTransformation.η Φ X)
                             (NaturalTransformation.η Ψ X)
                             (NaturalTransformation.η Θ X)
                             (NI.NaturalIsomorphism.⇒.η b  X)
                             (NI.NaturalIsomorphism.⇒.η b′ X)
                             c c′) }
    }
  }

pollo : ∀ {A′ A B B′} {u : A′ ⇒ A} {v : B ⇒ B′} → Functor (Product (Category.op (coSlice A)) (Slice B)) (Product (Category.op (coSlice A′)) (Slice B′))
pollo {u = u} {v = v} = Functor.op (u /C) ⁂ (C/ v)

open HomReasoning
open MR

-- The same proof that works for Cod does NOT work in general.  The obstruction:
--
-- reindexing an MR2 A B along u : A′ ⇒ A and v : B ⇒ B′ has to turn a bifunctor
-- on (coSlice A)ᵒᵖ × Slice B into one on (coSlice A′)ᵒᵖ × Slice B′.  By
-- precomposition that would need a functor
--
--     (coSlice A′)ᵒᵖ × Slice B′  ⟶  (coSlice A)ᵒᵖ × Slice B ,
--
-- i.e. coSlice A′ ⟶ coSlice A together with Slice B′ ⟶ Slice B.  What u and v
-- actually give is exactly the opposite pair: `u /C : coSlice A ⟶ coSlice A′`
-- precomposes with u and `C/ v : Slice B ⟶ Slice B′` postcomposes with v.  That
-- is what `pollo` above assembles, and it points the wrong way for `p ∘F -`.
-- The functors pointing the right way are the pushout along u and the pullback
-- along v, which need C to have pushouts and pullbacks — hypotheses this module
-- does not carry.  (Going the other way, as a left Kan extension of p along
-- `pollo`, is blocked on universe levels: coSlice A has objects in Set (o ⊔ ℓ)
-- while p lands in Setoids ℓ e.)
--
-- Nothing outside p is affected, so below every component that only mentions the
-- underlying process f is proved outright — they are literally the Coherent/Core
-- proofs — and only the components mentioning the reindexed profunctor are
-- postulated as UNSOUND-*.  Those are not parts left undone: they are
-- unavailable without extra hypotheses on C.
-- ┌──────────────────────────────────────────────────────────────────────────┐
-- │ KNOWN-FALSE POSTULATE.  Everything named UNSOUND-* in Categories.Rosen is │
-- │ a statement this development knows to be FALSE.  It is postulated only so │
-- │ that the shape of the obstruction is visible and typed; nothing that      │
-- │ depends on it is verified.  `grep -rn UNSOUND src/Categories/Rosen/`      │
-- │ enumerates the whole debt.                                               │
-- └──────────────────────────────────────────────────────────────────────────┘
--
-- The obstruction, precisely: reindexing along (u : A′ ⇒ A , v : B ⇒ B′) needs
-- coSlice A′ → coSlice A and Slice B′ → Slice B.  The functors `pollo`
-- assembles run the OTHER way; the right-way ones are pushout along u and
-- pullback along v, which this module does not assume.  Adding those two
-- hypotheses is what it would take to discharge the three postulates below.
--
-- NOTE ON THE PAPER.  §4's `proposition_assignment_profunctor_r` asserts that
-- (A,B) ↦ proMRS(A,B) IS a profunctor, with no hypothesis on C and no proof.
-- That proposition is exactly what is unproved here.
postulate
  -- The whole bifunctor, postulated as one named obstruction.
  --
  -- An earlier version built this as a record whose f-components were proved
  -- and whose four Φ-components were `sorry`.  That is worse than useless: the
  -- reindexed system is opaque, so none of the "proved" laws actually
  -- constrain anything, and the record reads as a construction when it is not
  -- one.  The attempted record is preserved verbatim in the comment below.
  UNSOUND-MRS-Profunctor :
    Bifunctor (Category.op C) C (Setoids (o ⊔ suc ℓ ⊔ suc e) (o ⊔ ℓ ⊔ e))

-- THE ATTEMPTED CONSTRUCTION (does not typecheck without the postulates it
-- used to carry; kept as a record of what was tried and of exactly which
-- components are the obstruction).
--
-- MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ suc ℓ ⊔ suc e) (o ⊔ ℓ ⊔ e))
-- MRS-Profunctor = record
--   { F₀ = (λ { (A , B) → MR2-Setoid A B })
--   ; F₁ = λ { {(A , B)} {(A′ , B′)} (u , v) → record
--     { _⟨$⟩_ = λ {⟪ f , p , Φ ⟫ → ⟪ v ∘ f ∘ u , UNSOUND-reindex-p u v p , UNSOUND-reindex-Φ u v p Φ ⟫ }
--     ; cong = λ { {⟪ f , p , Φ ⟫} {⟪ g , q , Φ′ ⟫} (f≈g , _) →
--         (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
--       , UNSOUND-reindex-twist
--       }
--     }}
--   ; identity = λ { (f≈g , _) → Equiv.trans identityˡʳ f≈g , UNSOUND-reindex-twist }
--   ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)}
--                        {⟪ f , p , Φ ⟫} {⟪ g , q , Φ′ ⟫} (f≈g , _) →
--       (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
--              (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
--              (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
--              (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
--              v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
--     , UNSOUND-reindex-twist }
--   ; F-resp-≈ = λ { (u≈u′ , v≈v′) (f≈g , _) →
--       ∘-resp-≈ v≈v′ (∘-resp-≈ f≈g u≈u′) , UNSOUND-reindex-twist }
--   }
