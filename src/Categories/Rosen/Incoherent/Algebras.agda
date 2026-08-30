{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.Algebras
  {o ℓ e} {C : Category o ℓ e}
  (M : Monoidal C)
  (Cl : Closed M)
  (BC : BinaryCoproducts C)
  where

open import Categories.Category.Construction.F-Algebras
  using (F-Algebras)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Algebra
  using (F-Algebra; F-Algebra-Morphism)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Fibred Cl
  using (iMR2ᴿ; iMR2ᴿ₀; iMR2ᴿ⇒)

open Category C
open HomReasoning
open MR C
open Monoidal M using (-⊗_; _⊗₁_)
open BinaryCoproducts BC
open Closed Cl using (adjoint; [_,_]₀; [_,_]₁; [_,-])

------------------------------------------------------------------------
-- Incoherent (M,R)-systems as algebras
--
-- Fix an object A.
--
-- 1. The category iMR2ᴿ A is the fibre of (incoherent) (M,R)-systems
--    over A: objects are triples (B , f : A ⇒ B , Φ : B ⇒ [ A , B ])
--    and morphisms are maps v : B ⇒ B′ compatible with both f and Φ.
--
-- 2. We consider the endofunctor X ↦ A + (X ⊗ A).  In settings where ⊗
--    distributes over coproducts, this is (naturally isomorphic to)
--    X ↦ A ⊗ (𝟙 + X).  We work directly with A + (X ⊗ A), so we do not
--    assume any distributivity laws.
--
-- No symmetry of ⊗ is assumed: the transpositions between Φ and Φ#
-- use only the closed structure, and the algebra structure map is
-- [ f , Φ# ] (no braiding involved).
--
-- The main result in this module is an explicit equivalence between
-- iMR2ᴿ A and the category of algebras for X ↦ A + (X ⊗ A).
------------------------------------------------------------------------

-- Endofunctor X ↦ A + (X ⊗ A) on C.
infix 9 _⊗[_+I]
_⊗[_+I] : {A : Obj} → Functor C C
_⊗[_+I] {A} = A +- ∘F -⊗ A

module K {A} = Functor (_⊗[_+I] {A})


-- Category of algebras for X ↦ A + (X ⊗ A).
F-Algebra-Category : {A : Obj} → Category _ _ _
F-Algebra-Category {A} = F-Algebras (_⊗[_+I] {A})


-- Comparison functor iMR2ᴿ A → Alg(A + - ⊗ A).
--
-- On objects (B , f , Φ), we use closedness to transpose
-- Φ : B ⇒ [ A , B ]₀
-- into Φ# : B ⊗ A ⇒ B and define the algebra structure
--
--   α : A + (B ⊗ A) ⇒ B
--   α = [ f , Φ# ]
--
-- No braiding is involved: Φ lives in [ A , B ]₀, so transposing
-- it gives a map out of B ⊗ A directly.

to : {A : Obj} → Functor (iMR2ᴿ A) (F-Algebra-Category {A})
to {A} = record
  { F₀           = λ x →
    let module x = iMR2ᴿ₀ x
        module ξ = iMR2 x.ξ
        Φ#       = adjoint.Radjunct ξ.Φ
    in record
      { A = x.B
      ; α = [ ξ.f , Φ# ]
      }
  ; F₁           = λ f →
    let module f = iMR2ᴿ⇒ f
        ΦX#       = adjoint.Radjunct f.ξX.Φ
        ΦY#       = adjoint.Radjunct f.ξY.Φ
        idA       = id {A = A}
        module ⊗A = Functor (-⊗ A)

        yoga : f.v ∘ ΦX# ≈ ΦY# ∘ (f.v ⊗₁ idA)
        yoga = begin
          f.v ∘ ΦX# ≈⟨ Equiv.sym (adjoint.Radjunct-comm′
            {f = f.ξX.Φ} {g = f.v}) ⟩
          adjoint.Radjunct ([ id , f.v ]₁ ∘ f.ξX.Φ)
            ≈⟨ adjoint.Radjunct-resp-≈ f.eqΦ ⟩
          adjoint.Radjunct (f.ξY.Φ ∘ f.v)
            ≈⟨ refl⟩∘⟨ ⊗A.homomorphism ○ sym-assoc ⟩
          ΦY# ∘ (f.v ⊗₁ idA) ∎
    in record
      { f = f.v
      ; commutes =
          let F₁v = idA +₁ (f.v ⊗₁ idA)
          in begin
               f.v ∘ [ f.ξX.f , ΦX# ]        ≈⟨ ∘-distribˡ-[] ⟩
               [ f.v ∘ f.ξX.f , f.v ∘ ΦX# ] ≈⟨ +-unique
                 (assoc ○ refl⟩∘⟨ +₁∘i₁ ○ refl⟩∘⟨ identityʳ ○
                  inject₁ ○ (Equiv.sym f.eqf))
                 (assoc ○ refl⟩∘⟨ +₁∘i₂ ○ sym-assoc ○
                  inject₂ ⟩∘⟨refl ○ assoc ○ sym-assoc ○
                  Equiv.sym yoga) ⟩
               [ f.ξY.f , ΦY# ] ∘ F₁v        ∎
      }
  ; identity       = Equiv.refl
  ; homomorphism   = Equiv.refl
  ; F-resp-≈       = λ eq → eq
  }

-- Converse functor Alg(A + - ⊗ A) → iMR2ᴿ A.
--
-- Given an algebra α : A + (B ⊗ A) ⇒ B, define
--
--   f = α ∘ i₁
--   Φ = Ladjunct (α ∘ i₂)
--
-- i.e. transpose α ∘ i₂ : B ⊗ A ⇒ B through the closed structure.

from : {A : Obj} → Functor (F-Algebra-Category {A}) (iMR2ᴿ A)
from {A} = record
  { F₀           = λ x →
    let module x = F-Algebra x
        α         = x.α
    in record
      { B = x.A
      ; ξ = ⟪ α ∘ i₁ , adjoint.Ladjunct (α ∘ i₂) ⟫
      }
  ; F₁           = λ {X} {Y} f →
    let module x = F-Algebra X
        module y = F-Algebra Y
        module f = F-Algebra-Morphism
        f′        = f .F-Algebra-Morphism.f
        αx        = x.α
        αy        = y.α
        idA       = id {A = A}
        hx        = αx ∘ i₂
        hy        = αy ∘ i₂
    in record
      { v   = f′
      ; eqf = pullˡ (f.commutes f) ○ assoc ○
              ∘-resp-≈ʳ (Equiv.trans inject₁ identityʳ)
      ; eqΦ =
          let module HomA = Functor ([ A ,-])
              tensorEq : f′ ∘ hx ≈ hy ∘ (f′ ⊗₁ idA)
              tensorEq = begin
                f′ ∘ hx ≈⟨ sym-assoc ○ (f.commutes f) ⟩∘⟨refl ⟩
                (αy ∘ Functor.F₁ _⊗[_+I] f′) ∘ i₂ ≈⟨ pullʳ +₁∘i₂ ⟩
                αy ∘ (i₂ ∘ (f′ ⊗₁ idA)) ≈⟨ sym-assoc ⟩
                hy ∘ f′ ⊗₁ idA ∎
              η = adjoint.unit.η
          in begin
            [ id , f′ ]₁ ∘ HomA.F₁ hx ∘ η _
              ≈⟨ pullˡ (Equiv.sym HomA.homomorphism) ⟩
            HomA.F₁ (f′ ∘ hx) ∘ η _
              ≈⟨ HomA.F-resp-≈ tensorEq ⟩∘⟨refl ⟩
            HomA.F₁ (hy ∘ (f′ ⊗₁ idA)) ∘ η _
              ≈⟨ adjoint.Ladjunct-comm′ {f = f′} {g = hy} ⟩
            _ ∎
      }
  ; identity       = Equiv.refl
  ; homomorphism   = Equiv.refl
  ; F-resp-≈       = λ z → z
  }

------------------------------------------------------------------------
-- Equivalence
--
-- The functors `to` and `from` are inverse up to natural isomorphism.
--
-- The proofs are constructive.
-- On the algebra side, the key steps are `RLadjunct≈id` (the zig of the
-- closed adjunction) and the coproduct η-law `+-g-η`.
-- On the iMR2ᴿ side, the key steps are `inject₂` for the coproduct and
-- `LRadjunct≈id`.
-- No braiding or symmetry of the monoidal structure is used.
------------------------------------------------------------------------

private
  module F∘G {A : Obj} {X : F-Algebra (_⊗[_+I] {A})} where
    module X = F-Algebra X
    α   = X.α
    h   = α ∘ i₂
    hₐ  = adjoint.Radjunct (adjoint.Ladjunct h)

    h≈ : hₐ ≈ α ∘ i₂
    h≈ = begin
      hₐ     ≈⟨ adjoint.RLadjunct≈id ⟩
      α ∘ i₂ ∎

    αFG≈α : [ α ∘ i₁ , hₐ ] ≈ α
    αFG≈α = Equiv.trans ([]-cong₂ Equiv.refl h≈) (+-g-η {f = α})

    commutes₊ : id ∘ [ α ∘ i₁ , hₐ ] ≈
                α ∘ Functor.F₁ (_⊗[_+I] {A = A}) id
    commutes₊ = begin
      id ∘ [ α ∘ i₁ , hₐ ] ≈⟨ identityˡ ⟩
      [ α ∘ i₁ , hₐ ]      ≈⟨ αFG≈α ⟩
      α                    ≈˘⟨ identityʳ ⟩
      α ∘ id               ≈⟨ ∘-resp-≈ʳ
        (Equiv.sym (Functor.identity (_⊗[_+I] {A = A}))) ⟩
      α ∘ Functor.F₁ (_⊗[_+I] {A = A}) id ∎

    commutes₋ : id ∘ α ≈
                [ α ∘ i₁ , hₐ ] ∘ Functor.F₁ (_⊗[_+I] {A = A}) id
    commutes₋ = begin
      id ∘ α               ≈⟨ identityˡ ⟩
      α                    ≈˘⟨ αFG≈α ⟩
      [ α ∘ i₁ , hₐ ]      ≈˘⟨ identityʳ ⟩
      [ α ∘ i₁ , hₐ ] ∘ id ≈⟨ ∘-resp-≈ʳ
        (Equiv.sym (Functor.identity (_⊗[_+I] {A = A}))) ⟩
      [ α ∘ i₁ , hₐ ] ∘ Functor.F₁ (_⊗[_+I] {A = A}) id ∎

  module G∘F {A : Obj} {X : iMR2ᴿ₀ A} where
    module X = iMR2ᴿ₀ X
    module ξ = iMR2 X.ξ

    Φ′ : X.B ⇒ [ A , X.B ]₀
    Φ′  = adjoint.Ladjunct ([ ξ.f , adjoint.Radjunct ξ.Φ ] ∘ i₂)

    Φ′≈Φ : Φ′ ≈ ξ.Φ
    Φ′≈Φ = Equiv.trans (adjoint.Ladjunct-resp-≈ inject₂)
                       adjoint.LRadjunct≈id

    eqΦ₊ : [ id , id ]₁ ∘ Φ′ ≈ ξ.Φ ∘ id
    eqΦ₊ = begin
      [ id , id ]₁ ∘ Φ′ ≈⟨ ∘-resp-≈ˡ (Functor.identity ([ A ,-])) ⟩
      id ∘ Φ′           ≈⟨ identityˡ ⟩
      Φ′                ≈⟨ Φ′≈Φ ⟩
      ξ.Φ               ≈˘⟨ identityʳ ⟩
      ξ.Φ ∘ id          ∎

    eqΦ₋ : [ id , id ]₁ ∘ ξ.Φ ≈ Φ′ ∘ id
    eqΦ₋ = begin
      [ id , id ]₁ ∘ ξ.Φ ≈⟨ ∘-resp-≈ˡ (Functor.identity ([ A ,-])) ⟩
      id ∘ ξ.Φ           ≈⟨ identityˡ ⟩
      ξ.Φ                ≈˘⟨ Φ′≈Φ ⟩
      Φ′                 ≈˘⟨ identityʳ ⟩
      Φ′ ∘ id            ∎


AlgA≣MRS^A : {A : Obj} →
             StrongEquivalence (iMR2ᴿ A) (F-Algebra-Category {A})
AlgA≣MRS^A {A} = record
  { F           = to {A}
  ; G           = from {A}
  ; weak-inverse = record
    { F∘G≈id = niHelper (record
      { η       = λ X → record
        { f        = id
        ; commutes = F∘G.commutes₊ {X = X}
        }
      ; η⁻¹     = λ X → record
        { f        = id
        ; commutes = F∘G.commutes₋ {X = X}
        }
      ; commute = λ f → Equiv.trans identityˡ (Equiv.sym identityʳ)
      ; iso     = λ X → record
        { isoˡ = identityˡ
        ; isoʳ = identity²
        }
      })
    ; G∘F≈id = niHelper (record
      { η       = λ X → record
        { v   = id
        ; eqf = identityˡ ○ inject₁
        ; eqΦ = G∘F.eqΦ₊ {X = X}
        }
      ; η⁻¹     = λ X → record
        { v   = id
        ; eqf = Equiv.trans identityˡ (Equiv.sym inject₁)
        ; eqΦ = G∘F.eqΦ₋ {X = X}
        }
      ; commute = λ f → Equiv.trans identityˡ (Equiv.sym identityʳ)
      ; iso     = λ X → record
        { isoˡ = identityˡ
        ; isoʳ = identityˡ
        }
      })
    }
  }
