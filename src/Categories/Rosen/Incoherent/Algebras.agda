{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Rosen.Incoherent.Algebras
  {o ℓ e} {C : Category o ℓ e}
  (M : Monoidal C)
  (Cl : Closed M)
  (S : Symmetric M)
  (BC : BinaryCoproducts C)
  where

----------------------------------------------------------------------
-- Incoherent (M,R)-Systems as Algebras
--
-- Fix an object A.
--
-- 1. The category iMR2ᴿ A is the fibre of (incoherent) (M,R)-systems over A:
--    objects are triples (B , f : A ⇒ B , Φ : B ⇒ [ A , B ]) and morphisms are
--    maps v : B ⇒ B' compatible with both f and Φ.
--
-- 2. We consider the endofunctor X ↦ A + (A ⊗ X).  In settings where ⊗
--    distributes over coproducts, this is (naturally isomorphic to)
--    X ↦ A ⊗ (𝟙 + X).  We work directly with A + (A ⊗ X), so we do not assume
--    any distributivity laws.
--
-- The main result in this module is an explicit equivalence between iMR2ᴿ A
-- and the category of algebras for X ↦ A + (A ⊗ X).
----------------------------------------------------------------------

open Category C

open import Data.Product using (_,_)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Fibred Cl using (iMR2ᴿ; iMR2ᴿ₀; iMR2ᴿ⇒)

open HomReasoning
open MR C
open Monoidal M using (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_)
open BinaryCoproducts BC
open Symmetric S hiding (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_) renaming (braided-iso to β)
open Closed Cl using (adjoint; [_,_]₀; [_,_]₁; [_,-])

-- Endofunctor X ↦ A + (A ⊗ X) on C.
_⊗[I+_] : {A : Obj} → Functor C C
_⊗[I+_] {A} = A +- ∘F A ⊗-

-- Category of algebras for X ↦ A + (A ⊗ X).
F-Algebra-Category : {A : Obj} → Category _ _ _
F-Algebra-Category {A} = F-Algebras (_⊗[I+_] {A})


-- Comparison functor iMR2ᴿ A → Alg(A + A ⊗ -).
--
-- On objects (B , f , Φ), we use closedness to transpose
-- Φ : B ⇒ [ A , B ]₀
-- into Φ# : A ⊗ B ⇒ B and define the algebra structure
--
--   α : A + (A ⊗ B) ⇒ B
--   α = [ f , Φ# ∘ β.from ]
--
-- where β.from : A ⊗ B ⇒ B ⊗ A is the braiding.
to : {A : Obj} → Functor (iMR2ᴿ A) (F-Algebra-Category {A})
to {A} = record
  { F₀ = λ x →
    let module x = iMR2ᴿ₀ x
        module ξ = iMR2 x.ξ
        Φ# = adjoint.Radjunct ξ.Φ
    in record
      { A = x.B
      ; α = [ ξ.f , Φ# ∘ β.from ]
      }
  ; F₁ = λ f →
    let module f = iMR2ᴿ⇒ f
        ΦX# = adjoint.Radjunct f.ξX.Φ
        ΦY# = adjoint.Radjunct f.ξY.Φ
        idA = id {A = A}
        module ⊗A = Functor (-⊗ A)
        yoga : f.v ∘ ΦX# ∘ β.from ≈ ΦY# ∘ β.from ∘ (idA ⊗₁ f.v)
        yoga = begin
            f.v ∘ ΦX# ∘ β.from                                 ≈⟨ sym-assoc ○ (Equiv.sym (adjoint.Radjunct-comm′ {f = f.ξX.Φ} {g = f.v})) ⟩∘⟨refl ⟩
            adjoint.Radjunct ([ id , f.v ]₁ ∘ f.ξX.Φ) ∘ β.from ≈⟨ adjoint.Radjunct-resp-≈ f.eqΦ ⟩∘⟨refl ⟩
            adjoint.Radjunct (f.ξY.Φ ∘ f.v) ∘ β.from           ≈⟨ (refl⟩∘⟨ ⊗A.homomorphism ○ sym-assoc) ⟩∘⟨refl ○ assoc ⟩
            ΦY# ∘ (f.v ⊗₁ idA) ∘ β.from                        ≈⟨ refl⟩∘⟨ braiding.⇒.sym-commute {X = (A , f.X.B)} {Y = (A , f.Y.B)} (idA , f.v) ⟩
            ΦY# ∘ β.from ∘ (idA ⊗₁ f.v)                        ∎
      in record
      { f = f.v
      ; commutes =
          let F₁v = idA +₁ (idA ⊗₁ f.v)
          in begin
            f.v ∘ [ f.ξX.f , ΦX# ∘ β.from ]         ≈⟨ ∘-distribˡ-[] ⟩
            [ f.v ∘ f.ξX.f , f.v ∘ (ΦX# ∘ β.from) ] ≈⟨ +-unique (assoc ○ refl⟩∘⟨ +₁∘i₁ ○ refl⟩∘⟨ identityʳ ○ inject₁ ○ (Equiv.sym f.eqf))
                                                                (assoc ○ refl⟩∘⟨ +₁∘i₂ ○ sym-assoc ○ inject₂ ⟩∘⟨refl ○ assoc ○ Equiv.sym yoga) ⟩
            [ f.ξY.f , ΦY# ∘ β.from ] ∘ F₁v         ∎
      }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ eq → eq
  }
  
-- Converse functor Alg(A + A ⊗ -) → iMR2ᴿ A.
--
-- Given an algebra α : A + (A ⊗ B) ⇒ B, define
--
--   f = α ∘ i₁
--   Φ = Ladjunct (α ∘ i₂ ∘ β.from)
--
-- i.e. transpose the composite B ⊗ A --β.from→ A ⊗ B --α∘i₂→ B.
from : {A : Obj} → Functor (F-Algebra-Category {A}) (iMR2ᴿ A) 
from {A} = record
  { F₀ = λ x →
    let module x = F-Algebra x
        α = x.α
    in record
      { B = x.A
      ; ξ = ⟪ α ∘ i₁ , adjoint.Ladjunct (α ∘ i₂ ∘ β.from) ⟫
      }
  ; F₁ = λ {X} {Y} f →
    let module x = F-Algebra X
        module y = F-Algebra Y
        module f = F-Algebra-Morphism
        f' = f .F-Algebra-Morphism.f
        αx = x.α
        αy = y.α
        idA = id {A = A}
        hx = αx ∘ i₂ ∘ β.from
        hy = αy ∘ i₂ ∘ β.from
    in record
      { v = f'
      ; eqf = pullˡ (f.commutes f) ○ assoc ○ ∘-resp-≈ʳ (Equiv.trans inject₁ identityʳ) 
      ; eqΦ =
          let module HomA = Functor ([ A ,-])
              F₁f = idA +₁ (idA ⊗₁ f')
              tensorEq : f' ∘ hx ≈ hy ∘ (f' ⊗₁ idA)
              tensorEq = begin
                f' ∘ hx                            ≈⟨ sym-assoc ○ (f.commutes f) ⟩∘⟨refl ⟩
                (αy ∘ F₁f) ∘ i₂ ∘ β.from           ≈⟨ sym-assoc ○ assoc ⟩∘⟨refl ⟩
                (αy ∘ (F₁f ∘ i₂)) ∘ β.from         ≈⟨ assoc ○ refl⟩∘⟨ +₁∘i₂ ⟩∘⟨refl ⟩
                αy ∘ (i₂ ∘ (idA ⊗₁ f')) ∘ β.from   ≈⟨ sym-assoc ○ (Equiv.sym assoc) ⟩∘⟨refl ○ assoc ⟩
                (αy ∘ i₂) ∘ (idA ⊗₁ f') ∘ β.from   ≈⟨ refl⟩∘⟨ braiding.⇒.sym-commute {X = (x.A , A)} {Y = (y.A , A)} (f' , idA) ○ assoc ○ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
                (αy ∘ (i₂ ∘ β.from)) ∘ (f' ⊗₁ idA) ∎
          in begin
            [ id , f' ]₁ ∘ adjoint.Ladjunct hx             ≈⟨ sym-assoc ⟩
            ([ id , f' ]₁ ∘ HomA.F₁ hx) ∘ adjoint.unit.η _ ≈⟨ (Equiv.sym HomA.homomorphism) ⟩∘⟨refl ⟩
            HomA.F₁ (f' ∘ hx) ∘ adjoint.unit.η _           ≈⟨ (HomA.F-resp-≈ tensorEq) ⟩∘⟨refl ⟩
            HomA.F₁ (hy ∘ (f' ⊗₁ idA)) ∘ adjoint.unit.η _  ≈⟨ adjoint.Ladjunct-comm′ {f = f'} {g = hy} ⟩
            adjoint.Ladjunct hy ∘ f' ∎
      }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ z → z
  }

------------------------------------------------------------------------
-- Equivalence
--
-- The functors `to` and `from` are inverse up to natural isomorphism.
--
-- The proofs are constructive.
-- On the algebra side, the key steps are `RLadjunct≈id` and cancellation of
-- the two braids (symmetry of the monoidal structure).
-- On the iMR2ᴿ side, the key steps are `inject₂` for the coproduct and
-- `LRadjunct≈id`.
------------------------------------------------------------------------

AlgA≣MRS^A : {A : Obj} → StrongEquivalence (iMR2ᴿ A) (F-Algebra-Category {A})
AlgA≣MRS^A {A} = record 
  { F = to {A} 
  ; G = from {A}
  ; weak-inverse = record 
    { F∘G≈id = niHelper (record 
      { η = λ X → record 
         { f = id 
         ; commutes =
             let module X = F-Algebra X
                 α = X.α
                 B = X.A
                 βAB = β.from {X = A} {Y = B}
                 βBA = β.from {X = B} {Y = A}
                 h = α ∘ i₂ ∘ βBA
                 hₐ = adjoint.Radjunct (adjoint.Ladjunct h)

                 h≈ : hₐ ∘ βAB ≈ α ∘ i₂
                 h≈ = begin hₐ ∘ βAB               ≈⟨ ∘-resp-≈ˡ adjoint.RLadjunct≈id ○ assoc ○ refl⟩∘⟨ assoc ⟩
                            α ∘ (i₂ ∘ (βBA ∘ βAB)) ≈⟨ refl⟩∘⟨ ∘-resp-≈ʳ (commutative {X = B} {Y = A}) ⟩
                            α ∘ (i₂ ∘ id)          ≈⟨ refl⟩∘⟨ identityʳ ⟩
                            α ∘ i₂                 ∎

                 αFG≈α : [ α ∘ i₁ , hₐ ∘ βAB ] ≈ α
                 αFG≈α = Equiv.trans ([]-cong₂ Equiv.refl h≈) (+-g-η {f = α})
             in begin id ∘ [ α ∘ i₁ , hₐ ∘ βAB ]          ≈⟨ identityˡ ⟩
                      [ α ∘ i₁ , hₐ ∘ βAB ]               ≈⟨ αFG≈α ⟩
                      α                                   ≈˘⟨ identityʳ ⟩
                      α ∘ id                              ≈⟨ ∘-resp-≈ʳ (Equiv.sym (Functor.identity (_⊗[I+_] {A = A}))) ⟩
                      α ∘ Functor.F₁ (_⊗[I+_] {A = A}) id ∎
         } 
      ; η⁻¹ = λ X → record 
         { f = id 
         ; commutes =
             let module X = F-Algebra X
                 α = X.α
                 B = X.A
                 βAB = β.from {X = A} {Y = B}
                 βBA = β.from {X = B} {Y = A}
                 h = α ∘ i₂ ∘ βBA
                 hₐ = adjoint.Radjunct (adjoint.Ladjunct h)

                 h≈ : hₐ ∘ βAB ≈ α ∘ i₂
                 h≈ = begin hₐ ∘ βAB               ≈⟨ ∘-resp-≈ˡ adjoint.RLadjunct≈id ○ assoc ○ refl⟩∘⟨ assoc ⟩
                            α ∘ (i₂ ∘ (βBA ∘ βAB)) ≈⟨ refl⟩∘⟨ ∘-resp-≈ʳ (commutative {X = B} {Y = A}) ⟩
                            α ∘ (i₂ ∘ id)          ≈⟨ refl⟩∘⟨ identityʳ ⟩
                            α ∘ i₂                 ∎

                 αFG≈α : [ α ∘ i₁ , hₐ ∘ βAB ] ≈ α
                 αFG≈α = Equiv.trans ([]-cong₂ Equiv.refl h≈) (+-g-η {f = α})
             in begin id ∘ α                                                  ≈⟨ identityˡ ⟩
                      α                                                       ≈˘⟨ αFG≈α ⟩
                      [ α ∘ i₁ , hₐ ∘ βAB ]                                   ≈˘⟨ identityʳ ⟩
                      [ α ∘ i₁ , hₐ ∘ βAB ] ∘ id                              ≈⟨ ∘-resp-≈ʳ (Equiv.sym (Functor.identity (_⊗[I+_] {A = A}))) ⟩
                      [ α ∘ i₁ , hₐ ∘ βAB ] ∘ Functor.F₁ (_⊗[I+_] {A = A}) id ∎
         } 
      ; commute = λ f → Equiv.trans identityˡ (Equiv.sym identityʳ) 
      ; iso = λ X → record 
        { isoˡ = identityˡ 
        ; isoʳ = identityˡ 
        } 
      }) 
    ; G∘F≈id = niHelper (record 
      { η = λ X → record 
         { v = id 
         ; eqf = identityˡ ○ inject₁ 
         ; eqΦ =
             let module X = iMR2ᴿ₀ X
                 module ξ = iMR2 X.ξ
                 B = X.B
                 βAB = β.from {X = A} {Y = B}
                 βBA = β.from {X = B} {Y = A}
                 Φ# = adjoint.Radjunct ξ.Φ
                 α = [ ξ.f , Φ# ∘ βAB ]

                 Φ′ : B ⇒ [ A , B ]₀
                 Φ′ = adjoint.Ladjunct (α ∘ i₂ ∘ βBA)

                 Φ′≈Φ : Φ′ ≈ ξ.Φ
                 Φ′≈Φ =
                   let step₁ : α ∘ i₂ ∘ βBA ≈ Φ#
                       step₁ = begin
                         α ∘ i₂ ∘ βBA     ≈⟨ sym-assoc ⟩
                         (α ∘ i₂) ∘ βBA   ≈⟨ ∘-resp-≈ˡ inject₂ ⟩
                         (Φ# ∘ βAB) ∘ βBA ≈⟨ assoc ⟩
                         Φ# ∘ (βAB ∘ βBA) ≈⟨ ∘-resp-≈ʳ (commutative {X = A} {Y = B}) ⟩
                         Φ# ∘ id          ≈⟨ identityʳ ⟩
                         Φ#               ∎
                   in Equiv.trans (adjoint.Ladjunct-resp-≈ step₁) adjoint.LRadjunct≈id
             in begin [ id , id ]₁ ∘ Φ′ ≈⟨ ∘-resp-≈ˡ (Functor.identity ([ A ,-])) ⟩
                      id ∘ Φ′           ≈⟨ identityˡ ⟩
                      Φ′                ≈⟨ Φ′≈Φ ⟩
                      ξ.Φ               ≈˘⟨ identityʳ ⟩
                      ξ.Φ ∘ id          ∎
         } 
      ; η⁻¹ = λ X → record 
         { v = id 
         ; eqf = Equiv.trans identityˡ (Equiv.sym inject₁) 
         ; eqΦ =
             let module X = iMR2ᴿ₀ X
                 module ξ = iMR2 X.ξ
                 B = X.B
                 βAB = β.from {X = A} {Y = B}
                 βBA = β.from {X = B} {Y = A}
                 Φ# = adjoint.Radjunct ξ.Φ
                 α = [ ξ.f , Φ# ∘ βAB ]

                 Φ′ : B ⇒ [ A , B ]₀
                 Φ′ = adjoint.Ladjunct (α ∘ i₂ ∘ βBA)

                 Φ′≈Φ : Φ′ ≈ ξ.Φ
                 Φ′≈Φ =
                   let step₁ : α ∘ i₂ ∘ βBA ≈ Φ#
                       step₁ = begin
                         α ∘ i₂ ∘ βBA     ≈⟨ sym-assoc ⟩
                         (α ∘ i₂) ∘ βBA   ≈⟨ ∘-resp-≈ˡ inject₂ ⟩
                         (Φ# ∘ βAB) ∘ βBA ≈⟨ assoc ⟩
                         Φ# ∘ (βAB ∘ βBA) ≈⟨ ∘-resp-≈ʳ (commutative {X = A} {Y = B}) ⟩
                         Φ# ∘ id          ≈⟨ identityʳ ⟩
                         Φ#               ∎
                   in Equiv.trans (adjoint.Ladjunct-resp-≈ step₁) adjoint.LRadjunct≈id
             in begin
               [ id , id ]₁ ∘ ξ.Φ  ≈⟨ ∘-resp-≈ˡ (Functor.identity ([ A ,-])) ⟩
               id ∘ ξ.Φ            ≈⟨ identityˡ ⟩
               ξ.Φ                 ≈˘⟨ Φ′≈Φ ⟩
               Φ′                  ≈˘⟨ identityʳ ⟩
               Φ′ ∘ id             ∎
         } 
      ; commute = λ f → Equiv.trans identityˡ (Equiv.sym identityʳ)
      ; iso = λ X → record 
        { isoˡ = identityˡ 
        ; isoʳ = identityˡ 
        } 
      }) 
    } 
  }
