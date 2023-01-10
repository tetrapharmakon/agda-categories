{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions.Pippo {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

module C = Category C
module M = Monad M

open import Categories.Adjoint using (Adjoint)
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning
open import Categories.NaturalTransformation hiding (id)
open NaturalTransformation using (η)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper; sym; associator)

open import Categories.Adjoint.Construction.Adjunctions M

open import Categories.Object.Terminal (Split M)
open import Categories.Object.Initial (Split M)
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli M as KL
open import Categories.Adjoint.Construction.EilenbergMoore M as EM


open import Categories.Adjoint.Construction.Adjunctions.Properties M 

Kl-initial : IsInitial Kl-object
Kl-initial = record
  { ! = !
  ; !-unique = λ { {A} H → niHelper (
    let module A = SplitObj A
        module K = SplitObj Kl-object
        module H = Split⇒ H
        module Γ = NaturalIsomorphism H.Γ
        module CH = C.HomReasoning
        open Category A.D in
    record
      { η   = Γ.⇐.η
      ; η⁻¹ = Γ.⇒.η
      ; commute = λ f → let open A.D.HomReasoning in 
          begin _ ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ A.F.F-resp-≈ ((H.μ-comp   CH.⟩∘⟨refl) CH.○ (C.assoc CH.○ (CH.refl⟩∘⟨ C.assoc))))) ⟩ 
                _ ≈⟨ ((refl⟩∘⟨ refl⟩∘⟨ A.F.homomorphism)) ⟩
                _ ≈⟨ (refl⟩∘⟨ pullˡ A.D (A.adj.counit.commute _)) ⟩
                _ ≈⟨ (refl⟩∘⟨ assoc) ⟩
                _ ≈⟨ cancelˡ A.D (Γ.iso.isoˡ _) ⟩
                _ ≈⟨ (refl⟩∘⟨ A.F.homomorphism) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ pushˡ A.D A.F.homomorphism) ⟩ 
                _ ≈⟨ extendʳ A.D (A.adj.counit.commute _) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ pushˡ A.D A.F.homomorphism) ⟩ -- (refl⟩∘⟨ (refl⟩∘⟨ A.F.homomorphism)) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ extendʳ A.D (A.adj.counit.commute _)) ⟩ -- (extendʳ A.D (A.adj.counit.commute _)) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ pullˡ A.D A.adj.zig) ⟩ -- (refl⟩∘⟨ refl⟩∘⟨ elimˡ A.D A.adj.zig) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ (identityˡ ○ A.F.F-resp-≈ (elimˡ C M.F.identity))) ⟩ -- (refl⟩∘⟨ refl⟩∘⟨ A.F.F-resp-≈ {! (elimˡ C M.F.identity) !}) ⟩ 
                _ ≈⟨ (refl⟩∘⟨ Γ.⇐.commute f) ⟩ 
                _ ≈⟨ pullˡ A.D (Equiv.sym H.H.homomorphism) ⟩ 
                _ ≈⟨ (H.H.F-resp-≈ (elimʳ C (M.F.F-resp-≈ M.F.identity CH.○ M.F.identity) CH.⟩∘⟨refl) ⟩∘⟨refl) ⟩ 
                _ ≈⟨ (H.H.F-resp-≈ (pullˡ C M.identityʳ CH.○ C.identityˡ) ⟩∘⟨refl) ⟩ 
                _ ∎
      ; iso = NaturalIsomorphism.iso (sym H.Γ)
      })
    }
  }
