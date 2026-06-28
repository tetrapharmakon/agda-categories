{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.NaturalTransformation using (NaturalTransformation;_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,_])
module Categories.Rosen.TotalCategory {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

import Categories.Morphism.Reasoning as MR
open HomReasoning 
open MR

open import Categories.Rosen.Core Cl
open import Categories.Functor.Profunctor.Tabulator

{-
The category of elements of the presheaf

Cᵒᵖ → Set

sending A to Nat( Cod , [ A , Cod ] )

a typical object of such a category is a pair (A, ϕ) and arrows are

u : A ⇒ A' such that 

[u,1] ∘ ψ ≈ ϕ where

[u,1] ∘ ψ : c ⇒ [A',c] ⇒ [A,c]
-}

record tot⇒ (x y : tab₀ MRS-Profunctor) : Set (o ⊔ ℓ ⊔ e) where
  constructor [_,_∥_,_]
  module x = tab₀ x
  module y = tab₀ y
  field
    l : x.L ⇒ y.L 
    r : x.R ⇒ y.R 
  
  f = MR2.f x.ξ
  g = MR2.f y.ξ

  module ϕ = NaturalTransformation (MR2.ϕ x.ξ)
  module ψ = NaturalTransformation (MR2.ϕ y.ξ)
  module l*ψ = NaturalTransformation ((nHom l ∘ʳ Cod) ∘ᵥ MR2.ϕ y.ξ)
  
  field
    eqf : r ∘ f ≈ g ∘ l
    -- TODO: this condition supersedes eqϕ, which is just `nat {id}`; 
    -- ϕ.η t ∘ r ≈ [ A , r ] ∘ ϕ.η t
    -- is the naturality square of ϕ
    nat : ∀ {s t} (α : Arr.Morphism⇒ s t)
        → l*ψ.η t ∘ Arr.Morphism⇒.cod⇒ α
        ≈ Functor.F₁ [ x.L ,-] (Arr.Morphism⇒.cod⇒ α) ∘ ϕ.η s
    -- it's not a one-shot ojb because it requires to change the def of the `total` category
  
  eqϕ : ∀ {t} → l*ψ.η t ≈ ϕ.η t
  eqϕ {t} =
    Equiv.sym identityʳ
    ○ nat (Category.id Arr.Arrow {A = t})
    ○ elimˡ C [-,-].identity


total : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
total = record
  { Obj = tab₀ MRS-Profunctor
  ; _⇒_ = λ s t → tot⇒ s t
  ; _≈_ = λ h k → tot⇒.l h ≈ tot⇒.l k × tot⇒.r h ≈ tot⇒.r k
  ; id = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} → 
       let module ϕNT = NaturalTransformation ϕ
           module l*ϕ = NaturalTransformation ((nHom id ∘ʳ Cod) ∘ᵥ ϕ)
       in
       [ id , id
       ∥ id-comm-sym C
       , (λ {s} {t} α → 
         elimˡ C [-,-].identity ⟩∘⟨refl 
         ○ ϕNT.commute α)
       ]}
  ; _∘_ = λ { {A} {B} {X} t t' →
       let module t  = tot⇒ t
           module t' = tot⇒ t'
           module ψ  = NaturalTransformation (MR2.ϕ t.y.ξ)
           module Hom[-1] {X} = Functor (appʳ [-,-] X)
           module Hx = Functor [ t'.x.L ,-]
           module Hy = Functor [ t.x.L ,-]
       in
       [ t.l ∘ t'.l , t.r ∘ t'.r ∥ 
         pullʳ C t'.eqf ○ pullˡ C t.eqf ○ assoc
       , (λ {s} {t₀} α →
           let r = Arr.Morphism⇒.cod⇒ α in
           begin
             ([ t.l ∘ t'.l , id ]₁ ∘ ψ.η t₀) ∘ r             ≈⟨ ∘-resp-≈ (∘-resp-≈ (Hom[-1].homomorphism) Equiv.refl) Equiv.refl ⟩
             (([ t'.l , id ]₁ ∘ [ t.l , id ]₁) ∘ ψ.η t₀) ∘ r ≈⟨ ∘-resp-≈ assoc Equiv.refl ○ assoc ⟩
             [ t'.l , id ]₁ ∘ (([ t.l , id ]₁ ∘ ψ.η t₀) ∘ r) ≈⟨ (refl⟩∘⟨ t.nat α) ○  sym-assoc ⟩
            ([ t'.l , id ]₁ ∘ Hy.F₁ r) ∘ t.ϕ.η s             ≈⟨ (∘-resp-≈ (Equiv.sym [ [-,-] ]-commute) Equiv.refl) ○ assoc ⟩
             Hx.F₁ r ∘ ([ t'.l , id ]₁ ∘ t.ϕ.η s)            ≈⟨ refl⟩∘⟨ t'.eqϕ {t = s} ⟩
             Hx.F₁ r ∘ t'.ϕ.η s                              ∎)
       ]}
  ; assoc = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv = record
    { refl = Equiv.refl , Equiv.refl
    ; sym = λ { (p , q) → Equiv.sym p , Equiv.sym q }
    ; trans = λ { (p₁ , q₁) (p₂ , q₂) → Equiv.trans p₁ p₂ , Equiv.trans q₁ q₂ }
    }
  ; ∘-resp-≈ = λ { (p₁ , q₁) (p₂ , q₂) → ∘-resp-≈ p₁ p₂ , ∘-resp-≈ q₁ q₂ }
  }

-- This functor works.
∇maybe : Functor total repairs
∇maybe = record
  { F₀ = λ x → 
      let module x = tab₀ x
          module ξx = MR2 x.ξ 
      in record { A = x.L ; ϕ = ξx.ϕ }
  ; F₁ = λ { {x} {y} f → 
      let module x = tab₀ x
          module y = tab₀ y
          module f = tot⇒ f 
      in record { u = f.l ; eq = f.eqϕ } }
  ; identity = λ {A} → Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = proj₁
  }

-- Is there a functor in the opposite direction?
∇⁻¹maybe : Functor repairs total 
∇⁻¹maybe = record
  { F₀ = λ {(record { A = A ; ϕ = ϕ }) → (A , A) ∣ ⟪ id , ϕ ⟫}
  ; F₁ = λ { {X} {Y} f → let module f = rep⇒ f in
  [ f.u , f.u 
  ∥ id-comm C , (λ α → {!  !}) ]}
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ x → x , {! Equiv.refl !}
  }

-- Instead, one would like a functor tabulator -> repairs to define MR3 as pullback?

{-

tab(MRS-Profunctor) -----V₁----> C^→ <----?---- repairs <---∇---- total

probably this functor `?` does not exist...
It seems that the only way to define a pullback is done in 

https://github.com/tetrapharmakon/agda-categories/blob/5b97012b94ad174962a136951e9ab9e73d7cbcb0/src/Categories/Rosen/FibreA.agda#L145

where the "basepoint" A is taken into consideration.
-}

Q : Functor repairs Arr.Arrow
Q = record
  { F₀ = λ x → let module x = rep₀ x in (record { arr = NaturalTransformation.η x.ϕ (record { arr = id }) })
  ; F₁ = λ { {x} {y} f → 
    let module x = rep₀ x 
        module y = rep₀ y
        module f = rep⇒ f
    in mor⇒ {!  !}}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }