{-# OPTIONS --without-K --allow-unsolved-metas --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (0ℓ; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.HigherMRS {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Higher-order (M,R)-systems following a Fibonacci-style construction:
-- each step A → B → [A,B] → [B,[A,B]] → ... embeds the two previous
-- levels into an internal hom.  Built as iterated IsoCommas of ℝ and Vᵢ.
-- Exports: MRS3, 𝕄ℝ𝕊, 𝕄ℝ𝕊ₒ, 𝕄ℝ𝕊ₐ, Π-MRS, pℕ, 𝕄ℝ𝕊-down, lemma,
--          MRS-chain, MRS∞, MRS∞-proj, MRS∞-commute.

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-poset;≤-refl;≤-trans)
open import Data.Product using (Σ;_,_;proj₁;proj₂)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.IsoComma using (IsoComma;IsoCommaObj;IsoComma⇒;ICproj₁;ICproj₂)
open import Categories.Category.Construction.Thin 0ℓ ≤-poset
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties using ([_]-resp-Iso)
open import Categories.Functor.Profunctor.Tabulator using (tab₀;tab⇒)
open import Categories.Morphism.Reasoning as MR
open import Categories.Morphism as Morphism using (_≅_; Iso)
open import Categories.Morphism.Properties as Morphismₚ using (Iso-∘; Iso-swap)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism;niHelper)
open import Categories.Rosen.Core Cl
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}
open import Categories.Rosen.Tabulator Cl using (V₁; 𝕋MRS)

import Reason
open Reason C
open HomReasoning
open MR

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)

-- MRS3: the 3rd level, IsoComma of ℝ (from ProElements) and V₁ (from Tabulator).
MRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
MRS3 = IsoComma ℝ V₁

-- 𝕄ℝ𝕊 n: the n-th level category together with a functor to Arr.Arrow.
𝕄ℝ𝕊 : (n : ℕ) → Σ (Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e) (λ x → Functor x Arr.Arrow)
𝕄ℝ𝕊 zero = MRS3 , V₂
  where 
    -- Base level: functor V₂ from MRS3 to Arr.Arrow.
    V₂ : Functor MRS3 Arr.Arrow 
    V₂ = record
      { F₀ = λ x → 
        let module x = IsoCommaObj x 
        in record { arr = MR2.f (tab₀.ξ x.b) }
      ; F₁ = λ { {x} {y} f → 
        let module x = IsoCommaObj x 
            module y = IsoCommaObj y 
            module f = IsoComma⇒ f
        in mor⇒ {dom⇒ = tab⇒.l f.g} {cod⇒ = tab⇒.r f.g} 
          (begin _ ≈⟨ sym-id-1 ○ assoc ⟩ 
                 _ ≈⟨ proj₁ (tab⇒.eq f.g) ⟩ 
                 _ ≈⟨ id-0 ⟩ 
                 _ ∎)}
      ; identity = Equiv.refl , Equiv.refl
      ; homomorphism = Equiv.refl , Equiv.refl
      ; F-resp-≈ = λ {(_ , dat) → (dat .proj₁) , (dat .proj₂)}
      }
𝕄ℝ𝕊 (suc n) 
  = let MRSn = proj₂ (𝕄ℝ𝕊 n) 
        module Vₙ = Functor MRSn
    in IsoComma ℝ MRSn
  , record
      { F₀ = λ x → 
        let module x = IsoCommaObj x
        in Vₙ.F₀ x.b
      ; F₁ = λ { {x} {y} f → 
        let module x = IsoCommaObj x 
            module y = IsoCommaObj y 
            module f = IsoComma⇒ f
        in Vₙ.F₁ f.g }
      ; identity = Vₙ.identity
      ; homomorphism = Vₙ.homomorphism
      ; F-resp-≈ = λ f≈g → Vₙ.F-resp-≈ (proj₂ f≈g)
      }

-- 𝕄ℝ𝕊ₒ n: the n-th level category.
𝕄ℝ𝕊ₒ : (n : ℕ) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
𝕄ℝ𝕊ₒ n = proj₁ (𝕄ℝ𝕊 n)

-- 𝕄ℝ𝕊ₐ n: the functor from the n-th level to Arr.Arrow.
𝕄ℝ𝕊ₐ : (n : ℕ) → Functor (𝕄ℝ𝕊ₒ n) Arr.Arrow
𝕄ℝ𝕊ₐ n = proj₂ (𝕄ℝ𝕊 n)

-- Π-MRS n: projection from level (suc n) down to level n.
Π-MRS : (n : ℕ) → Functor (𝕄ℝ𝕊ₒ (suc n)) (𝕄ℝ𝕊ₒ n)
Π-MRS n = ICproj₂

reduce : (k : ℕ) → Functor (𝕄ℝ𝕊ₒ k) (𝕄ℝ𝕊ₒ 0)
reduce 0 = idF
reduce (suc k) = reduce k ∘F Π-MRS k

-- ℕ as a poset category.
pℕ : Category 0ℓ 0ℓ 0ℓ
pℕ = Thin

-- 𝕄ℝ𝕊-down: functor from level n down to level m when m ≤ n.
𝕄ℝ𝕊-down : ∀ {n m} → m ≤ n → Functor (𝕄ℝ𝕊ₒ n) (𝕄ℝ𝕊ₒ m)
𝕄ℝ𝕊-down {n} z≤n = reduce n
𝕄ℝ𝕊-down (s≤s {m} {n} m≤n) = go
  where
    F-down = 𝕄ℝ𝕊-down m≤n
    module F-down = Functor F-down
    go : Functor (𝕄ℝ𝕊ₒ (suc n)) (𝕄ℝ𝕊ₒ (suc m))
    go = record
      { F₀ = λ x →
        let module x = IsoCommaObj x
        in record { a = x.a ; b = F-down.F₀ x.b ; iso = {!  !} }
      ; F₁ = λ { {x} {y} f →
        let module x = IsoCommaObj x
            module y = IsoCommaObj y
            module f = IsoComma⇒ f
        in record { f = f.f ; g = F-down.F₁ f.g ; commute = {!  !} } }
      ; identity = (refl , refl) , F-down.identity
      ; homomorphism = (refl , refl) , F-down.homomorphism
      ; F-resp-≈ = λ eq → ((eq .proj₁ .proj₁) , (eq .proj₁ .proj₂)) , F-down.F-resp-≈ (proj₂ eq)
      }


private module M0 = Category (𝕄ℝ𝕊ₒ zero)
private module ElMRS = Category ElMRS
private module 𝕋MRS = Category 𝕋MRS

-- lemma: 𝕄ℝ𝕊-down at level n is naturally ≃ to the identity. (WIP: has holes)
lemma-id : ∀ {n : ℕ} → NaturalIsomorphism (𝕄ℝ𝕊-down {n} {n} ≤-refl) (idF {C = 𝕄ℝ𝕊ₒ n})
lemma-id {zero} = niHelper (record 
  { η = λ X → M0.id {X}
  ; η⁻¹ = λ X → M0.id {X}
  ; commute = λ f → id-comm-sym (𝕄ℝ𝕊ₒ zero) {f = f}
  ; iso = λ X → record { isoˡ = M0.identity² {X} ; isoʳ = M0.identity² {X} } 
  })
lemma-id {suc n} = niHelper (record 
  { η = λ X →
      let module X = IsoCommaObj X in record
        { f = ElMRS.id
        ; g = IH.⇒.η X.b
        ; commute = {!  !}
        }
  ; η⁻¹ = λ X →
      let module X = IsoCommaObj X in record
        { f = ElMRS.id
        ; g = IH.⇐.η X.b
        ; commute = {!  !}
        }
  ; commute = λ f →
      let module f = IsoComma⇒ f
      in (id-comm-sym ElMRS {f = f.f} , IH.⇒.commute f.g)
  ; iso = λ X →
      let module X = IsoCommaObj X
      in record
        { isoˡ = (ElMRS.identity² {X.a} , Morphism.Iso.isoˡ (IH.iso X.b))
        ; isoʳ = (ElMRS.identity² {X.a} , Morphism.Iso.isoʳ (IH.iso X.b))
        }
  }) where
  module IH = NaturalIsomorphism (lemma-id {n})
  module Mn = Category (𝕄ℝ𝕊ₒ n)

-- lemma-homomorphism: 𝕄ℝ𝕊-down respects composition up to natural isomorphism.
lemma-homomorphism : ∀ {n m k : ℕ} (m≤n : m ≤ n) (k≤m : k ≤ m) →
  NaturalIsomorphism (𝕄ℝ𝕊-down (≤-trans k≤m m≤n)) ((𝕄ℝ𝕊-down k≤m) ∘F (𝕄ℝ𝕊-down m≤n))
lemma-homomorphism {n = n} z≤n z≤n = niHelper (record
  { η = λ X → M0.id
  ; η⁻¹ = λ X → M0.id
  ; commute = λ f → id-comm-sym (𝕄ℝ𝕊ₒ zero) {f = Functor.F₁ (reduce n) f}
  ; iso = λ X → record { isoˡ = M0.identity² {Functor.F₀ (reduce n) X} ; isoʳ = M0.identity² {Functor.F₀ (reduce n) X} }
  })
lemma-homomorphism (s≤s m≤n) z≤n = niHelper (record
  { η = λ X → {!  !}
  ; η⁻¹ = λ X → {!  !}
  ; commute = λ f → {!  !}
  ; iso = λ X → {!  !}
  })
lemma-homomorphism (s≤s m≤n) (s≤s k≤m) = niHelper (record
  { η = λ X → {!  !}
  ; η⁻¹ = λ X → {!  !}
  ; commute = λ f → {!  !}
  ; iso = λ X → {!  !}
  })

-- lemma-Fresp: proof-irrelevance for 𝕄ℝ𝕊-down on thin morphisms.
lemma-Fresp : ∀ {n m : ℕ} (p q : m ≤ n) → NaturalIsomorphism (𝕄ℝ𝕊-down p) (𝕄ℝ𝕊-down q)
lemma-Fresp {n = n} z≤n z≤n = niHelper (record
  { η = λ X → M0.id {Functor.F₀ (reduce n) X}
  ; η⁻¹ = λ X → M0.id {Functor.F₀ (reduce n) X}
  ; commute = λ f → id-comm-sym (𝕄ℝ𝕊ₒ zero) {f = Functor.F₁ (reduce n) f}
  ; iso = λ X → record { isoˡ = M0.identity² {Functor.F₀ (reduce n) X} ; isoʳ = M0.identity² {Functor.F₀ (reduce n) X} }
  })
lemma-Fresp (s≤s p) (s≤s q) = niHelper (record
  { η = λ X → {!  !}
  ; η⁻¹ = λ X → {!  !}
  ; commute = λ f → {!  !}
  ; iso = λ X → {!  !}
  })
  
-- MRS-chain: the chain ... → 𝕄ℝ𝕊ₒ 2 → 𝕄ℝ𝕊ₒ 1 → 𝕄ℝ𝕊ₒ 0 as ℕ^op → Cats. (WIP: has holes)
MRS-chain : Functor (Category.op pℕ) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
MRS-chain = record
  { F₀ = 𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤n → 𝕄ℝ𝕊-down m≤n
  ; identity = λ { {n} → lemma-id {n} } 
   ; homomorphism = λ { {n} {m} {k} {f} {g} → lemma-homomorphism f g }
   ; F-resp-≈ = λ { {n} {m} {f} {g} _ → lemma-Fresp f g }
  }

open import Categories.Diagram.Limit MRS-chain renaming (Limit to MRS-Limit)

-- Limit of MRS-chain.
-- MRS∞: the limit object (the "∞-level" MRS category).
MRS∞ = MRS-Limit.apex
-- MRS∞-proj: projection functors MRS∞ → 𝕄ℝ𝕊ₒ n.
MRS∞-proj = MRS-Limit.proj
-- MRS∞-commute: universal property of the limit.
MRS∞-commute = MRS-Limit.limit-commute
