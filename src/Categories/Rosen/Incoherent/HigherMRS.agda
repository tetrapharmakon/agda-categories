{-# OPTIONS --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (0ℓ; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.HigherMRS
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M)
  where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-poset)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym)
open import Relation.Binary using (Antisymmetric)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.IsoComma
  using (IsoComma; IsoCommaObj; IsoComma⇒; ICproj₁; ICproj₂)
open import Categories.Category.Construction.Thin 
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_)
  renaming (id to idF)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Profunctor.Tabulator using (tab₀; tab⇒)
open import Categories.Morphism as BaseMorphism using (_≅_; Iso)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism; niHelper; _ⓘˡ_; _ⓘʳ_;_ⓘᵥ_)

open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Elements Cl
open import Categories.Rosen.Incoherent.Functors Cl
open import Categories.Rosen.Tabulator Cl using (V₁; 𝕋MRS)

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₀; [_,_]₁)

-- Incoherent higher (M,R)-systems: diagrams
-- A —f→ B —ϕ→ [A,B] —ϕ₂→ [B,[A,B]] —ϕ₃→ [[A,B],[B,[A,B]]] —→ ...
-- without the natural transformation condition of full MR2.

-- iMRS3: the 3rd level, IsoComma of ℝ (from ProElements) and V₁ (from
-- Tabulator).
iMRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
iMRS3 = IsoComma ℝ [_]f

-- 𝕚𝕄ℝ𝕊 n: the n-th level category together with a functor to Arr.Arrow.
𝕚𝕄ℝ𝕊 : (n : ℕ) → Σ (Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
  (λ x → Functor x Arr.Arrow)
𝕚𝕄ℝ𝕊 zero = iMRS3 , record
  { F₀ = λ x → let module x = IsoCommaObj x in record { arr = iMR2.ϕ (iMR2₀.ξ x.a) }
  ; F₁ = λ { {A} {B} f → 
    let module A = IsoCommaObj A
        module B = IsoCommaObj B
        module f = IsoComma⇒ f 
        ℓ = twiMR2⇒.l f.f
        r = twiMR2⇒.r f.f
        equ = Equiv.sym (twiMR2⇒.eqϕ f.f)
    in mor⇒ {dom⇒ = r} {cod⇒ = [ ℓ , r ]₁} equ }
  ; identity = refl , [-,-].identity
  ; homomorphism = refl , [-,-].homomorphism
  ; F-resp-≈ = λ z → z .proj₁ .proj₂ , [-,-].F-resp-≈ (z .proj₁)
  }
𝕚𝕄ℝ𝕊 (suc n)
  = let MRSn = proj₂ (𝕚𝕄ℝ𝕊 n)
    in IsoComma ℝ MRSn
  , (proj₂ (𝕚𝕄ℝ𝕊 n) ∘F ICproj₂)

-- 𝕚𝕄ℝ𝕊ₒ n: the n-th level category.
𝕚𝕄ℝ𝕊ₒ : (n : ℕ) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
𝕚𝕄ℝ𝕊ₒ n = proj₁ (𝕚𝕄ℝ𝕊 n)

-- Π-MRS n: projection from level (suc n) down to level n.
Π-MRS : (n : ℕ) → Functor (𝕚𝕄ℝ𝕊ₒ (suc n)) (𝕚𝕄ℝ𝕊ₒ n)
Π-MRS n = ICproj₂

module MRc {n} = Category (𝕚𝕄ℝ𝕊ₒ n)
private module M0   = Category (𝕚𝕄ℝ𝕊ₒ zero)
private module ArrC = Category Arr.Arrow
private module ArrMR = MR Arr.Arrow

V : (n : ℕ) → Functor (𝕚𝕄ℝ𝕊ₒ n) Arr.Arrow
V n = proj₂ (𝕚𝕄ℝ𝕊 n)

reduce : (k : ℕ) → Functor (𝕚𝕄ℝ𝕊ₒ k) (𝕚𝕄ℝ𝕊ₒ 0)
reduce 0 = idF
reduce (suc k) = reduce k ∘F Π-MRS k

VΠ : (k : ℕ) → NaturalIsomorphism (V k ∘F Π-MRS k) (V (suc k))
VΠ k = niHelper (record
  { η = λ X → ArrC.id
      {Functor.F₀ (V k) (Functor.F₀ (Π-MRS k) X)}
  ; η⁻¹ = λ X → ArrC.id
      {Functor.F₀ (V k) (Functor.F₀ (Π-MRS k) X)}
  ; commute = λ f →
      ArrMR.id-comm-sym
        {f = Functor.F₁ (V k ∘F Π-MRS k) f}
  ; iso = λ X → record
      { isoˡ = ArrC.identity²
          {Functor.F₀ (V k) (Functor.F₀ (Π-MRS k) X)}
      ; isoʳ = ArrC.identity²
          {Functor.F₀ (V k) (Functor.F₀ (Π-MRS k) X)}
      }
  })

reduce-compat : (k : ℕ) → NaturalIsomorphism (V 0 ∘F reduce k) (V k)
reduce-compat 0 = NI.unitorʳ
reduce-compat (suc k) =
  NI.trans (NI.sym-associator (Π-MRS k) (reduce k) (V 0))
    (NI.trans ((reduce-compat k) ⓘʳ Π-MRS k) (VΠ k))

open import Relation.Binary.Core using (Rel)

data _≤_ : Rel ℕ 0ℓ where
  ≤-refl  : ∀ {n} → n ≤ n
  ≤-trans : ∀ {m n k} (m≤n : m ≤ n) (n≤k : n ≤ k) → m ≤ k
  ≤+1     : ∀ {n} → n ≤ suc n

≤-suc-inj : ∀ {a b} → suc a ≤ suc b → a ≤ b
≤-suc-inj ≤-refl = ≤-refl
≤-suc-inj {a} {b} (≤-trans p q) = ≤-trans (≤-suc-inj {!   !}) (≤-suc-inj {!   !})
≤-suc-inj ≤+1 = ≤+1

¬suc≤ : ∀ {m} → suc m ≤ m → ⊥
¬suc≤ {zero} = {!   !} -- ()
¬suc≤ {suc m} p = ¬suc≤ {m} (≤-suc-inj p)

antisym : Relation.Binary.Antisymmetric _≡_ _≤_
antisym ≤-refl y = ≡-refl
antisym (≤-trans i≤j j≤k) k≤i with antisym i≤j (≤-trans j≤k k≤i)
... | ≡-refl = antisym j≤k k≤i
antisym ≤+1 (≤-trans p q) = ⊥-elim (¬suc≤ (≤-trans p q))
open import Relation.Binary using (Poset)

prufa : Poset 0ℓ 0ℓ 0ℓ
prufa = record 
  { Carrier = ℕ 
  ; _≈_ = _≡_ 
  ; _≤_ = _≤_ 
  ; isPartialOrder = record 
    { isPreorder = record 
      { isEquivalence = isEquivalence
      ; reflexive = λ {  ≡-refl → ≤-refl }
      ; trans = ≤-trans 
      } 
    ; antisym = {!   !} 
    } 
  }

-- ℕ as a poset category.
pℕ : Category 0ℓ 0ℓ 0ℓ
pℕ = Thin 0ℓ prufa



-- 𝕚𝕄ℝ𝕊-F/η: a downward functor together with compatibility against V.
𝕚𝕄ℝ𝕊-F : ∀ {n m} → m ≤ n → Functor (𝕚𝕄ℝ𝕊ₒ n) (𝕚𝕄ℝ𝕊ₒ m)
𝕚𝕄ℝ𝕊-F {n} {m} ≤-refl = idF
𝕚𝕄ℝ𝕊-F {n} {m} (≤-trans {m} {x} {n} m≤x x≤n) = 
    let dis = 𝕚𝕄ℝ𝕊-F {x} {m} m≤x
        dat = 𝕚𝕄ℝ𝕊-F {n} {x} x≤n
    in dis ∘F dat
𝕚𝕄ℝ𝕊-F {suc n} {n} ≤+1 = Π-MRS n

𝕚𝕄ℝ𝕊-η : ∀ {n m} → (m≤n : m ≤ n) → NaturalIsomorphism (V m ∘F (𝕚𝕄ℝ𝕊-F m≤n)) (V n)
𝕚𝕄ℝ𝕊-η {n} {m} ≤-refl = NI.unitorʳ
𝕚𝕄ℝ𝕊-η {n} {m} (≤-trans {m} {x} {n} m≤x x≤n) = 
  let θ   = 𝕚𝕄ℝ𝕊-η {x} {m} m≤x 
      θ'  = 𝕚𝕄ℝ𝕊-η {n} {x} x≤n
      dis = 𝕚𝕄ℝ𝕊-F {x} {m} m≤x
      dat = 𝕚𝕄ℝ𝕊-F {n} {x} x≤n
  in θ' ⓘᵥ (θ ⓘʳ dat) ⓘᵥ NI.sym-associator dat dis (V m)
𝕚𝕄ℝ𝕊-η {suc n} {n} ≤+1 = VΠ n

private module ElMRS = Category τ'[iMR2]
private module 𝕋MRS = Category 𝕋MRS
 
-- lemma: the downward functor at level n is naturally ≃ to the
-- identity.
lemma-id : ∀ {n : ℕ} →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n} {n} ≤-refl) (idF {C = 𝕚𝕄ℝ𝕊ₒ n})
lemma-id {n} = let module 𝕄 = Category (𝕚𝕄ℝ𝕊ₒ n) in niHelper (record 
  { η = λ X → 𝕄.id {X} 
  ; η⁻¹ = λ X → 𝕄.id {X} 
  ; commute = λ f → id-comm-sym (𝕚𝕄ℝ𝕊ₒ n) {f = f} 
  ; iso = λ X → record
      { isoˡ = 𝕄.identity² {X}
      ; isoʳ = 𝕄.identity² {X}
      }
  })

lemma-id′ : ∀ {n : ℕ} (ref : n ≤ n) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n} {n} ref) (idF {C = 𝕚𝕄ℝ𝕊ₒ n})
lemma-id′ {n} ≤-refl = let module 𝕄 = Category (𝕚𝕄ℝ𝕊ₒ n) in  niHelper (record 
  { η = λ X → 𝕄.id {A = X} 
  ; η⁻¹ = λ X → 𝕄.id {A = X} 
  ; commute = λ f → id-comm-sym (𝕚𝕄ℝ𝕊ₒ n) {f = f} 
  ; iso = λ X → record
      { isoˡ = 𝕄.identity² {X}
      ; isoʳ = 𝕄.identity² {X}
      } }) -- ok
lemma-id′ {n} (≤-trans ref ref₁) with antisym ref ref₁
lemma-id′ {n} (≤-trans ≤-refl ≤-refl) | ≡-refl = NI.unitor²
lemma-id′ {n} (≤-trans ≤-refl (≤-trans ref₁ ref₂)) | ≡-refl = lemma-id′ {n} (≤-trans ref₁ ref₂) ⓘᵥ NI.unitorˡ
lemma-id′ {n} (≤-trans (≤-trans ref ref₂) ref₁) | ≡-refl =
  let m = lemma-id′ (≤-trans ref (≤-trans ref₂ ref₁)) in
  m ⓘᵥ NI.associator (𝕚𝕄ℝ𝕊-F ref₁) (𝕚𝕄ℝ𝕊-F ref₂) (𝕚𝕄ℝ𝕊-F ref)

-- lemma-homomorphism: 𝕚𝕄ℝ𝕊-down respects composition up to natural
-- isomorphism.
lemma-homomorphism : ∀ {n m k : ℕ} (m≤n : m ≤ n) (k≤m : k ≤ m) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F (≤-trans k≤m m≤n))
    ((𝕚𝕄ℝ𝕊-F k≤m) ∘F (𝕚𝕄ℝ𝕊-F m≤n))
lemma-homomorphism {n} {m} {k} m≤n k≤m = 
  let module 𝕄 = Category (𝕚𝕄ℝ𝕊ₒ k) 
      F = 𝕚𝕄ℝ𝕊-F (≤-trans k≤m m≤n)
  in niHelper (record 
    { η = λ X → 𝕄.id
    ; η⁻¹ = λ X → 𝕄.id
    ; commute = λ f → id-comm-sym (𝕚𝕄ℝ𝕊ₒ k) {f = Functor.F₁ F f}
    ; iso = λ X → record
      { isoˡ = 𝕄.identity²
      ; isoʳ = 𝕄.identity²
      }
    })

-- lemma-Fresp: proof-irrelevance for 𝕚𝕄ℝ𝕊-down on thin morphisms.
lemma-Fresp : ∀ {n m : ℕ} (p q : m ≤ n) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F p) (𝕚𝕄ℝ𝕊-F q)
lemma-Fresp {n} {m} ≤-refl q = let module 𝕄 = Category (𝕚𝕄ℝ𝕊ₒ n) 
  in niHelper (record 
    { η = λ X → {!   !} -- Category.id (𝕚𝕄ℝ𝕊ₒ n)
    ; η⁻¹ = {!   !} 
    ; commute = {!   !} 
    ; iso = {!   !} 
    })
lemma-Fresp {n} {m} (≤-trans p p') ≤-refl = {!   !} -- absurd
lemma-Fresp {n} {m} (≤-trans p p') (≤-trans q q') = {!   !}
lemma-Fresp {n} {m} (≤-trans p p') ≤+1 = {!   !}
lemma-Fresp {n} {m} ≤+1 q = {!   !} 
  -- let module 𝕄 = Category (𝕚𝕄ℝ𝕊ₒ m) 
  -- in {!   !} -- niHelper (record 
    -- { η = λ X → {!   !} -- Category.id (𝕚𝕄ℝ𝕊ₒ m)
    -- ; η⁻¹ = λ X → {!   !} 
    -- ; commute = λ f → {!   !} 
    -- ; iso = λ X → {!   !} 
    -- }) 

{-
lemma-Fresp {n} (≤-trans p p') q = niHelper (record 
  { η = {!   !} 
  ; η⁻¹ = {!   !} 
  ; commute = {!   !} 
  ; iso = {!   !} 
  })
lemma-Fresp {n} ≤+1 q = niHelper (record 
  { η = {!   !} 
  ; η⁻¹ = {!   !} 
  ; commute = {!   !} 
  ; iso = {!   !} 
  })
-}

{-
lemma-Fresp {n = n} z≤n z≤n = niHelper (record
  { η = λ X → M0.id {Functor.F₀ (reduce n) X}
  ; η⁻¹ = λ X → M0.id {Functor.F₀ (reduce n) X}
  ; commute = λ f →
      id-comm-sym (𝕚𝕄ℝ𝕊ₒ zero)
        {f = Functor.F₁ (reduce n) f}
  ; iso = λ X → record
      { isoˡ = M0.identity² {Functor.F₀ (reduce n) X}
      ; isoʳ = M0.identity² {Functor.F₀ (reduce n) X}
      }
  })
lemma-Fresp {n = suc n'} {m = suc m'} (s≤s p) (s≤s q) = niHelper (record
  { η = λ X → {! IH.⇒.η (Functor.F₀ ? X) !}
  ; η⁻¹ = λ X → {! !}
  ; commute = λ f → {! !}
  ; iso = λ X → {! !}
  }) where module IH = NaturalIsomorphism (lemma-Fresp {n'} {m'} p q)
-}

-- iMRS-chain: the chain … → 𝕚𝕄ℝ𝕊ₒ 2 → 𝕚𝕄ℝ𝕊ₒ 1 → 𝕚𝕄ℝ𝕊ₒ 0 as ℕ^op → Cats.
iMRS-chain : Functor (Category.op pℕ) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
iMRS-chain = record
  { F₀ = 𝕚𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤n → 𝕚𝕄ℝ𝕊-F m≤n
  ; identity = λ { {n} → lemma-id {n} }
  ; homomorphism = λ { {n} {m} {k} {f} {g} → lemma-homomorphism f g }
  ; F-resp-≈ = λ { {n} {m} {f} {g} _ → lemma-Fresp f g }
  }

-- Needs MRS-chain as a parameter, so it stays here rather than at the
-- top of the file.
open import Categories.Diagram.Limit iMRS-chain
  renaming (Limit to iMRS-Limit)

-- Limit of MRS-chain.
-- iMRS∞: the limit object (the "∞-level" MRS category).
iMRS∞ = iMRS-Limit.apex
-- iMRS∞-proj: projection functors iMRS∞ → 𝕚𝕄ℝ𝕊ₒ n.
iMRS∞-proj = iMRS-Limit.proj
-- iMRS∞-commute: universal property of the limit.
iMRS∞-commute = iMRS-Limit.limit-commute
