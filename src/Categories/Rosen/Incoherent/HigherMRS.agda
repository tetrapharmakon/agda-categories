{-# OPTIONS --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (0ℓ; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.HigherMRS
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M)
  where

open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-poset; ≤-refl; ≤-trans; n≤1+n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)
open import Relation.Binary using (Antisymmetric)
open import Relation.Nullary using (yes; no)

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

data _≤′_ : Rel ℕ 0ℓ where
  ≤′-refl  : ∀ {n} → n ≤′ n
  ≤′-trans : ∀ {m n k} (m≤′n : m ≤′ n) (n≤′k : n ≤′ k) → m ≤′ k
  ≤′+1     : ∀ {n} → n ≤′ suc n

≤′to≤ : ∀ {m n} → m ≤′ n → m ≤ n
≤′to≤ ≤′-refl        = ≤-refl
≤′to≤ (≤′-trans p q) = ≤-trans (≤′to≤ p) (≤′to≤ q)
≤′to≤ ≤′+1           = n≤1+n _

lemma : ∀ {n} → 0 ≤′ n
lemma {n = zero} = ≤′-refl
lemma {n = suc n} = ≤′-trans lemma ≤′+1

lemma-2 : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
lemma-2 ≤′-refl = ≤′-refl
lemma-2 (≤′-trans e e₁) = ≤′-trans (lemma-2 e) (lemma-2 e₁)
lemma-2 ≤′+1 = ≤′+1

≤to≤′ : ∀ {m n} → m ≤ n  → m ≤′ n
≤to≤′ z≤n = lemma
≤to≤′ (s≤s a) = lemma-2 (≤to≤′ a)

open import Relation.Binary using (Poset)

module P = Poset ≤-poset

≤′-antisym : Relation.Binary.Antisymmetric _≡_ _≤′_
≤′-antisym a b = P.antisym (≤′to≤ a) (≤′to≤ b)

prufa : Poset 0ℓ 0ℓ 0ℓ
prufa = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤′_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ {  ≡-refl → ≤′-refl }
      ; trans = ≤′-trans
      }
    ; antisym = ≤′-antisym
    }
  }

-- ℕ as a poset category.
pℕ : Category 0ℓ 0ℓ 0ℓ
pℕ = Thin 0ℓ prufa



-- 𝕚𝕄ℝ𝕊-F/η: a downward functor together with compatibility against V.
𝕚𝕄ℝ𝕊-F : ∀ {n m} → m ≤′ n → Functor (𝕚𝕄ℝ𝕊ₒ n) (𝕚𝕄ℝ𝕊ₒ m)
𝕚𝕄ℝ𝕊-F {n} {m} ≤′-refl = idF
𝕚𝕄ℝ𝕊-F {n} {m} (≤′-trans {m} {x} {n} m≤′x x≤′n) = 𝕚𝕄ℝ𝕊-F {x} {m} m≤′x ∘F 𝕚𝕄ℝ𝕊-F {n} {x} x≤′n
𝕚𝕄ℝ𝕊-F {suc n} {n} ≤′+1 = Π-MRS n

𝕚𝕄ℝ𝕊-η : ∀ {n m} → (m≤′n : m ≤′ n) → NaturalIsomorphism (V m ∘F (𝕚𝕄ℝ𝕊-F m≤′n)) (V n)
𝕚𝕄ℝ𝕊-η {n} {m} ≤′-refl = NI.unitorʳ
𝕚𝕄ℝ𝕊-η {n} {m} (≤′-trans {m} {x} {n} m≤′x x≤′n) =
  let θ   = 𝕚𝕄ℝ𝕊-η {x} {m} m≤′x
      θ'  = 𝕚𝕄ℝ𝕊-η {n} {x} x≤′n
      dis = 𝕚𝕄ℝ𝕊-F {x} {m} m≤′x
      dat = 𝕚𝕄ℝ𝕊-F {n} {x} x≤′n
  in θ' ⓘᵥ (θ ⓘʳ dat) ⓘᵥ NI.sym-associator dat dis (V m)
𝕚𝕄ℝ𝕊-η {suc n} {n} ≤′+1 = VΠ n

private module ElMRS = Category τ'[iMR2]
private module 𝕋MRS = Category 𝕋MRS

-- lemma: the downward functor at level n is naturally ≃ to the
-- identity.
lemma-id : ∀ {n : ℕ} →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n} {n} ≤′-refl) (idF {C = 𝕚𝕄ℝ𝕊ₒ n})
lemma-id {zero} = niHelper (record
  { η = λ X → M0.id {X}
  ; η⁻¹ = λ X → M0.id {X}
  ; commute = λ f → id-comm-sym (𝕚𝕄ℝ𝕊ₒ zero) {f = f}
  ; iso = λ X → record
      { isoˡ = M0.identity² {X}
      ; isoʳ = M0.identity² {X}
      }
  })
lemma-id {suc n} = niHelper (record
  { η = λ X → Mn+1.id {A = X}
  ; η⁻¹ = λ X → Mn+1.id {A = X}
  ; commute = λ f → id-comm-sym (𝕚𝕄ℝ𝕊ₒ (suc n)) {f = f}
  ; iso = λ X → record
      { isoˡ = Mn+1.identity² {X}
      ; isoʳ = Mn+1.identity² {X}
      }
  }) where module Mn+1 = Category (𝕚𝕄ℝ𝕊ₒ (suc n))


lemma-id′ : ∀ {n : ℕ} (ref : n ≤′ n) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n} {n} ref) (idF {C = 𝕚𝕄ℝ𝕊ₒ n})
lemma-id′ {n} ≤′-refl = let module 𝕄 = Category (𝕚𝕄ℝ𝕊ₒ n) in  niHelper (record 
  { η = λ X → 𝕄.id {A = X} 
  ; η⁻¹ = λ X → 𝕄.id {A = X} 
  ; commute = λ f → id-comm-sym (𝕚𝕄ℝ𝕊ₒ n) {f = f} 
  ; iso = λ X → record
      { isoˡ = 𝕄.identity² {X}
      ; isoʳ = 𝕄.identity² {X}
      } })
lemma-id′ {n} (≤′-trans ref ref₁) with ≤′-antisym ref ref₁
lemma-id′ {n} (≤′-trans ≤′-refl ≤′-refl) | ≡-refl = NI.unitor²
lemma-id′ {n} (≤′-trans ≤′-refl (≤′-trans ref₁ ref₂)) | ≡-refl = 
  lemma-id′ {n} (≤′-trans ref₁ ref₂) ⓘᵥ NI.unitorˡ
lemma-id′ {n} (≤′-trans (≤′-trans ref ref₂) ref₁) | ≡-refl =
  let m = lemma-id′ (≤′-trans ref (≤′-trans ref₂ ref₁)) in
  m ⓘᵥ NI.associator (𝕚𝕄ℝ𝕊-F ref₁) (𝕚𝕄ℝ𝕊-F ref₂) (𝕚𝕄ℝ𝕊-F ref)




-- lemma-homomorphism: 𝕚𝕄ℝ𝕊-down respects composition up to natural
-- isomorphism.
lemma-homomorphism : ∀ {n m k : ℕ} (m≤′n : m ≤′ n) (k≤′m : k ≤′ m) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F (≤′-trans k≤′m m≤′n))
    ((𝕚𝕄ℝ𝕊-F k≤′m) ∘F (𝕚𝕄ℝ𝕊-F m≤′n))
lemma-homomorphism {n} {m} {k} m≤′n k≤′m = niHelper {!   !} 
  where module Mn = Category (𝕚𝕄ℝ𝕊ₒ n)

one-step : ∀ {n₁ m : ℕ}
   (p : n₁ ≤ suc m)
   (q : m ≤ n₁)
   → n₁ ≡ m ⊎ n₁ ≡ suc m
one-step z≤n z≤n = inj₁ ≡-refl
one-step (s≤s z≤n) z≤n = inj₂ ≡-refl
one-step (s≤s p) (s≤s q) with one-step p q
... | inj₁ ≡-refl = inj₁ ≡-refl
... | inj₂ ≡-refl = inj₂ ≡-refl

one-step′ : ∀ {n₁ m : ℕ}
   (p : n₁ ≤′ suc m)
   (q : m ≤′ n₁)
   → n₁ ≡ m ⊎ n₁ ≡ suc m
one-step′ p q = one-step (≤′to≤ p) (≤′to≤ q)

lemma-Fresp-≤′+1 : ∀ {m : ℕ} (p : m ≤′ suc m) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {m = m} ≤′+1) (𝕚𝕄ℝ𝕊-F {m = m}  p)
lemma-Fresp-≤′+1 (≤′-trans q p₁) with one-step′ p₁ q
... | inj₁ ≡-refl = {!  lemma-Fresp-≤′+1 p₁ !} -- usare questo + lemma-id′ qui
... | inj₂ ≡-refl = {! lemma-Fresp-≤′+1 q   !} -- usare questo + lemma-id′ qui
lemma-Fresp-≤′+1 ≤′+1 = {!   !} -- ok

-- lemma-Fresp: proof-irrelevance for 𝕚𝕄ℝ𝕊-down on thin morphisms.
lemma-Fresp : ∀ {n m : ℕ} (p q : m ≤′ n) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F p) (𝕚𝕄ℝ𝕊-F q)
lemma-Fresp {n} ≤′-refl ≤′-refl = {!   !} -- ok
lemma-Fresp {n} ≤′-refl (≤′-trans n≤′n n≤′n₁) with ≤′-antisym n≤′n n≤′n₁
... | ≡-refl = lemma-id′ ≤′-refl -- usare lemma-id′ qui
lemma-Fresp {n} (≤′-trans p p₁) ≤′-refl with ≤′-antisym p p₁
... | ≡-refl = {!   !} -- usare lemma-id′ qui
lemma-Fresp {n} (≤′-trans p p₁) (≤′-trans q q₁) = {!   !} -- usare ipotesi induttiva qui
lemma-Fresp {n} (≤′-trans p p₁) ≤′+1 with one-step′ p₁ p
... | inj₁ ≡-refl = {!  lemma-Fresp-≤′+1 p₁ !} -- usare questo + lemma-id′ qui
... | inj₂ ≡-refl = {!  lemma-Fresp-≤′+1 p !} -- usare questo + lemma-id′ qui
lemma-Fresp {n} ≤′+1 (≤′-trans q q₁) with one-step′ q₁ q
... | inj₁ ≡-refl = {! lemma-Fresp-≤′+1 q₁  !}  -- usare questo + lemma-id′ qui
... | inj₂ ≡-refl = {!  lemma-Fresp-≤′+1 q  !}  -- usare questo + lemma-id′ qui
lemma-Fresp {n} ≤′+1 ≤′+1 = {!   !} -- ok



-- iMRS-chain: the chain … → 𝕚𝕄ℝ𝕊ₒ 2 → 𝕚𝕄ℝ𝕊ₒ 1 → 𝕚𝕄ℝ𝕊ₒ 0 as ℕ^op → Cats.
iMRS-chain : Functor (Category.op pℕ) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
iMRS-chain = record
  { F₀ = 𝕚𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤′n → 𝕚𝕄ℝ𝕊-F m≤′n
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
