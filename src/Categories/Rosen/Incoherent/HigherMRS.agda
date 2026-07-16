{-# OPTIONS --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (0ℓ; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.HigherMRS
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M)
  where

open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-poset; ≤-refl; ≤-trans; n≤1+n; m≤n⇒m≤1+n; +-cancelʳ-≡; +-assoc; +-comm; m≤n+m)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Antisymmetric)
open import Relation.Nullary using (yes; no)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.IsoComma
  using (IsoComma; IsoCommaObj; IsoComma⇒; ICproj₁; ICproj₂)
open import Categories.Category.Construction.Thin
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_)
  renaming (id to idF)
open import Data.Product using (∃; ∃-syntax)
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

_≤≤_ : Rel ℕ 0ℓ
n ≤≤ m = ∃[ k ] k + n ≡ m

≤≤to≤ : ∀ {m n} → m ≤≤ n → m ≤ n
≤≤to≤ {m} {n} (k , p) = subst (λ x → m ≤ x) p (m≤n+m m k)

letrans : ∀ {i j k} → i ≤≤ j → j ≤≤ k → i ≤≤ k
letrans {i = i} {j = j} {k = k} (n , ≡-refl) (m , ≡-refl) = n + m , ≡-trans (cong (_+ i) (+-comm n m)) (+-assoc m n i)

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

≤to≤′ : ∀ {m n} → m ≤ n → m ≤′ n
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

≤≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤≤-poset = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤≤_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ { ≡-refl → 0 , ≡-refl }
      ; trans = λ a b → letrans a b
      }
    ; antisym = λ a b → P.antisym (≤≤to≤ a) (≤≤to≤ b)
    }
  }


-- ℕ as a poset category.
pℕ : Category 0ℓ 0ℓ 0ℓ
pℕ = Thin 0ℓ prufa

pℕ′ : Category 0ℓ 0ℓ 0ℓ
pℕ′ = Thin 0ℓ ≤-poset

pℕ′≤ : Category 0ℓ 0ℓ 0ℓ
pℕ′≤ = Thin 0ℓ ≤≤-poset

-- 𝕚𝕄ℝ𝕊-F/η: a downward functor together with compatibility against V.
𝕚𝕄ℝ𝕊-F : ∀ {n m} → m ≤≤ n → Functor (𝕚𝕄ℝ𝕊ₒ n) (𝕚𝕄ℝ𝕊ₒ m)
𝕚𝕄ℝ𝕊-F {n} {m} (zero , ≡-refl) = idF --idF
𝕚𝕄ℝ𝕊-F {n} {m} (suc w , ≡-refl) = 𝕚𝕄ℝ𝕊-F {n = w + m} (w , ≡-refl) ∘F Π-MRS (w + m)

proof-irrelevance : ∀ {n} {m} (z : ℕ) (q1 q2 : z + m ≡ n) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n = n} (z , q1)) (𝕚𝕄ℝ𝕊-F (z , q2))
proof-irrelevance {n} {m} z q1 q2 with q1 | q2
... | ≡-refl | ≡-refl = NI.refl

η-canon : (z m : ℕ) → NaturalIsomorphism (V m ∘F 𝕚𝕄ℝ𝕊-F {n = z + m} (z , ≡-refl)) (V (z + m))
η-canon zero m = NI.unitorʳ
η-canon (suc w) m =
  NI.trans
    (NI.sym-associator (Π-MRS (w + m)) (𝕚𝕄ℝ𝕊-F {n = w + m} (w , ≡-refl)) (V m))
    (NI.trans (η-canon w m ⓘʳ Π-MRS (w + m)) (VΠ (w + m)))

𝕚𝕄ℝ𝕊-η : ∀ {n m} → (m≤′n : m ≤≤ n) → NaturalIsomorphism (V m ∘F (𝕚𝕄ℝ𝕊-F m≤′n)) (V n)
𝕚𝕄ℝ𝕊-η {n} {m} (k , k+m≡n) with k+m≡n
... | ≡-refl = η-canon k m

private module ElMRS = Category τ'[iMR2]
private module 𝕋MRS = Category 𝕋MRS

trueFact : ∀ {i j k}
      → ∀ (n m : ℕ)
      → (p : n + m + k ≡ i)
      → (p′ : n + k ≡ j)
      → (p″ : m + j ≡ i)
      → NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n = i} {m = k} (n + m , p))
                           (𝕚𝕄ℝ𝕊-F {n = j} {m = k} (n , p′) ∘F 𝕚𝕄ℝ𝕊-F {n = i} {m = j} (m , p″))
trueFact zero m ≡-refl ≡-refl ≡-refl = NI.sym NI.unitorˡ
trueFact {k = k} (suc n) m ≡-refl ≡-refl zz = {!   !} -- {!   !} ⓘᵥ ((trueFact n m ≡-refl ≡-refl {!   !}) ⓘʳ Π-MRS (n + m + k)) ⓘᵥ {!   !}
  where furbo : ∀ {n m k} → m + (n + k) ≡ n + m + k
        furbo {n} {m} {k} rewrite +-comm n m = ≡-sym (+-assoc m n k)

final : ∀ {i j k}
      → (g : i ≤≤ j)
      → (f : j ≤≤ k)
      → NaturalIsomorphism (𝕚𝕄ℝ𝕊-F (letrans g f)) (𝕚𝕄ℝ𝕊-F g ∘F 𝕚𝕄ℝ𝕊-F f)
final (n , ≡-refl) (zero , ≡-refl) = {!   !}
final (n , ≡-refl) (suc j , ≡-refl) = {!   !}


-- iMRS-chain: the chain … → 𝕚𝕄ℝ𝕊ₒ 2 → 𝕚𝕄ℝ𝕊ₒ 1 → 𝕚𝕄ℝ𝕊ₒ 0 as ℕ^op → Cats.
iMRS-chain : Functor (Category.op pℕ′≤) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
iMRS-chain = record
  { F₀ = 𝕚𝕄ℝ𝕊ₒ -- 𝕚𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤′n → 𝕚𝕄ℝ𝕊-F m≤′n
  ; identity = λ { {n} → NI.refl } --lemma-id {n} }
  ; homomorphism = λ { {n} {m} {k} {f} {g} → {!   !} }
  ; F-resp-≈ = λ { {n} {m} {z1 , q1} {z2 , q2} _ → {!   !} }
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
