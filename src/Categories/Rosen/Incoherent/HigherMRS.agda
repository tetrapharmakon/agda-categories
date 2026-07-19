{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (0ℓ; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.HigherMRS
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M)
  where

open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-poset; ≤-refl; ≤-trans; n≤1+n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)
open import Relation.Binary using (Antisymmetric)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)

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
-- A —f→ B —Φ→ [A,B] —Φ₂→ [B,[A,B]] —Φ₃→ [[A,B],[B,[A,B]]] —→ ...
-- without the natural transformation condition of full MR2.

-- iMRS3: the 3rd level, IsoComma of ℝ (from ProElements) and V₁ (from
-- Tabulator).
iMRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
iMRS3 = IsoComma ℝ [_]f

-- 𝕚𝕄ℝ𝕊 n: the n-th level category together with a functor to Arr.Arrow.
𝕚𝕄ℝ𝕊 : (n : ℕ) → Σ (Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
  (λ x → Functor x Arr.Arrow)
𝕚𝕄ℝ𝕊 zero = iMRS3 , record
  { F₀ = λ x → let module x = IsoCommaObj x in record { arr = iMR2.Φ (iMR2₀.ξ x.a) }
  ; F₁ = λ { {A} {B} f →
    let module A = IsoCommaObj A
        module B = IsoCommaObj B
        module f = IsoComma⇒ f
        ℓ = twiMR2⇒.l f.f
        r = twiMR2⇒.r f.f
        equ = Equiv.sym (twiMR2⇒.eqΦ f.f)
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

data _≈′_ : ∀ {n m} → (p q : n ≤′ m) → Set 0ℓ where
  ≈-assoc : ∀ {n m k l}
            (p : n ≤′ m) (q : m ≤′ k) (r : k ≤′ l)
        → ≤′-trans p (≤′-trans q r)
        ≈′ ≤′-trans (≤′-trans p q) r
  id-l : ∀ {n m}
        {p : n ≤′ m}
        → ≤′-trans ≤′-refl p ≈′ p
  id-r : ∀ {n m}
        {p : n ≤′ m}
        → ≤′-trans p ≤′-refl ≈′ p
  refe : ∀ {n m} {p : n ≤′ m}
      → p ≈′ p
  trans-cong :
    ∀ {n m k} {p q : n ≤′ m} {r s : m ≤′ k}
    → p ≈′ q
    → r ≈′ s
    → ≤′-trans p r ≈′ ≤′-trans q s
  transs :
    ∀ {n m} {p q r : n ≤′ m}
    → p ≈′ q
    → q ≈′ r
    → p ≈′ r
  symm :
    ∀ {n m} {p q : n ≤′ m}
    → p ≈′ q
    → q ≈′ p

data _≤2_ : Rel ℕ 0ℓ where
  ≤2-refl  : ∀ {n} → n ≤2 n
  ≤2-inc   : ∀ {m n} (m≤′n : m ≤2 n)
           → m ≤2 suc n

concat : ∀ {i j k} → i ≤2 j → j ≤2 k → i ≤2 k
concat a ≤2-refl = a
concat a (≤2-inc b) = ≤2-inc (concat a b)

convert : ∀ {m n} → m ≤′ n → m ≤2 n
convert ≤′-refl = ≤2-refl
convert (≤′-trans r q) = concat (convert r) (convert q)
convert ≤′+1 = ≤2-inc ≤2-refl

reconvert : ∀ {m n} → m ≤2 n → m ≤′ n
reconvert ≤2-refl = ≤′-refl
reconvert (≤2-inc a) = ≤′-trans (reconvert a) ≤′+1

reconv-concat : ∀ {i j k} (a : i ≤2 j) (b : j ≤2 k) → reconvert (concat a b) ≈′ ≤′-trans (reconvert a) (reconvert b)
reconv-concat a ≤2-refl = symm id-r
reconv-concat a (≤2-inc b) = transs (trans-cong (reconv-concat a b) refe) (symm (≈-assoc (reconvert a) (reconvert b) ≤′+1))

reccon : ∀ {m n} (a : m ≤′ n) → reconvert (convert a) ≈′ a
reccon ≤′-refl = refe
reccon (≤′-trans a a₁) = transs (reconv-concat (convert a) (convert a₁)) (trans-cong (reccon a) (reccon a₁))
reccon ≤′+1 = id-l

mangh : ∀ {i j} → suc i ≤2 j → i ≤2 j
mangh ≤2-refl = ≤2-inc ≤2-refl
mangh (≤2-inc r) = ≤2-inc (mangh r)

inv : ∀ {i j} → suc i ≤2 suc j → i ≤2 j
inv ≤2-refl = ≤2-refl
inv (≤2-inc r) = mangh r

impossibl : ∀ {n} → ¬ (suc n ≤2 n)
impossibl {zero} ()
impossibl {suc n} r = impossibl {n = n} (inv r)

contractible-one-steeep : ∀ {m n} {a b : m ≤2 n} → reconvert a ≈′ reconvert b
contractible-one-steeep {a = ≤2-refl} {b = ≤2-refl} = refe
contractible-one-steeep {a = ≤2-refl} {b = ≤2-inc b} = ⊥-elim (impossibl b)
contractible-one-steeep {a = ≤2-inc a} {b = ≤2-refl} = ⊥-elim (impossibl a)
contractible-one-steeep {a = ≤2-inc a} {b = ≤2-inc b} = trans-cong contractible-one-steeep refe

truecontractible : ∀ {n m} → (p q : n ≤′ m) → p ≈′ q
truecontractible p q = transs (symm (reccon p)) (transs contractible-one-steeep (reccon q))

≤′to≤ : ∀ {m n} → m ≤′ n → m ≤ n
≤′to≤ ≤′-refl        = ≤-refl
≤′to≤ (≤′-trans p q) = ≤-trans (≤′to≤ p) (≤′to≤ q)
≤′to≤ ≤′+1           = n≤1+n _

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

lemma-id : ∀ {n : ℕ} →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F {n} {n} ≤′-refl) (idF {C = 𝕚𝕄ℝ𝕊ₒ n})
lemma-id {n} = NI.refl

-- lemma-homomorphism: 𝕚𝕄ℝ𝕊-down respects composition up to natural
-- isomorphism.
lemma-homomorphism : ∀ {n m k : ℕ} (m≤′n : m ≤′ n) (k≤′m : k ≤′ m) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F (≤′-trans k≤′m m≤′n))
    ((𝕚𝕄ℝ𝕊-F k≤′m) ∘F (𝕚𝕄ℝ𝕊-F m≤′n))
lemma-homomorphism {n} {m} {k} m≤′n k≤′m = NI.refl where module Mn = Category (𝕚𝕄ℝ𝕊ₒ n)

lemma-Frespa : ∀ {n m : ℕ} {p q : m ≤′ n} (e : p ≈′ q) →
  NaturalIsomorphism (𝕚𝕄ℝ𝕊-F p) (𝕚𝕄ℝ𝕊-F q)
lemma-Frespa (≈-assoc p q r) = NI.sym (NI.associator (𝕚𝕄ℝ𝕊-F r) (𝕚𝕄ℝ𝕊-F q) (𝕚𝕄ℝ𝕊-F p))
lemma-Frespa id-l = NI.unitorˡ
lemma-Frespa id-r = NI.unitorʳ
lemma-Frespa refe = NI.refl
lemma-Frespa (trans-cong e e₁) = let a = lemma-Frespa e; b = lemma-Frespa e₁ in a NI.ⓘₕ b
lemma-Frespa (transs e e₁) = let a = lemma-Frespa e; b = lemma-Frespa e₁ in NI.trans a b
lemma-Frespa (symm p) = NI.sym (lemma-Frespa p)

-- iMRS-chain: the chain … → 𝕚𝕄ℝ𝕊ₒ 2 → 𝕚𝕄ℝ𝕊ₒ 1 → 𝕚𝕄ℝ𝕊ₒ 0 as ℕ^op → Cats.
iMRS-chain : Functor (Category.op pℕ) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
iMRS-chain = record
  { F₀ = 𝕚𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤′n → 𝕚𝕄ℝ𝕊-F m≤′n
  ; identity = λ { {n} → lemma-id {n} }
  ; homomorphism = λ { {n} {m} {k} {f} {g} → lemma-homomorphism f g }
  ; F-resp-≈ = λ { {n} {m} {f} {g} _ → lemma-Frespa (truecontractible f g) }
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
