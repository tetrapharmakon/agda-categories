{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (0ℓ; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.HigherMRS
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M)
  where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-poset; ≤-refl; ≤-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.IsoComma
  using (IsoComma; IsoCommaObj; IsoComma⇒; ICproj₁; ICproj₂)
open import Categories.Category.Construction.Thin 0ℓ ≤-poset
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_)
  renaming (id to idF)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Profunctor.Tabulator using (tab₀; tab⇒)
open import Categories.Morphism as BaseMorphism using (_≅_; Iso)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism; niHelper; _ⓘˡ_; _ⓘʳ_)

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
𝕚𝕄ℝ𝕊 zero = iMRS3 , {! !}
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

-- ℕ as a poset category.
pℕ : Category 0ℓ 0ℓ 0ℓ
pℕ = Thin

-- 𝕚𝕄ℝ𝕊-down: a downward functor together with compatibility against V.
𝕚𝕄ℝ𝕊-down : ∀ {n m} → m ≤ n →
  Σ (Functor (𝕚𝕄ℝ𝕊ₒ n) (𝕚𝕄ℝ𝕊ₒ m))
    (λ F-down → NaturalIsomorphism (V m ∘F F-down) (V n))
𝕚𝕄ℝ𝕊-down {n} z≤n = reduce n , reduce-compat n
𝕚𝕄ℝ𝕊-down (s≤s {m} {n} m≤n) = go , down-compat
  where
    down = 𝕚𝕄ℝ𝕊-down m≤n
    F-down = proj₁ down
    module F-down = Functor F-down
    module down = NaturalIsomorphism (proj₂ down)
    module ArrM = BaseMorphism Arr.Arrow

    go : Functor (𝕚𝕄ℝ𝕊ₒ (suc n)) (𝕚𝕄ℝ𝕊ₒ (suc m))
    go = record
      { F₀ = λ x →
          let module x = IsoCommaObj x
              iso' = record
                { from = down.⇒.η x.b
                ; to   = down.⇐.η x.b
                ; iso  = down.iso x.b
                }
          in record
            { a = x.a
            ; b = F-down.F₀ x.b
            ; iso = ArrM.≅.trans x.iso (ArrM.≅.sym iso')
            }
      ; F₁ = λ { {x} {y} f →
          let module x = IsoCommaObj x
              module y = IsoCommaObj y
              module f = IsoComma⇒ f
              MRSn = proj₂ (𝕚𝕄ℝ𝕊 n)
              MRSm = proj₂ (𝕚𝕄ℝ𝕊 m)
              module Vₙ = Functor MRSn
              module Vₘ = Functor MRSm
              module R  = Functor ℝ
          in let open ArrC.HomReasoning in record
            { f = f.f
            ; g = F-down.F₁ f.g
            ; commute = begin
                Vₘ.F₁ (F-down.F₁ f.g)
                  ArrC.∘ (down.⇐.η x.b ArrC.∘ ArrM._≅_.from x.iso)
                  ≈⟨ ArrC.sym-assoc
                       {f = ArrM._≅_.from x.iso}
                       {g = down.⇐.η x.b}
                       {h = Vₘ.F₁ (F-down.F₁ f.g)} ⟩
                (Vₘ.F₁ (F-down.F₁ f.g) ArrC.∘ down.⇐.η x.b)
                  ArrC.∘ ArrM._≅_.from x.iso
                  ≈⟨ ArrC.∘-resp-≈ˡ
                       (ArrC.Equiv.sym (down.⇐.commute f.g)) ⟩
                (down.⇐.η y.b ArrC.∘ Vₙ.F₁ f.g)
                  ArrC.∘ ArrM._≅_.from x.iso
                  ≈⟨ ArrC.assoc
                       {f = ArrM._≅_.from x.iso}
                       {g = Vₙ.F₁ f.g}
                       {h = down.⇐.η y.b} ⟩
                down.⇐.η y.b
                  ArrC.∘ (Vₙ.F₁ f.g ArrC.∘ ArrM._≅_.from x.iso)
                  ≈⟨ ArrC.∘-resp-≈ʳ f.commute ⟩
                down.⇐.η y.b
                  ArrC.∘ (ArrM._≅_.from y.iso ArrC.∘ R.F₁ f.f)
                  ≈⟨ ArrC.sym-assoc
                       {f = R.F₁ f.f}
                       {g = ArrM._≅_.from y.iso}
                       {h = down.⇐.η y.b} ⟩
                (down.⇐.η y.b ArrC.∘ ArrM._≅_.from y.iso)
                  ArrC.∘ R.F₁ f.f ∎
            }
        }
      ; identity = (refl , refl) , F-down.identity
      ; homomorphism = (refl , refl) , F-down.homomorphism
      ; F-resp-≈ = λ eq →
          ((eq .proj₁ .proj₁) , (eq .proj₁ .proj₂))
            , F-down.F-resp-≈ (proj₂ eq)
      }

    go-proj : NaturalIsomorphism (V (suc m) ∘F go)
      ((V m ∘F F-down) ∘F Π-MRS n)
    go-proj = niHelper (record
      { η = λ X → ArrC.id
      ; η⁻¹ = λ X → ArrC.id
      ; commute = λ f →
          let open ArrC.HomReasoning in
          begin
            ArrC.id ArrC.∘ Functor.F₁ (V (suc m) ∘F go) f
              ≈⟨ ArrC.identityˡ
                   {f = Functor.F₁ (V (suc m) ∘F go) f} ⟩
            Functor.F₁ ((V m ∘F F-down) ∘F Π-MRS n) f
              ≈˘⟨ ArrC.identityʳ
                    {f = Functor.F₁ ((V m ∘F F-down) ∘F Π-MRS n) f} ⟩
            Functor.F₁ ((V m ∘F F-down) ∘F Π-MRS n) f
              ArrC.∘ ArrC.id ∎
      ; iso = λ X → record
          { isoˡ = identityˡ , identity²
          ; isoʳ = identityˡ , identity²
          }
      })

    down-compat : NaturalIsomorphism (V (suc m) ∘F go) (V (suc n))
    down-compat = NI.trans go-proj ((proj₂ down) ⓘʳ Π-MRS n)

downF : ∀ {n m} → m ≤ n → Functor (𝕚𝕄ℝ𝕊ₒ n) (𝕚𝕄ℝ𝕊ₒ m)
downF p = proj₁ (𝕚𝕄ℝ𝕊-down p)

down-compat : ∀ {n m} (p : m ≤ n) →
  NaturalIsomorphism (V m ∘F downF p) (V n)
down-compat p = proj₂ (𝕚𝕄ℝ𝕊-down p)

private module ElMRS = Category τ'[iMR2]
private module 𝕋MRS = Category 𝕋MRS

-- lemma: the downward functor at level n is naturally ≃ to the
-- identity.
lemma-id : ∀ {n : ℕ} →
  NaturalIsomorphism (downF {n} {n} ≤-refl) (idF {C = 𝕚𝕄ℝ𝕊ₒ n})
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
  { η = λ X →
      let module X = IsoCommaObj X
          module ArrM = BaseMorphism Arr.Arrow
          MRSn = proj₂ (𝕚𝕄ℝ𝕊 n)
          module Vₙ = Functor MRSn
          down' = proj₂ (𝕚𝕄ℝ𝕊-down (≤-refl {n}))
          F-down' = proj₁ (𝕚𝕄ℝ𝕊-down (≤-refl {n}))
          module F-down' = Functor F-down'
          module down' = NaturalIsomorphism down'
      in record
        { f = ElMRS.id
        ; g = IH.⇒.η X.b
        ; commute = 
            let open ArrC.HomReasoning 
            in {! !}
        }
  ; η⁻¹ = λ X →
      let module X = IsoCommaObj X in record
        { f = ElMRS.id
        ; g = IH.⇐.η X.b
        ; commute = 
            let open ArrC.HomReasoning 
            in {! !}
        }
  ; commute = λ f →
      let module f = IsoComma⇒ f
      in (id-comm-sym τ'[iMR2] {f = f.f} , IH.⇒.commute f.g)
  ; iso = λ X →
      let module X = IsoCommaObj X
      in record
        { isoˡ =
            (ElMRS.identity² {X.a} , BaseMorphism.Iso.isoˡ (IH.iso X.b))
        ; isoʳ =
            (ElMRS.identity² {X.a} , BaseMorphism.Iso.isoʳ (IH.iso X.b))
        }
  })
  where
    module IH = NaturalIsomorphism (lemma-id {n})
    module Mn = Category (𝕚𝕄ℝ𝕊ₒ n)

-- lemma-homomorphism: 𝕚𝕄ℝ𝕊-down respects composition up to natural
-- isomorphism.
lemma-homomorphism : ∀ {n m k : ℕ} (m≤n : m ≤ n) (k≤m : k ≤ m) →
  NaturalIsomorphism (downF (≤-trans k≤m m≤n))
    ((downF k≤m) ∘F (downF m≤n))
lemma-homomorphism {n = n} z≤n z≤n = niHelper (record
  { η = λ X → M0.id
  ; η⁻¹ = λ X → M0.id
  ; commute = λ f →
      id-comm-sym (𝕚𝕄ℝ𝕊ₒ zero)
        {f = Functor.F₁ (reduce n) f}
  ; iso = λ X → record
      { isoˡ = M0.identity² {Functor.F₀ (reduce n) X}
      ; isoʳ = M0.identity² {Functor.F₀ (reduce n) X}
      }
  })
lemma-homomorphism (s≤s m≤n) z≤n = niHelper (record
  { η = λ X → {! !}
  ; η⁻¹ = λ X → {! !}
  ; commute = λ f → {! !}
  ; iso = λ X → {! !}
  })
lemma-homomorphism (s≤s m≤n) (s≤s k≤m) = niHelper (record
  { η = λ X → {! !}
  ; η⁻¹ = λ X → {! !}
  ; commute = λ f → {! !}
  ; iso = λ X → {! !}
  })

-- lemma-Fresp: proof-irrelevance for 𝕚𝕄ℝ𝕊-down on thin morphisms.
lemma-Fresp : ∀ {n m : ℕ} (p q : m ≤ n) →
  NaturalIsomorphism (downF p) (downF q)
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
  { η = λ X → {! !}
  ; η⁻¹ = λ X → {! !}
  ; commute = λ f → {! !}
  ; iso = λ X → {! !}
  })

-- iMRS-chain: the chain … → 𝕚𝕄ℝ𝕊ₒ 2 → 𝕚𝕄ℝ𝕊ₒ 1 → 𝕚𝕄ℝ𝕊ₒ 0 as ℕ^op → Cats.
iMRS-chain : Functor (Category.op pℕ) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
iMRS-chain = record
  { F₀ = 𝕚𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤n → downF m≤n
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
