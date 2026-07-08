# Categories.Rosen — (M,R)-systems in agda-categories

Work-in-progress documentation of the `Categories.Rosen` module hierarchy.

## Modules

### `Core.agda`
Core definitions for the category of (M,R)-systems.
- `Cod` — Codomain functor `Arrow(C) → C`.
- `nHom` — sends `f : A ⇒ B` to the induced natural transformation `[-,f] : [B,-] ⇒ [A,-]`.
- `nHom-identity` — `nHom` respects identity.
- `MR2` — an (M,R)-system according to Rosen: a pair `(f, ϕ)` where `f : A ⇒ B` and `ϕ : Cod ⇒ [A,-]∘Cod`.
- `MR2-Setoid` — `MR2` as a `Setoid`.
- `MRS-Profunctor` — the profunctor `C^op × C → Sets` sending `(A, B)` to `MR2 A B`.

### `Repairs.agda`
The "fibration of repairs": the category of elements of the functor `A ↦ Nat(Cod, [A,-]∘Cod)`.
- `rep₀` — objects: `(A, ϕ)` with `ϕ : Cod ⇒ [A,-]∘Cod`.
- `rep⇒` — morphisms: `u : X.A ⇒ Y.A` such that `(nHom u ∘ʳ Cod) ∘ᵥ Y.ϕ ≃ X.ϕ`.
- `repairs` — the total category of this fibration.

### `TotalCategory.agda`
The total category of the MRS-profunctor tabulator.
- `tot⇒` — morphisms in the total category.
- `total` — the total category, equivalent to the tabulator of `MRS-Profunctor`.

### `HigherMRS.agda`
Higher-order (M,R)-systems in a Fibonacci-style construction: each step
`A → B → [A,B] → [B,[A,B]] → ...` embeds the two previous levels into an
internal hom. Built as iterated IsoCommas of ℝ and Vᵢ.
- `MRS3` — the 3rd level: `IsoComma ℝ V₁`.
- `𝕄ℝ𝕊` — the n-th level category + functor to `Arr.Arrow`.
- `𝕄ℝ𝕊ₒ` / `𝕄ℝ𝕊ₐ` — projections to the category / functor.
- `Π-MRS` — projection `(suc n) → n`.
- `pℕ` — ℕ as a poset category.
- `𝕄ℝ𝕊-down` — functors from higher to lower levels.
- `MRS-chain` — a chain `⋯ → 2 → 1 → 0` as a functor `ℕ^op → Cats`.
- `MRS∞` — the limit of the chain (the "∞-level" MRS category).

### `Tabulator.agda`
Tabulator of `MRS-Profunctor`: a canonical category `𝕋MRS` attached to the
profunctor `MRS-Profunctor : C^op × C → Sets`, equipped with a universal 2-cell.
- `𝕋MRS` — the tabulator category of `MRS-Profunctor`.
- `π` — left projection `𝕋MRS → C`.
- `þ` — the universal terminal 2-cell.
- `V₁` — extracts the "f" component from each `MR2` object.
- `ϵ` — natural transformation from `MRS-Profunctor` to the lifted hom functor.

### `FibreA.agda`
Fibre-at-A construction: an alternative approach to higher (M,R)-systems by fixing
the domain object `A`, which simplifies the definitions.
- `totalAtA₀` / `totalAtA₁` — objects and morphisms of the fibre over `A`.
- `totalAtA` — the category totalAtA A (fibre over `A` of `MRS-Profunctor`).
- `∇` — functor from the fibre to `Arrow`, sending `(B, ξ)` to `ϕ : B → [A,B]`.
- `commaNablaV` — comma category `∇ ↓ V₁` (weaker invariant, historical).

### `Algebras.agda`
Incoherent (M,R)-systems as endofunctor algebras.  The endofunctor is
`X ↦ A ⊗ (𝟙 + X)` (conceptually; implemented via distributivity as `A + (A ⊗ X)`).
Provides an explicit equivalence between the fibre category `iMR2ᴿ A` and the
category of algebras for the endofunctor `X ↦ A + (A ⊗ X)`.
- `_⊗[I+_]` — endofunctor `X ↦ A + (A ⊗ X)` (representing `A ⊗ (𝟙 + X)` when ⊗ distributes).
- `F-Algebra-Category` — category of algebras for `_⊗[I+_]`.
- `to` / `from` — comparison functors between `iMR2ᴿ A` and `F-Algebra-Category {A}`.
- `AlgA≣MRS^A` — `StrongEquivalence (iMR2ᴿ A) (F-Algebra-Category {A})`.

### `TabEquivalence.agda`
Equivalence between the total category (see `TotalCategory.agda`) and the
tabulator of `MRS-Profunctor` (see `Tabulator.agda`).
- `Eq` / `Eq⁻¹` — inverse functors (identity on objects) establishing the equivalence.
- `Eq⊣Eq⁻¹` — the adjoint equivalence.

### `Incoherent/Core.agda`
Incoherent (M,R)-systems: a simpler variant where `ϕ : B ⇒ [A,B]` is just a
morphism (not a natural transformation).
- `iMR2` — an incoherent (M,R)-system: `(f : A ⇒ B, ϕ : B ⇒ [A,B])`.
- `iMR2₀` / `iMR2⇒` — objects and morphisms of the total category.
- `τ[iMR2]` — total category of incoherent (M,R)-systems.

### `Incoherent/Fibred.agda`
Fibred incoherent (M,R)-systems: the fibre over a fixed domain A.
Reindexing along `u : A ⇒ A'` is functorial (contravariant) in A.
- `iMR2ᴿ₀` / `iMR2ᴿ⇒` — objects and morphisms of the fibre over A.
- `iMR2ᴿ A` — the fibre category over A.
- `MRSreindex u` — reindexing functor `iMR2ᴿ A' → iMR2ᴿ A`.

### `Incoherent/Displayed.agda`
Displayed incoherent (M,R)-systems: the fibre over a fixed codomain B.
Reindexing along `v : B ⇒ B'` is *pro*functorial in B (hence a displayed category).
- `iMR2ᴸ₀` / `iMR2ᴸ⇒` — objects and morphisms of the left-fibre over B.
- `iMR2ᴸ B` — the left-fibre category over B.
- `MRSdisplay v` — bifunctor `(iMR2ᴸ B)^op × iMR2ᴸ B' → Setoids`.

### `Adjunction/TotRep.agda`
Import module tying together `Core` and `Repairs` (no new definitions).

### `Cartesian/Sets.agda`
The category of Sets as a Cartesian closed monoidal category,
used to instantiate the Rosen constructions concretely.

### `Cartesian/Concrete.agda`
Generic instance: all Rosen modules instantiated for Sets,
serving as a type-checking test.

### `Cartesian/Adjoints.agda`
Instances of the Rosen constructions for the Cartesian (Sets) case.
In this setting, V₁ and U₁ acquire left adjoints.
- `const-ϕ` — the unique natural transformation `Cod ⇒ [A,-]∘Cod` in Sets.
- `yoneda-argument` — `Nat(Cod, [A,-]∘Cod)` is a singleton.
- `unique-ϕ` — every such ϕ equals `const-ϕ A`.
- `L` / `L⊣V₁` — left adjoint to V₁.
- `L'` / `L'⊣U₁` — left adjoint to U₁.

### `ProElements.agda`
Modified category of elements for a bifunctor `F : C^op × C → Sets`, specialised to `MRS-Profunctor`.
- `EltsCat` — generic (modified) category-of-elements construction.
- `ElMRS` — the category of elements of `MRS-Profunctor`.
- `ℝ` — functor from `ElMRS` to `Arrow(C)` extracting repair maps.
- `U₁` — functor from `ElMRS` to the twisted arrow category of `C`.
