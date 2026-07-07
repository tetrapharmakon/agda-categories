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

### `ProElements.agda`
Modified category of elements for a bifunctor `F : C^op × C → Sets`, specialised to `MRS-Profunctor`.
- `EltsCat` — generic (modified) category-of-elements construction.
- `ElMRS` — the category of elements of `MRS-Profunctor`.
- `ℝ` — functor from `ElMRS` to `Arrow(C)` extracting repair maps.
- `U₁` — functor from `ElMRS` to the twisted arrow category of `C`.
