# Categories.Rosen — (M,R)-systems in agda-categories

Work-in-progress documentation of the `Categories.Rosen` module hierarchy.

As of this revision, `Incoherent/Slice.agda`'s equivalence between the fibre
category `iMR2ᴸ B` and the slice category `Slice C (B × [B,B]₀)` (`AlgA≣MRS-B`)
is fully proved: all six interaction holes it previously carried have been
closed, the last one requiring the `Closed` module's mate square to establish
naturality of the curry/braid transpose across a change of exponent.
Completing that file was the occasion for auditing and documenting the rest
of the tree below.

**A number of other files in the tree carry gaps that are recorded
mathematical obstructions, not unfinished routine proofs.** Every one of them
is now postulated under a name beginning `UNSOUND-`, next to a comment
explaining the obstruction, so that

    grep -rn UNSOUND src/Categories/Rosen/

enumerates the whole debt, typed. **A statement postulated as `UNSOUND-*` is
one this development knows to be FALSE**; nothing depending on one is verified,
and none of them may be cited as a result. There are five, in four files
(`Coherent/NaturalAndHom.agda`, `Incoherent/CartesianAdjoints.agda`,
`Incoherent/IteratedTruncatedSimplicialObject.agda`, `Variants/Slice.agda`,
`Variants/Profunctorial.agda`).

The tree's only other `postulate` is function extensionality, which is an
ordinary axiom and lives alone in `Axioms.agda`.

**A green `make check` is therefore not evidence that a statement is proved.**
`sorry`/`UNSOUND-*` postulates typecheck by construction, and
`Coherent/HigherTruncatedSimplicialObject.agda` passes only because it sets
`--allow-unsolved-metas`. Read the **Status:** line of a file before relying on
anything in it.

## A note on the projection functors

Six functors project an (M,R)-system onto one edge of its defining diagram
`A → B → [A,B]`, three in each world, and the notation says which is which:

|  | picks out | source | target | name |
|---|---|---|---|---|
| incoherent | `f` | total `τ[iMR2]` | `Arrow(C)` | `[_]f` |
| incoherent | `f` | twisted elements | `Tw(C)`    | `⟅_⟆f` |
| incoherent | `Φ` | twisted elements | `Arrow(C)` | `⟅_⟆Φ` |
| coherent   | `f` | tabulator `𝕋MRS` | `Arrow(C)` | `[_]f` |
| coherent   | `f` | `ElMRS`          | `Tw(C)`    | `⟅_⟆f` |
| coherent   | `Φ` | `ElMRS`          | `Arrow(C)` | `⟅_⟆Φ` |

**Square brackets for a functor out of a total category, bags for one out of
twisted elements.**  This is the paper's own convention: `\atF`/`\atPhi` render
as `[-]_f`/`[-]_Φ` and `\lbag-\rbag_f`/`\lbag-\rbag_Φ` as the bags.

## Coherent (M,R)-systems

The core coherent definitions live in the `Coherent/` subdirectory. It also
contains `Coherent/C2Sets.agda`, a fully self-contained companion that builds
the category of C₂-sets concretely in order to exhibit a real counterexample
to a claim the core files merely state to be unprovable (see the
`Coherent/NaturalAndHom.agda` and `Coherent/C2Sets.agda` sections below).

### id-coherent vs cod-coherent: which core to use

Two cores coexist while the tree migrates from one notion to the other.

- **`Coherent/IdCore.agda`** — the id-coherent (M,R)-system, `Φ : id ⇒ [A,-]`,
  with a component at every *object*.  **This is the notion the paper settles
  on, and the one new work should use.**
- **`Coherent/CodCore.agda`** — the cod-coherent one, `Φ : Cod ⇒ [A,-]∘Cod`,
  with a component at every *arrow*.  Historically first, which is the only
  reason it used to be called `Core`; nothing depends on it now except the
  bridge.
- **`Coherent/CodCoherentEqualIdCoherent.agda`** — the proof that the two agree.
  This is the paper's `cod_lax_epi`.

The two are equivalent but not by definition: naturality over `Arr(C)` is
id-naturality *plus* the condition that `Φ`'s component depends only on the
codomain (`Φ-const-on-slices`).  A proof that used a naturality square of
`Arr(C)` outside that shape therefore has no id-world translation and has to be
re-derived; the bridge guarantees the *statements* correspond, not the proofs.

**The whole tree is on `IdCore`.**  `Coherent/CodCore.agda` is reached only by
the bridge module, which needs both sides in order to state that they agree.

`IdCore`'s setoid relation is wrapped in `Level.Lift`.  That is Agda universe
bookkeeping with no mathematical content — see the long comment at the top of
that file — and exists only because the upstream tabulator pins its profunctor's
levels.

### `Coherent/CodCore.agda`
Core definitions for the category of (M,R)-systems.
- `Cod` — Codomain functor `Arrow(C) → C`.
- `nHom` — sends `f : A ⇒ B` to the induced natural transformation `[-,f] : [B,-] ⇒ [A,-]`.
- `nHom-identity` — `nHom` respects identity.
- `MR2` — an (M,R)-system according to Rosen: a pair `(f, Φ)` where `f : A ⇒ B` and `Φ : Cod ⇒ [A,-]∘Cod`.
- `MR2-Setoid` — `MR2` as a `Setoid`.
- `MRS-Profunctor` — the profunctor `C^op × C → Sets` sending `(A, B)` to `MR2 A B`.

### `Coherent/NaturalAndHom.agda`
Proves that natural transformations `id ⇒ [A,-]` correspond to morphisms
`A ⇒ unit` in one direction, and explains in detail why the converse fails.
- `p` — sends `α : NaturalTransformation id [A,-]` to its component at `unit`, transposed: `A ⇒ unit`.
- `ι` — the converse direction, currying a map `A ⇒ unit` back into a natural transformation.
- `lem` — `p (ι α) ≈ α`, proved by an explicit equational chain using the closed/symmetric-monoidal unitor coherence.
- `UNSOUND-ι∘p≈id` — the statement that `ι (p α) ≈ α` pointwise, which is **not**
  provable in general, and is in fact **refuted** by `Coherent/C2Sets.agda`.
  Postulated, unused, to record the shape of the failure.

**Status:** compiles. `UNSOUND-ι∘p≈id` (formerly `false`) marks a genuine
counterexample, not a missing proof. The comment above it gives the
actual counterexample: in the cartesian closed category of C₂-sets with
`A = unit`, the nontrivial central element of C₂ is a natural endomorphism
of the identity that acts as the identity on the terminal object but swaps
the regular C₂-set — so `p` genuinely discards information that `ι` cannot
reconstruct. A natural transformation `id ⇒ [A,-]` is *not* determined by
its component at the unit without an extra density/generator hypothesis.

### `Coherent/C2Sets.agda`
Self-contained module (no parameters) that makes the `NaturalAndHom` claim
*concrete*: it builds the category of C₂-sets — functors `C2 → Sets`, where
`C2` is the one-object category whose endomorphisms are the two elements of
the cyclic group of order two, composed by xor — and exhibits it as Cartesian
closed in the canonical style (explicit pointwise product `_C×_`, terminal
`C⊤`, internal hom `_C^_` with the conjugation action, evaluation and
currying), then *deduces* its `Monoidal`/`Closed` structure from that, exactly
as `Cartesian/Sets.agda` does for Sets.
- `C2` / `C2Sets` — the two-element group as a category, and its category of (C₂-)sets.
- `C2Sets-CCC` / `C2Sets-Monoidal` / `C2Sets-Closed` — the Cartesian-closed, hence monoidal-closed, structures.
- `actBy b` — the natural endomorphism of the identity sending `x` to `b · x`; `swap = actBy true`, the action of the nontrivial element.
- `Creg` — the regular C₂-set, where the nontrivial action has no fixed points; this is what distinguishes `swap` from the identity.
- `swap-is-counterexample` — `¬ (∀ X → η(ι (p swap)) X ≈ η swap X)`: the concrete proof that the reverse direction of `lem` fails for C₂-sets, via the chain `p-swap≈id`, `collapse`.

**Status:** complete, no holes. The only thing left as a remarked-out sketch is
`ι-id≈actBy-false`, an interesting fact in its own right that the final proof
turned out not to need (it does not close by `refl` because `[unit,-].F₀` is
built through `Functor.Construction.Constant` rather than reducing to the
constant embedding).

### `Coherent/Repairs.agda`
The "fibration of repairs": the category of elements of the functor `A ↦ Nat(Cod, [A,-]∘Cod)`.
- `rep₀` — objects: `(A, Φ)` with `Φ : Cod ⇒ [A,-]∘Cod`.
- `rep⇒` — morphisms: `u : X.A ⇒ Y.A` such that `(nHom u ∘ʳ Cod) ∘ᵥ Y.Φ ≃ X.Φ`.
- `repairs` — the total category of this fibration.

### `Coherent/TotalCategory.agda`
The total category of the MRS-profunctor tabulator.
- `tot⇒` — morphisms in the total category.
- `total` — the total category, equivalent to the tabulator of `MRS-Profunctor`.

### `Coherent/HigherMRS.agda`
Higher-order (M,R)-systems in a Fibonacci-style construction: each step
`A → B → [A,B] → [B,[A,B]] → ...` embeds the two previous levels into an
internal hom. Built as iterated IsoCommas of `⟅_⟆Φ` and `[_]f`.
- `MRS3` — the 3rd level: `IsoComma ⟅_⟆Φ [_]f`.
- `𝕄ℝ𝕊` — the n-th level category + functor to `Arr.Arrow`.
- `𝕄ℝ𝕊ₒ` / `𝕄ℝ𝕊ₐ` — projections to the category / functor.
- `Π-MRS` — projection `(suc n) → n`.
- `pℕ` — ℕ as a poset category.
- `𝕄ℝ𝕊-down` — functors from higher to lower levels.
- `MRS-chain` — a chain `⋯ → 2 → 1 → 0` as a functor `ℕ^op → Cats`.
- `MRS∞` — the limit of the chain (the "∞-level" MRS category).

### `Coherent/HigherTruncatedSimplicialObject.agda`
Intended as the coherent counterpart of
`Incoherent/IteratedTruncatedSimplicialObject.agda` below, assembling
`Coherent/HigherMRS.agda`'s `MRS3`/`𝕋MRS` into a `TruncatedSimplicialObject`.
- `MRS-defines-truncated-simplicial-object` — the target record; every one of its 21 fields is currently an open `{! !}`.

**Status: unfinished, not a documented obstruction.** This is the one file in
the tree that sets `--allow-unsolved-metas`, which is what lets it compile at
all with 21 unfilled interaction holes. A large commented-out block at the
end of the file (the old incoherent attempt, itself carrying two genuine
`sorry`s) is kept as a reference sketch, but none of it has been ported to
the coherent setting yet. Contrast with the `sorry`s elsewhere in the tree,
which mark proven impossibilities rather than pending work.

### `Coherent/Tabulator.agda`
Tabulator of `MRS-Profunctor`: a canonical category `𝕋MRS` attached to the
profunctor `MRS-Profunctor : C^op × C → Sets`, equipped with a universal 2-cell.
- `𝕋MRS` — the tabulator category of `MRS-Profunctor`.
- `π` — left projection `𝕋MRS → C`.
- `þ` — the universal terminal 2-cell.
- `[_]f` — the **first edge functor**: extracts the process map `f` from a coherent (M,R)-system.  This is the paper's `[-]_f` (`\atF`, `definition_first_edge_functor`) --- the process selector that `def_atF` wants and cannot have incoherently, available here because the tabulator resolves the variance.
- `ϵ` — natural transformation from `MRS-Profunctor` to the lifted hom functor.

### `Coherent/FibreA.agda`
Fibre-at-A construction: an alternative approach to higher (M,R)-systems by fixing
the domain object `A`, which simplifies the definitions.
- `totalAtA₀` / `totalAtA₁` — objects and morphisms of the fibre over `A`.
- `totalAtA` — the category totalAtA A (fibre over `A` of `MRS-Profunctor`).
- `∇` — functor from the fibre to `Arrow`, sending `(B, ξ)` to `Φ : B → [A,B]`.
- `commaNablaV` — comma category `∇ ↓ [_]f` (weaker invariant, historical).

### `Coherent/TabEquivalence.agda`
Equivalence between the total category (see `TotalCategory.agda`) and the
tabulator of `MRS-Profunctor` (see `Tabulator.agda`).
- `Eq` / `Eq⁻¹` — inverse functors (identity on objects) establishing the equivalence.
- `Eq⊣Eq⁻¹` — the adjoint equivalence.

### `Coherent/ProElements.agda`
Modified category of elements for a bifunctor `F : C^op × C → Sets`, specialised to `MRS-Profunctor`.
- `EltsCat` — generic (modified) category-of-elements construction.
- `ElMRS` — the category of elements of `MRS-Profunctor`.
- `⟅_⟆Φ` — the **last edge functor**: extracts the repair component `Φ_B : B ⇒ [A,B]` from a coherent (M,R)-system, without fixing the domain.  This is the paper's `⦇-⦈_Φ` (`definition_last_edge_functor`).  Note the asymmetry with `⟅_⟆f`: the process map is already functorial on the tabulator, the repair map only after passing to twisted elements.
- `⟅_⟆f` — the left leg of the twisted-elements span (see the table above).

## Incoherent (M,R)-systems

A simpler variant where `Φ : B ⇒ [A,B]` is just a morphism, not a natural
transformation. This is the actively-developed part of the tree; several
files here document, rather than paper over, the places where dropping
naturality genuinely breaks a coherent-world construction.

### `Incoherent/Algebras.agda`
Characterizes the fibre of incoherent (M,R)-systems over a fixed domain
object `A` as a category of algebras. It assumes only closed structure and
binary coproducts (no symmetry of `⊗` is used anywhere — the transpositions
between `Φ` and its curried form `Φ#` use only the closed structure).
- `_⊗[_+I]` — the endofunctor `X ↦ A + (X ⊗ A)` on `C`.
- `F-Algebra-Category` — the category of algebras for that endofunctor.
- `to` — `iMR2ᴿ A → Alg(A + -⊗A)`: sends `(B, f, Φ)` to the algebra with structure map `[f, Φ#]`, where `Φ# = Radjunct Φ : B⊗A ⇒ B`.
- `from` — `Alg(A + -⊗A) → iMR2ᴿ A`: given an algebra `α : A + (B⊗A) ⇒ B`, sets `f = α ∘ i₁` and `Φ = Ladjunct (α ∘ i₂)`.
- `AlgA≣MRS^A` — the full `StrongEquivalence (iMR2ᴿ A) (F-Algebra-Category A)`, with constructive round-trip proofs.

**Status:** complete, no holes. This complements `Incoherent/Slice.agda`
(the `B`-fibre is a slice) by giving the dual/algebraic description of the
`A`-fibre.

### `Incoherent/Core.agda`
Incoherent (M,R)-systems: a simpler variant where `Φ : B ⇒ [A,B]` is just a
morphism (not a natural transformation).
- `iMR2` — an incoherent (M,R)-system: `(f : A ⇒ B, Φ : B ⇒ [A,B])`.
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

### `Incoherent/Slice.agda`
Establishes a strong equivalence between the fibre category `iMR2ᴸ B`
(incoherent (M,R)-systems with fixed codomain B) and the slice category
`Slice C (B × [B,B]₀)`. The pairing `⟨f, Φ⟩ : A ⇒ B × [B,B]₀` bundles the
process map and the curried repair map into a single slice arrow, using the
closed monoidal structure and symmetry (braiding) to swap between the two
curried forms of Φ.
- `slice B` — the slice category `Slice C (B × [B,B]₀)`.
- `to` / `from` — the comparison functors `iMR2ᴸ B → slice B` and back.
- `To.q-comm`, `To.cowedge` — naturality lemmas for the `to` direction, built from the `Closed` module's mate square.
- `AlgA≣MRS-B` — `StrongEquivalence (iMR2ᴸ B) (slice B)`.

**Status:** complete, no holes. All six `{! !}` interaction holes (in `from`'s
`F₁.eqΦ`, and the `F∘G≈id`/`G∘F≈id` naturality/round-trip obligations) have
been closed. The two commute-square holes reduced to `id ∘ h ≈ h ∘ id`; the
round-trip `eqΦ` obligations reduce to `swap_from ∘ swap_to ≈ id` via
`RLadjunct≈id`/`LRadjunct≈id` and the braiding involution; the hardest hole
(naturality of `swap_from` in the exponent) required invoking the `Closed`
module's mate square (`mate.commute₁`) because the exponent object changes
between the two adjunction instances involved. (Note: `Variants/Slice.agda`,
described below, is an unrelated, unfinished construction that happens to
share a filename — it slices the *domain* of Φ rather than exhibiting this
`iMR2ᴸ B ≃ Slice` equivalence.)

### `Incoherent/Repairs.agda`
The incoherent analogue of `Coherent/Repairs.agda`: the fibration of repair
data `Φ : B ⇒ [A,B]` without any naturality condition.
- `irep₀` — an object `A`, `B`, and `Φ : B ⇒ [A,B]₀`.
- `irep⇒` — morphisms `(u,v)` with `[u,id]₁ ∘ Y.Φ ∘ v ≈ [id,v]₁ ∘ X.Φ`.
- `irepairs` — the total category (used as the codomain of `[_]Φ` in `Functors.agda`).

### `Incoherent/Elements.agda`
The (twisted) category of elements of the incoherent total category, dual in
variance to `iMR2⇒`: morphisms twist the `A`-component contravariantly
against the `B`-component, matching the shape of the twisted-arrow category.
- `twiMR2⇒` — twisted morphisms `(l : Y.A ⇒ X.A, r : X.B ⇒ Y.B)` with `eqf`/`eqΦ` compatibility.
- `τ'[iMR2]` — the twisted total category.
- `⟅_⟆f` — functor `τ'[iMR2] → TwistedArrow` remembering only `f`.
- `⟅_⟆Φ` — functor `τ'[iMR2] → Arrow` remembering only `Φ` (used to build `iMRS3` in `Incoherent/HigherMRS.agda`).

### `Incoherent/Functors.agda`
Collects the basic projection functors out of `τ[iMR2]` (and, via Arbib's
construction, the comparison with Mealy automata).
- `[_]A` / `[_]B` — projections `τ[iMR2] → C` onto the domain/codomain.
- `[_]f` — projection `τ[iMR2] → Arrow(C)` onto the process map `f`.
- `[_]Φ` — projection `τ[iMR2] → irepairs` onto the repair map `Φ`.
- `lemma-epsilon` / `lemma-delta` — the two compatibility squares (output and transition) needed to interpret a twisted MR-morphism as a morphism of Mealy automata; both live in a shared module parameterized by an MR-morphism `f : twiMR2⇒ X Y`.
- `Arbib` — functor `τ'[iMR2] → twMealy` sending an incoherent (M,R)-system to the Mealy automaton with state object `[A,B]`, transition `d` and output `s` built from the adjunction unit/counit (the construction attributed to Arbib in the file's comment).

### `Incoherent/Mealy.agda`
The twisted category of Mealy automata internal to `C`, used as the target of
the `Arbib` functor in `Functors.agda`.
- `Mealy A B` — a Mealy automaton: state object `E`, transition `d : E⊗A ⇒ E`, output `s : E⊗A ⇒ B`.
- `Mealy₀` / `Mealy⇒` — objects and morphisms (a state map `u` intertwining `d`/`s` up to reindexing by `l`,`r`).
- `Mealy⇒-≈` — equality of automaton morphisms, componentwise from the morphism record.
- `twMealy` — the *twisted* category of Mealy automata: morphisms act
  contravariantly on inputs and covariantly on outputs.  This is deliberately
  not the total category usually recorded in the literature; it is the paper's
  `𝜏Mly` (`definition_twisted_category_mealy_automata`), and it is the right
  target for `Arbib`, whose source `τ'[iMR2]` twists the same way.  It was
  called `totalMealy` while the mismatch with the literature was being read as
  a defect.

### `Incoherent/HigherMRS.agda`
The incoherent counterpart of `Coherent/HigherMRS.agda`: builds the tower of
higher incoherent (M,R)-systems via iterated `IsoComma` and takes its limit.
- `iMRS3` — 3rd level, `IsoComma ⟅_⟆Φ [_]f`.
- `𝕚𝕄ℝ𝕊` / `𝕚𝕄ℝ𝕊ₒ` — the n-th level category paired with (resp. projected from) its functor to `Arrow(C)`.
- `Π-MRS` — projection `(suc n) → n`.
- `pℕ` — ℕ as a thin poset category, built via a hand-rolled `_≤′_`/`_≈′_`/`_≤2_` development proving `≤′`-proofs are contractible (generic order-theory scaffolding, not specific to MR-systems, but needed to index the tower).
- `𝕚𝕄ℝ𝕊-F` / `𝕚𝕄ℝ𝕊-η` — downward functors between levels and their compatibility with `V`.
- `iMRS-chain` — the chain `⋯ → 2 → 1 → 0` as a functor `ℕ^op → Cats`.
- `iMRS∞` / `iMRS∞-proj` / `iMRS∞-commute` — the limit of the chain and its universal property.

**Status:** complete, no holes.

### `Incoherent/Iterated.agda`
An alternative, simpler encoding of the "two composable incoherent
MR-systems" span, avoiding the `IsoComma` machinery of `HigherMRS.agda` in
favour of a direct record with a compatibility field `hᵣ≈kₗ`.
- `iMRSᴵᴵ₀` / `iMRSᴵᴵ⇒` — a pair of composable `iMR2`s (`hor`, `vert`) sharing the middle object, and morphisms of such pairs.
- `iMRSᴵᴵ` — the resulting category.
- `deg₀²` / `deg₂²` — the two face functors extracting the horizontal/vertical `iMR2`.
- `comp` — the face functor computing the actual composite `iMR2` (with the `eqΦ` square proved via the bifunctor interchange and the shared-boundary hypothesis `hᵣ≈kₗ`).

### `Incoherent/IteratedTruncatedSimplicialObject.agda`
Assembles `Core`/`Iterated`/`Functors` (instantiated at `Sets`) into a
`TruncatedSimplicialObject` and documents, in detail, where the construction
genuinely breaks down for *incoherent* MR-systems.
- `ιMR2` / `⊤MR2` — the two candidate degeneracy points `iMR2 A A` (identity) and `iMR2 A ⊤`.
- `s₀⁰`, `s₀¹`, `s₁¹` — the three degeneracy functors of the truncated simplicial object.
- `iMRSᴵᴵ-defines-truncated-simplicial-object` — the resulting `TruncatedSimplicialObject (Cats ...)`.

**Status:** compiles, but `d₁²-s₀¹` (forward and inverse directions) rests on
the postulate `UNSOUND-Φ-is-constant`, marking a genuine mathematical
obstruction, not missing routine work. Note that the paper claims only a
*semi*simplicial structure (faces, no degeneracies); the record built here is a
full `TruncatedSimplicialObject`, and the surplus is exactly what is unproved. The file's own comment proves this explicitly:
choosing `⊤MR2` as the degeneracy point forces `⊤ ≅ A` for every set `A`
(absurd); choosing `ιMR2` instead makes the simplicial identity
`d₁² ∘ s₀¹ ≈ id` require every incoherent repair map `Φ : B → (A → B)` to be
the constant map `(b,a) ↦ b`, which is false for a generic `Φ`. The file
concludes that the identity "requires either coherent MR2 systems, a
restriction to normalized Φ, or a weaker notion of morphism that forgets
Φ-compatibility" — i.e. this is a recorded impossibility result, not
unfinished work.

### `Incoherent/CartesianAdjoints.agda`
Attempts to exhibit left adjoints to `[_]f`/`⟅_⟆f`, instantiated at `Sets`.
(The coherent counterpart, a former `Cartesian/Adjoints.agda`, has been removed:
see the note under `Cartesian/WellPointed.agda` below.)
- `const-Φ` — the constant repair map `B → (A → B)`, `const-Φ A a b = a`.
- `L` / `L'` — the incoherent counterparts of the coherent left adjoints, equipping an arrow with the constant repair map.
- `L⊣A`, `L′⊣⟅⟆f` — the claimed adjunctions. **These assert the opposite of what
  the paper asserts**: §3 of "The Rosen fibration" labels the corresponding
  diagram `not_adjoints` and says in so many words that `L` and `L′` "fall just
  short of satisfying the adjunction property". They must not be cited.

**Status:** compiles, but both counits rest on the postulate
`UNSOUND-Φ-is-constant`, marking a documented genuine obstruction: in the
coherent construction, Φ's naturality plus a
Yoneda argument forces it to *be* the constant map uniquely; an `iMR2` stores
no naturality data, so that argument is simply unavailable, and the
counit's `eqΦ` field would require an *arbitrary* `Φ : B → (A → B)` to
satisfy `Φ b a ≡ b`, which is false in general. Proving these adjunctions
for real would require restricting the objects considered or reinstating
the coherent naturality condition.

## `MetabolicClosure.agda`

New module formalizing "closure points" of an (M,R)-system: generalized
elements `b₀ : unit ⇒ B` at which the (uncurried) repair map recovers the
original process `f`.
- `MetabolicClosure ξ` — a closure point `b₀` with `Φη₀ ξ ∘ b₀ ≈ Ladjunct (f ξ ∘ unitorˡ.from)`.
- `fact` — the equivalent "uncurried" form of the closure condition.
- `UnivClosurePoint ξ` — a stronger, `A`-indexed notion of closure point depending only on the repair family.
- `Univ⇒Metabolic` — every universal closure point is metabolic.
- `reindexMR2` — reindexing a coherent `MR2` system along `u : A' ⇒ A`, `v : B ⇒ B'`.
- `ReindexingPreservesClosure` — the (intended) statement that reindexing sends `b₀` to `v ∘ b₀`.

**Status:** complete, no holes, no postulates. The interaction hole that used
to sit in the final step of `ReindexingPreservesClosure` was closed.

## Variants (experimental)

> A former `Functorial/` subdirectory (a would-be `U`-parametric variant that
> diverged from `Coherent/` and relied on an escape-hatch
> `postulate irrelevance`) was removed from the tree; the same idea is
> developed cleanly by `Variants/Functorial.agda` below.

Four independent explorations of ways to generalize where Φ's naturality
data lives, kept side by side for comparison. All four type-check; two of them
(`Slice`, `Profunctorial`) do so only because their missing pieces are
postulated as `UNSOUND-*`, so read their **Status:** lines before using them.

### `Variants/Functorial.agda`
Generalizes `Cod : Arrow(C) → C` to an arbitrary functor `U : E → C` (the
module is parameterized by `U`), redefining `MR2 A B` with
`Φ : NaturalTransformation U ([A,-] ∘F U)` in place of `Cod`.
- `nHom`, `nHom-identity` — as in `Coherent/CodCore.agda`, but stated once and reused.
- `MR2`, `MR2-Setoid` — the `U`-parametric (M,R)-system.
- `MRS-Profunctor` — the full profunctor structure `C^op × C → Setoids`, proved completely (identity, homomorphism and `F-resp-≈` all filled in, by the same argument that works for `Cod`).

**Status:** complete, no holes, no postulates. This is the road-tested
version of the `U`-parametric idea that the former `Functorial/` subdirectory
also attempted; unlike that effort it carries no extra existential-witness
field and needs no escape-hatch postulate.

### `Variants/FullyPoly.agda`
An experimental "fully polymorphic" variant of `MR2` where Φ is natural in
*both* variables of the arrow category simultaneously (naturality stated
over `Arrow(C) × Arrow(C)` rather than just `Arrow(C)`), together with an
extensive catalogue of the naturality squares this induces.
- `MR2`, `MR2-Setoid` — the fully-polymorphic (M,R)-system and its setoid of equality.
- `Naturalities` — a module deriving 14 named naturality consequences (`nat-1⇒uᴿ`, `nat-u⇒1ᴸ`, the "cross naturalities" `nat-1⇒u×u⇒1` etc.) from the two-variable naturality of Φ.
- `MRS-Profunctor` — the attempted profunctor structure on `MR2`.

**Status:** complete, no holes, no postulates. The `homomorphism` hole was
closed and the dead `private postulate sorry` (declared, never invoked) was
removed.

### `Variants/Profunctorial.agda`
The most speculative variant: replaces the fixed `[A,-] ∘F Cod`-shaped
target of Φ with an arbitrary chosen profunctor
`p : Bifunctor (coSlice A)^op (Slice B) Setoids`, so an (M,R)-system carries
its own bespoke notion of naturality rather than reusing one fixed shape.
- `conjoint[_,-]` — the "conjoint" bifunctor `Hom(Cod(-), [A,-](Dom(-)))` used as the universal target for Φ.
- `MR2` — the profunctorial (M,R)-system, `⟪ f , p , Φ ⟫`.
- `MR2-Setoid` — equality up to `f ≈ g` and a natural isomorphism between the chosen profunctors `p ≅ q` compatible with Φ.
- `pollo` — the reindexing functor on `(coSlice A)^op × Slice B` induced by `u : A' ⇒ A`, `v : B ⇒ B'`.
- `MRS-Profunctor` — the attempted profunctor structure (essentially entirely unfilled).

**Status:** type-checks, but `MRS-Profunctor` rests on three postulates —
`UNSOUND-reindex-p`, `UNSOUND-reindex-Φ`, `UNSOUND-reindex-twist`. `MR2-Setoid`
really is proved to be a setoid, and every component of `MRS-Profunctor` not
mentioning the reindexed profunctor is proved outright. The obstruction is
precise: reindexing along `(u : A′ ⇒ A, v : B ⇒ B′)` needs `coSlice A′ →
coSlice A` and `Slice B′ → Slice B`, i.e. pushout along `u` and pullback along
`v`, which this module does not assume (`pollo` assembles the functors that run
the other way). This is what §4's `proposition_assignment_profunctor_r` asserts
without proof.

### `Variants/Slice.agda`
A slice-category-flavoured take on the same "fully polymorphic Φ" idea as
`FullyPoly.agda`, but phrased via `Categories.Category.Slice` rather than
raw arrow-pairs; a large commented-out block sketches an intended
`nHom`-based `MRS-Profunctor` construction mirroring `Coherent/CodCore.agda`'s,
ported to this setting.
- `MR2` — `⟪ f , Φ ⟫` with `Φ : NaturalTransformation (Dom B) ([A,-] ∘F Dom B)`.
- `MR2-Setoid` — equality up to `f ≈ g` and `Φ ≃ Φ'`.
- `MRS-Profunctor` — the attempted profunctor structure; only `F₀` and part of `F₁.cong` are filled in.

**Status:** type-checks, but `MRS-Profunctor` rests on the postulate
`UNSOUND-reindex-Φ`. The comment above it states flatly that **there is no
profunctor** `C.op × C → Sets` sending `(A , B) ↦ MR2 A B`, so the bifunctor
declared there does not exist and must not be cited; the same pullback-along-`v`
obstruction as in `Variants/Profunctorial.agda` is at work. Everything not
mentioning the reindexed Φ is proved outright.
This file's `MR2` is *unrelated* to the construction in `Incoherent/Slice.agda`
described above — despite the shared filename, `Variants/Slice.agda` slices
the *domain* of Φ, not the `iMR2ᴸ B ≃ Slice C (B×[B,B]₀)` equivalence.

## Adjunction / Cartesian instantiation

### `Adjunction/TotRep.agda`
Builds the incidence relation between the total category (see
`Coherent/TotalCategory.agda`) and the repair fibration (see
`Coherent/Repairs.agda`): the category of repairs *coreflects* into the
total category.
- `K` — the coreflector `total → repairs`, forgetting the metabolic map `f` and keeping only the repair component `Φ`.
- `[_,Cod]₁` — precomposition of the hom functor `[A,-]` with `Cod`, reindexed by `u`.
- `𝕁` — the inclusion `repairs → total`, sending a repair system `(A, Φ)` to the (M,R)-system `(A, A)` with identity metabolic map `id : A ⇒ A` and repair `Φ`.
- `𝕁⊣K` — the adjunction `𝕁 ⊣ K`; since its unit is the identity, `𝕁` is full and faithful and the total category coreflects onto the repair fibration.

### `Cartesian/Sets.agda`
The category of Sets as a Cartesian closed monoidal category,
used to instantiate the Rosen constructions concretely.
- `Sets-Canonical` / `Sets-CCC` — the canonical and bundled Cartesian-closed structures on Sets.
- `Sets-Monoidal` / `Sets-Closed` — the induced monoidal and closed structures (product given by `×`, exponentials by function types).

**Note:** re-exports `extensionality` (function extensionality) from
`Axioms.agda`. That is a standard axiom, not a placeholder for a missing proof,
but it does prevent `--safe` on this module and on everything downstream.

### `Axioms.agda`
The one place where the development's non-logical assumptions are declared.
Contains function extensionality and nothing else. `grep -rn Rosen.Axioms`
lists every module that depends on an axiom.

### `Cartesian/Concrete.agda`
The parametric instantiation point `(o : Level)` for the Rosen constructions
over Sets. As it stands it carries only the module declaration and imports —
the concrete constructions it is meant to tie together live in
`Cartesian/Sets.agda` and `Cartesian/WellPointed.agda`; no instantiations are
defined here yet.

### `Cartesian/WellPointed.agda`
Well-pointedness of Sets, and the one consequence the development needs from it:
a natural transformation `id ⇒ [A,-]` over Sets is forced to be the constant
family, so `Nat(id, [A,-])` is a singleton.
- `point` — the map `1 → X` naming an element.
- `α-is-const` — every `α : id ⇒ [A,-]` satisfies `η α X z ≡ λ _ → z`.
- `Nat-id-hom-unique` — hence any two such agree.

**Status:** complete, no holes.  Not `--safe`, only because it reaches
`extensionality` through `Cartesian/Sets.agda`; the proof itself does not use it.

This module formalises the paper's `lem_onset_trivials`.  Its header explains why
the hypothesis deserves a name of its own: in the topos of C₂-sets 1 is not a
generator, nothing here applies, and that is exactly what the paper's
`cartesian_w_nontrivial_MRs` exploits.

A former `Cartesian/Adjoints.agda` built left adjoints to `[_]f` and `⟅_⟆f` out of
this singleton property.  It was removed: the adjunctions exist only when every
coherent (M,R)-system is trivial, so they relate categories whose objects the
rest of the development is at pains to escape.  The paper records the
obstruction in a footnote in §3 instead of claiming the result.

