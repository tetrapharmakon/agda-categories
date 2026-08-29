---
name: lint-agda
description: Bring Agda sources under src/Categories/Rosen/ into line with the agda-stdlib style guide, and commit the result atomically. Use whenever the user says "lint the files", "lint <path>", "style-check", or asks for the Rosen tree to be tidied/aligned with the style guide — no further explanation should be needed from them. Also the reference for how commits in this repo are shaped.
---

# Linting the Rosen tree

Style source: <https://github.com/agda/agda-stdlib/blob/master/doc/style-guide.md>,
distilled below and adapted where agda-categories deliberately differs. When a
rule below and the upstream guide disagree, this file wins — the deviations are
intentional and recorded in "Deviations".

## The invariant

**A lint must not change what typechecks.** Agda layout is semantic. Every rule
here is cosmetic-by-construction; if a fix would alter a term, drop the fix.

Verification loop, non-negotiable:

```bash
cd src/Categories/Rosen && make check          # baseline, before touching anything
# ... edits ...
cd src/Categories/Rosen && make check          # must end at the same or better count
```

`make check` **skips `Functorial/`** (`SOURCES` filters it out). If you lint
anything under `Functorial/`, verify it by hand:

```bash
cd /home/fouche/repos/agda-categories
agda -i src --warning=noUserWarning --warning=noUnsupportedIndexedMatch \
     --warning=noUselessPrivate src/Categories/Rosen/Functorial/<F>.agda
```

Files that failed the baseline stay failing — do not fold proof work into a lint.

## Procedure

1. `git status`. If the tree is dirty, say so and lint only what the user named,
   or ask. Never lint on top of someone else's uncommitted work silently.
2. Baseline `make check`; record the pass/fail set.
3. Scan (see "Quick scan" below) to size the job before editing.
4. Apply **[FIX]** rules file by file. Collect **[FLAG]** findings into a report;
   do not act on them without being asked.
5. Re-run `make check` (plus direct `agda` for `Functorial/`).
6. Commit atomically — see "Commits".
7. Report: what was fixed per file, and the [FLAG] list you left alone.

## Quick scan

```bash
cd src/Categories/Rosen
grep -rn " $"            --include=*.agda .            # trailing whitespace
grep -rnP "\t"           --include=*.agda .            # tabs
grep -rn "[A-Za-z0-9]'"  --include=*.agda .            # ASCII ' instead of ′
for f in $(find . -name '*.agda'); do [ -n "$(tail -c1 $f)" ] && echo "$f"; done
awk 'length>100 {print FILENAME":"FNR": "length}' $(find . -name '*.agda')
```

As of the last full scan the tree carried ~449 trailing-whitespace lines, ~149
ASCII primes, 18 files with no final newline, 745 lines over 72 columns (239
over 100). Expect those orders of magnitude; a scan returning zero means you
scanned the wrong directory.

---

## [FIX] — apply these mechanically

### Whitespace
- No trailing whitespace. No tabs.
- Exactly one newline at end of file.
- Top-level module contents at zero indentation; each nested scope +2 spaces.
- `where` indented 2 below the proof; its contents aligned with the `where`.

### Blank lines
- One blank line after the module header, and after each term definition.
- **Two** blank lines between adjacent `record`/`module` definitions — they use
  single blank lines internally, so two marks where one ends.
- One blank line after a `private` block, two before the main module body.

### Alignment
- `data`: align the `:` of every constructor.
- `record`: align the `:` of every field.
- Record literals: align the `=` of every field.
- Function clauses: align arguments across cases where possible.

### Record literal layout
`record` on the same line as the rest of the proof; `{` opens the next line;
every later field on its own line starting with `;`; closing `}` on its own line.

```agda
foo = record
  { F₀ = ...
  ; F₁ = ...
  }
```

### Multi-line type signatures
Continuation lines align with the first character of the type. `→` goes at the
**end** of a line, never the start of the next.

### Equational reasoning
`begin` on the same line as the rest of the proof; each `_≈⟨_⟩_` step on its own
line indented 2; the relation signs aligned into a column.

### Imports
- All imports immediately after the module declaration, **alphabetical**.
- **Exception**: imports needed by the module's own parameters go *above* the
  module declaration. This repo already does this — keep it.
- **Instantiated imports** (a parameterised module applied to arguments) go
  *after* the main import block. In this tree that is the
  `import Reason` / `open Reason C` / `open Closed Cl using (...)` /
  `open import Categories.Rosen.Coherent.Core Cl` group. Keep it last.
- `using (...)` when taking fewer than five names from a module.
- Modifier order: `public`, `using`, `renaming`. If `public` is present, put
  `using`/`renaming` on their own line.
- Never re-export via `public` inside the import list — import qualified, then
  `open ... public` later in the file where it is visible.

### Comments
- Above the term, never trailing on the same line.
- Section banners are exactly 72 `-` characters wide, title in sentence case:
  `-- Rounding functions`, not `-- Rounding Functions` or `-- ROUNDING FUNCTIONS`.

### Symbols
- Primes are `′` (`\'`), not ASCII `'`. **Renaming a bound variable is a [FIX];
  renaming anything that leaves the file is a [FLAG]** — grep for uses first:
  `grep -rn "\bNAME\b" --include=*.agda src/`
- `∙` is `\.`, not `\bu2`. `·` is `\cdot`.
- Negated relations use the negated glyph (`≰`, `≢`), not `¬ (_ ≤ _)`.
- Instance arguments use ASCII `{{_}}`, not `⦃_⦄`.
- Dot patterns are unnecessary since Agda 2.6.0 — remove them.

### Fixity
Anything with `_` in its name gets an explicit fixity. Standard values:
`infix 4` binary relations · `infixl 7 _*_` · `infixl 6 _+_ _-_` · `infix 8 -_`
· `infixr 7 _∧_` · `infixr 6 _∨_` · `infix 3 ¬_` · `infixr 5 _∷_` ·
`infixr 9 _∘_` · `infixr 4 _,_` · `infixr 2 _×_` · `infixr 1 _⊎_` ·
`infix 3 _∎` · `infix 1 begin_` · `infixr -1 _$_`.

---

## [FLAG] — report, do not rewrite unasked

### Line length
The guide asks for 72 columns and concedes it is "the most violated rule ... not
always possible to achieve whilst using meaningful names". With
`NaturalTransformation`, `adjoint.Ladjunct` and aligned `≈⟨ ⟩` columns, this tree
cannot hit 72 without hurting readability.

Repo policy:
- Lines **you write or touch** should aim at 72 and must not exceed 100.
- Existing lines over 100: report them, fix only where the wrap is obviously free
  (a long import, a long comment).
- **Never mass-rewrap an aligned reasoning chain.** The column alignment carries
  more meaning than the margin does.

### Naming
Report, and only rename with the user's go-ahead (these names are load-bearing
across files):
- Datatypes capitalized; functions `camelCase`.
- Properties prefixed by their operator with `-` as separator: `+-comm`.
- Preconditions joined by `⇒`: `asym⇒antisym`; combined with `∨`/`∧`; square
  brackets for grouping: `[m∸n]⊓[n∸m]≡0`.
- Variables inside a proof name in alphabetical order: `m≤n+m`, not `n≤m+n`.
- Decidable versions written `R?`.
- `f⁺` for `Precondition → P(f)`, `f⁻` for `P(f) → Postcondition`.
- Variable conventions: `A B C` sets · `P Q R` predicates · `m n` ℕ · `i j k` ℤ
  · `x y z` otherwise · collections get a trailing `s`.

### Structure
- One named module per file. Named internal modules should be opened publicly at
  once or split out. No publicly exported single-letter internal modules.
- `private` is for temporary convenience terms only; non-trivial proofs inside a
  `private` block are discouraged.
- `mutual` is obsolete — put the signatures before the definitions instead.
- `with` is preferred to `Function.case`; the `|` is *not* aligned with `with`.
- Prefer `contradiction` over `⊥-elim` where both apply.
- Arguments implicit iff they can "almost always" be inferred; if a collection of
  proofs shares many implicits, extract an anonymous module.

---

## Deviations from upstream (do not "fix" these)

- **`let ... in` is permitted.** The guide prefers `where`, and for top-level
  definitions so do we — but agda-categories record literals cannot host a
  `where`, so `let` inside a record field is correct here, not a violation.
  ~20 files rely on this.
- **Module header.** Files open with
  `{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}`
  on line 1 — over 72 columns, and it stays that way.
- **Qualified-import naming** (`Data.Nat.Base` as `ℕ`, etc.) is a stdlib-internal
  convention; this tree follows agda-categories' `Categories.*` paths instead.
- **No deprecation blocks.** This is not a released library.
- **`sorry` is a real convention here.** A `private postulate sorry` marks a
  recorded mathematical obstruction, documented in `README.md` under a
  **Status:** line. A lint must never touch a `sorry`, a `postulate`, an open
  `{! !}` hole, or the comment explaining one — and if a lint changes anything
  a **Status:** line describes, update `README.md` in the same commit.

---

## Commits

Atomic and clean, always. The existing history is the model:

```
Rosen/Variants/Slice.agda: alphabetize imports
Rosen/MetabolicClosure: prove ReindexingPreservesClosure
```

- **One logical change per commit.** One file per commit when the change is
  per-file mechanical (imports, whitespace); one commit across files only when
  the change is genuinely a single concern.
- **Never mix a lint with a proof change.** If linting reveals a bug, finish the
  lint, commit it, then fix the bug in its own commit.
- Subject: `Rosen/<path>: <lowercase imperative>`, ≤72 chars where it fits.
- Body: why, when it isn't obvious. Wrap at 72.
- **Every commit must leave `make check` at least as green as it found it.**
  Verify before committing, not after.
- Stage explicitly by path. Never `git add -A` / `git add .` — this tree
  routinely carries unrelated dirty files (e.g. the `Makefile` `AGDA :=` line).
- Trailers on every commit:
  ```
  Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
  Claude-Session: <session url>
  ```
- Push only when asked. Working branch is `rosen`; `master` is upstream
  agda-categories and is not a target.
