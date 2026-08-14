# Repository instructions

## Objective

Formalize Theorem `t:main` from the paper in this repository in Lean 4 with
Mathlib. Also formalize Corollary `c:easy` with its printed statement unchanged.
Do not formalize the Multicolor section or `r:final`. Treat the paper as the
source for mathematical intent and Lean as the source for the checked formal
statement. Redo the numerical optimization independently and kernel-check every
inequality used to obtain `t:main`.

## Start every task

1. Read the relevant paper passage and `docs/blueprint.md` entry.
2. Inspect nearby Lean modules and search Mathlib for existing declarations.
3. State the intended declaration name, module, and dependencies before making
   a broad structural change.

## Build and verification

- Run `lake build` from the repository root before finishing any Lean change.
- While iterating, check a focused file with
  `lake env lean RamseyLean/Path/To/File.lean`.
- Deliver no `sorry`, `admit`, placeholder axioms, or disabled linters unless
  the user explicitly requests a temporary scaffold. If a proof is blocked,
  leave the compiling tree unchanged and document the blocker in the blueprint.
- Do not claim a proof is complete based only on editor feedback; verify it with
  the command line.

## Formalization style

- Reuse Mathlib definitions and theorems whenever their semantics match.
- Keep `autoImplicit` under control: declare important variables and hypotheses
  explicitly.
- Prefer small named interface lemmas over long tactic scripts repeated in
  multiple proofs.
- Give each formalized paper result a docstring containing its paper label and
  a concise description of any difference from the printed statement.
- Keep the public statements corresponding to `t:main` and `c:easy` fixed once
  agreed. Intermediate paper statements may be strengthened, weakened,
  generalized, split, or replaced when that simplifies the two targets; record
  every such change and its role in `docs/blueprint.md`.
- Use namespaces and qualified names to avoid collisions with Mathlib.
- Import narrowly once a module is stable. During discovery, `import Mathlib`
  is acceptable; use `#min_imports` when practical before finalizing a module.
- Useful discovery tools include `#check`, `#find`, `library_search`, `exact?`,
  `apply?`, `rw?`, `simp?`, and `aesop?`. Replace suggestion tactics with clear,
  maintainable proofs when that improves robustness.

## Blueprint discipline

- Update `docs/blueprint.md` when adding or renaming a declaration, changing a
  modeling decision, discovering a dependency, or identifying a paper gap.
- Preserve a traceable mapping from every formalized paper label to its Lean
  declaration and module.
- Distinguish unformalized results from results whose statements compile but
  whose proofs are incomplete.

## Git discipline

- Keep the tree compiling at each commit.
- Prefer one definition cluster or one conceptual proof per commit.
- Do not edit the paper source unless the task explicitly asks for it.
- Do not mix dependency/toolchain upgrades with mathematical proof changes.
- Never discard unrelated user changes from the working tree.
