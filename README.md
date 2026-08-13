# RamseyLean

Lean 4 formalization of the paper stored in this repository. The project uses
Mathlib and pins both Lean and Mathlib to `v4.32.1` for reproducible builds.

## First-time setup

1. Install [Git](https://git-scm.com/) and
   [VS Code](https://code.visualstudio.com/).
2. Install [Elan](https://lean-lang.org/install/) and the official
   `leanprover.lean4` VS Code extension.
3. From the repository root, run:

   ```powershell
   lake update
   lake exe cache get
   lake build
   ```

4. Open the repository root in VS Code. Open a `.lean` file and check that the
   Lean InfoView reports no errors.

Elan reads `lean-toolchain`, so no global Lean version needs to be selected.
The first dependency/cache download can take several minutes; later builds are
incremental.

## Repository layout

- `RamseyLean/`: Lean source modules.
- `RamseyLean.lean`: root module; import completed project modules here.
- `docs/blueprint.md`: theorem inventory, dependencies, and paper-to-Lean map.
- `paper/`: the exact paper source snapshot, PDF, bibliography, and style file.
- `AGENTS.md`: durable instructions for Codex and other coding agents.

The current target is *Optimizing the CGMS upper bound on Ramsey numbers* by
Parth Gupta, Ndiamé Ndiaye, Sergey Norin, and Louis Wei. Its complete
paper-to-Lean inventory, dependency order, source checksum, and known statement
gaps are recorded in `docs/blueprint.md`.

## Everyday commands

```powershell
# Check the whole formalization
lake build

# Check one file while iterating
lake env lean RamseyLean/Basic.lean

# Update within the versions pinned by lakefile.toml
lake update
lake exe cache get
```

Change the Mathlib revision and `lean-toolchain` together in a dedicated commit.
Run `lake update`, commit the resulting `lake-manifest.json`, and rebuild before
merging an upgrade.

## Recommended formalization loop

1. Pick one dependency-ready row in `docs/blueprint.md`.
2. Read its paper passage and inspect nearby Lean declarations.
3. Search Mathlib before introducing local definitions or bridge lemmas.
4. Fix the declaration type before asking Codex for the proof.
5. Keep the task to one result or one reusable support lemma.
6. Run a focused file check while iterating and `lake build` before committing.
7. Record every statement mismatch, new dependency, or blocker in the blueprint.
8. Remove exploratory `example` blocks before committing.

For productive Codex tasks, give one bounded goal at a time, for example:

> Formalize paper lemma `l:FpAvg` in the module named by the blueprint. Reuse
> Mathlib where possible, do not change earlier theorem statements, update the
> blueprint, and finish with `lake build` passing without `sorry` or new
> axioms.

Small, compiling commits make proof regressions and Mathlib upgrades much easier
to diagnose than large section-wide translations.

After making the baseline commit, independent discovery or proof tasks can run
in separate Codex worktrees. Avoid parallel edits to the same foundational
module; merge shared interfaces before starting proofs that depend on them.
