# v1.1 stage 1: target pin, AF, and what breaks (investigation only)

Date: 2026-11-25. No source file of the repository was changed or committed in this stage.
Trial builds were made in a separate working copy; the one fix that was tried there is kept
only as `trial2-fix.patch`.

## 1. Target pin (with sources)

| Item | Value | Source |
|---|---|---|
| Lean | `leanprover/lean4:v4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | release `README.txt` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` (= tag `v4.33.1`) | release `README.txt`; ternary-goldbach `proof/README.md` |
| batteries | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` | release `README.txt` |
| aesop | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` | same |
| Qq | `92c15be17b7caf78c2ad767ec40f89052d908d81` | same |
| proofwidgets | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` | same |
| importGraph | `16f02aa7642864af59f1ff0e384a015994db9118` | same |
| plausible | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` | same |
| LeanSearchClient | `5f4d51b81cbd3f6b32b156bfad9056621a040404` | same |

Release: <https://proofsandreasons.io/rh-oleans.html>, files under
`https://photos.proofsandreasons.io/alp-oleans-357309b5dd12/` (`README.txt` SHA-256 `c50c80c0…47320dd`,
`SHA256SUMS` SHA-256 `8fc121dd…a1f7e26`, both as downloaded on 2026-11-25).
The `lake-manifest.json` that `lake update` produced for AF on the Mathlib pin (2026-11-22 survey)
has exactly these eight revisions, plus the package `Cli`, which the release README does not list.

Release facts (from its README, not checked by us): 175,187 project modules, 14 archives,
31.9 GiB, 89 GiB + 6 GiB unpacked, built on x86_64 Linux, project files are plain
(non-module-system) `.olean`s specific to Lean v4.33.1; entry point `lib/Main.olean`, which
states `riemannHypothesis : RiemannHypothesis`.

`Main.olean` SHA-256 `9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad`: the same
value appears in the release's `SHA256SUMS-project-oleans.txt.gz` and on Sutherland's page
<https://math.mit.edu/~drew/grh/> (page of 2026-11-24 05:25 UTC). This compares two published
lists; no archive has been downloaded yet.

## 2. AF

- The release does **not** contain AF: none of the 175,187 module paths contains `Zeta23`,
  `XiPrime`, `RHTriple`, `RHBridge` or `TripleCorrelation`. So there is no module-name clash,
  and the declarations we use (`XiPrime.Ncount`, `XiPrime.N0simple`, the Weil explicit formula)
  must come from our own build of AF.
- Upstream AF is still on the old pin: `anthropics/formal-math` `zeta23/` has
  `lean-toolchain = v4.33.0-rc2`, Mathlib `51e6992e…` (checked 2026-11-25; last change to that
  directory 2026-08-28). There is no upstream version on the target pin.
- AF therefore has to be moved to the target pin by us. In the 2026-11-22 survey this needed
  only the three pin files (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`); all 329 AF
  files compiled with unchanged sources. That build is the one used for the trials below.
- Not known: whether any *declaration* name of AF or of our 89 modules clashes with one of the
  release's declarations. This can only be seen when the objects are loaded (stage 3).

## 3. Trial build of the 89 modules on the target pin

| Run | Sources | Result |
|---|---|---|
| trial 1 | unchanged (`fa0578a`) | 75 built, **1 failed** (`RHTriple.PolarGate`), 13 not reached (they import it) |
| trial 2 | `trial2-fix.patch` applied in the working copy | 89/89 built, 0 errors, 0 `sorryAx`, 20 linter warnings; wall 211.7 s, sum 540.3 s; `D20Pack` 37.5 s |

Breakage table:

| Module | Kind | Cause | Fix |
|---|---|---|---|
| `RHTriple.PolarGate` (1 use, line 210) | Mathlib lemma changed shape | `Asymptotics.IsLittleO.sum` now concludes `(∑ i ∈ s, A i) =o[l] g'` (sum of functions); the old pointwise form is the generated `IsLittleO.fun_sum` | replace the name by `Asymptotics.IsLittleO.fun_sum` |
| `RHTriple.TriplePrimeGate` (3 uses, lines 91–93) | same | same (found by search; the module was not reached in trial 1) | same |

Nothing else broke: no `simp`-set change, no timeout, no renamed lemma elsewhere. The fix is
4 changed lines in 2 files and does not exist on the old pin (`fun_sum` is new), so the two pins
cannot share these two files unchanged.

On the target pin with the fix (`trial2-check.out`): both final theorems have the same types as
before, `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, and the five duplicated
definitions are still equal by `rfl`.

## 4. `RiemannHypothesis`

`Mathlib/NumberTheory/LSeries/RiemannZeta.lean` has SHA-256 `db9f37f0…f2a1a9` at both
`51e6992e…` and `0df444a3…` (whole file identical). The definition is

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## 5. Pre-registration against the outcome

| Prediction (2026-11-25 09:58:06 JST) | Outcome | Verdict |
|---|---|---|
| 0–3 broken modules, most likely 0 | 2 modules need a change (1 failed, 1 more behind it) | inside the range; the "most likely 0" was wrong |
| if anything breaks, 1–2 in RHTriple, 0 in TripleCorrelation | 2 in RHTriple, 0 in TripleCorrelation | correct |
| about 20 linter warnings, wording changed | 20 warnings | count correct; wording not compared |
| `D20Pack` passes in about 30 s | passes, 37.5 s (3 workers) | correct |
| AF needs the pin files only, 0 source lines | consistent with the 2026-11-22 build; not rebuilt today | not re-tested |
| `RiemannHypothesis` identical | identical | correct |

The cause of the breakage had been seen in the 2026-11-22 survey (the `IsBigO.sum` family
changed shape) and was recorded then as "not used by either project". That was true of the
projects examined then; the 61 RHTriple files did not exist yet. The prediction should have
taken it into account.

## 6. For stage 3 (estimates, nothing verified)

- Disk: 460 GiB free; the release needs about 32 GiB of downloads and about 95 GiB unpacked.
- Machine: Apple silicon (arm64), 24 GiB RAM, 15 cores. The release was built on x86_64 Linux.
  Whether its `.olean`s load on this machine has not been tried.
- The precedent reports CPU 7 min 40 s and 38 min elapsed for its final link; its machine and
  memory are not known to us.
- Independent checks reported on Sutherland's page (nanoda, con-leche, lean4lean, Comparator
  v4.33.0, sandboxed rebuild) concern the release itself, not our theorem.
