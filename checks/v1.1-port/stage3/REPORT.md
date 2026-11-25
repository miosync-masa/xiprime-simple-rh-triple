# v1.1 stage 3: the final theorems without the hypothesis — audit record

Date: 2026-11-25. Branch `v1.1-port-4331`. New theorem file: commit `94f2ed4`
(`lean/RHTripleIntegration/Unconditional.lean`, SHA-256
`97c9f494…5c4a5079e8`; full value in `git`).

## Result

```
xiPrime_simple_proportion_c20_unconditional :
  1 - c20 / 3 ≤ liminf (fun T => ↑(Zeta23.XiPrime.N0simple 0 T) / ↑(Zeta23.XiPrime.Ncount 0 T)) atTop
xiPrime_simple_proportion_ge_9742_unconditional :
  0.9742 ≤ liminf (fun T => ↑(Zeta23.XiPrime.N0simple 0 T) / ↑(Zeta23.XiPrime.Ncount 0 T)) atTop
```

with `c20 = 77223/1000000`, so `1 - c20/3 = 974259/1000000` (at least 97.42%).
Each is the corresponding v1.0 theorem applied to `riemannHypothesis : RiemannHypothesis`
from the entry module `Main` of the compiled release. `#print axioms` for both:
`[propext, Classical.choice, Quot.sound]` (`final-link.log`).

## What was checked here, and by what

| Item | Checked by | Outcome |
|---|---|---|
| The two new theorems | Lean 4.33.1 elaborator and kernel, one compilation importing `Main` | accepted |
| Axioms of the two new theorems | `#print axioms` in that compilation | the three standard axioms |
| The 5 modules of `RHTripleIntegration` (incl. `Unconditional`) | `leanchecker` (shipped with Lean 4.33.1), replay in the kernel | rc 0 |
| The other 85 modules of this repository | `leanchecker`, one module per process | 85/85 rc 0 |
| The 317 modules of AF | `leanchecker` (one run over the prefix `Zeta23`, one worker thread) | rc 0, 317 modules replayed |
| The 175,187 modules of the release | — | **not re-checked here in any way** |
| comparator | — | **not run** |
| A negative control for `leanchecker` (a forged object) | — | **not run** |

## Trust boundary

- Importing a compiled object does not make Lean re-check it. In the final compilation Lean
  checked only the two new declarations; `riemannHypothesis` and everything under it were read
  from the release objects as they are.
- What ties those objects to the published release is hashes only (next section). The
  correctness of the release rests on its authors' build and on the independent checks reported
  on A. Sutherland's page (https://math.mit.edu/~drew/grh/). Those checks were **not re-run
  here**; we only compared the hash of `Main.olean`.
- `#print axioms` reads the axioms recorded through the imported objects; it is as trustworthy
  as those objects.
- The AF objects (317 modules) and our 89 modules were compiled here from source by Lean 4.33.1,
  each declaration passing the kernel once at compile time. The replay is a second pass of the
  same kernel over the stored declarations of all 407 modules. `leanchecker` describes itself as
  "not an external verifier, simply a tool to detect environment hacking"; the replay is not an
  independent check of the kernel.

## Downloaded files and hashes

Source: https://proofsandreasons.io/rh-oleans.html, files under
`https://photos.proofsandreasons.io/alp-oleans-357309b5dd12/`.

- 14 archives, 34,269,336,477 bytes (31.92 GiB). SHA-256 of each was computed **before
  extraction** and equals the release's `SHA256SUMS` (copy: `release-SHA256SUMS`). No archive
  member had an absolute path or `..`.
- After extraction: 175,187 project `.olean` files; all 175,187 equal the per-module list
  `SHA256SUMS-project-oleans.txt.gz` (0 different, 0 missing; `release-olean-hash-check.json`).
- `lib/Main.olean`: `9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad`
  — equal to the release list and to the value on Sutherland's page. Recomputed after the
  machine reset of 12:58: unchanged.
- `Unconditional.olean` (ours): `d477068271f3c1ada15d9b349d874cac0d84ecb42455874d1549dcc9839b67a8`,
  unchanged after the reset.

## One Mathlib

**The Mathlib used everywhere is the one shipped inside the release (`deps/mathlib`, revision
`0df444a360eaa60ab8c11dca51a86af692955474`), together with the release's seven other
dependencies.** No other Mathlib was on `LEAN_PATH` in the AF build, in the build of our 89
modules, in the final compilation, or in the replay. (For reference: 52,160 object files of the
release's `deps/` are byte-identical to the copy from Mathlib's official cache that was used in
stage 2.) Search path of the final compilation: `final-link-leanpath.txt`.

## Builds from source

| | AF (`3635e748`, from `git archive`, empty output dir) | this repository (closure) |
|---|---|---|
| Modules | 317/317 | 89/89 |
| Errors / `sorryAx` | 0 / 0 | 0 / 0 |
| Warnings | 254 | 20 |
| Wall | 810.9 s (6 workers) | 137.8 s (4 workers) |
| Sum over modules | 4698.3 s | 395.1 s |
| Combined source SHA-256 | `c54b96d5…05d484ab` | `0fc6ba0b…0ea72c` |

Full values and per-module results: `af-build.json`, `ours-build.json`. The pinned AF checkout
was not touched; AF sources are unmodified (stage 1 expected a toolchain bump only; that held).

## Final compilation: time and memory

Machine: Apple M5 Pro, 15 cores, 24 GiB (25,769,803,776 bytes), macOS 26.5.2, arm64.
The release objects were built on x86_64 Linux; they loaded on this machine without error.
No declaration-name collision occurred between the release, AF and this repository.

| | Value |
|---|---|
| Elapsed | 1204.20 s |
| CPU | 23.86 s user, 150.61 s sys |
| Maximum resident set size | 5,292,048,384 bytes |
| Peak memory footprint | 5,720,564,568 bytes |

## Replay in the kernel

### Final state

| Set | Modules | Tool | Outcome |
|---|---|---|---|
| `RHTripleIntegration.*` incl. `Unconditional` (release on the path) | 5 | `leanchecker`, one process | rc 0 |
| Rest of this repository | 85 | `leanchecker`, one process per module | 85 × rc 0 |
| AF | 308 | `leanchecker`, one process per module | 308 × rc 0 |
| AF: `Zeta23.MV`, `Zeta23.PrimeSideB` | 2 | `leanchecker` (retry) | rc 0 |
| AF: `Zeta23`, `Zeta23.PrimeSideA`, `Zeta23.Taper`, `Zeta23.XiPrime.Coeff`, `.ExplicitFormula`, `.QuarticWindow`, `.ZeroCount` | 7 | `tools/ReplayOne.lean` | 7 × rc 0 |

All 90 modules of this repository (89 + `Unconditional`) and all 317 modules of AF were
replayed. No run reported a declaration rejected by the kernel. Per-module time and memory:
`replay/serial-ours.tsv`, `replay/serial-af.tsv`, `replay/serial-af-retry.tsv`,
`replay/one-af-parents.tsv`. Except for the first row, the release was not on the search path
(`replay/leanpath-norelease.txt`): none of these modules imports it.

### What went wrong on the way, in order

1. **11:17, five jobs at once, release on the path, many modules per process** (`replay/j*.log`).
   j1 attempt 1: rc 1, our path mistake (`Unconditional.olean` in a directory the search did
   not reach; never read). j1 attempt 2 (12:20): rc 0, 818 s, peak footprint 34.75 GB.
   j2 (85 modules in one process): terminated abnormally at 12:38:58 after 4861 s, peak
   footprint 100.02 GB. j3–j5 (AF): no verdict; **the machine reset at about 12:58**.
   Starting five such jobs together was our decision and our mistake.
2. **13:10, one module per process, release off the path**: 85/85 rc 0 in 320 s; largest peak
   footprint 3.58 GB (`TripleCorrelation.D20Pack`).
3. **13:15, AF, same method**: the first module, the root `Zeta23`, hit the 900 s limit
   (`serial-af-attempt1.tsv`); a second try was stopped by us at swap use of 27 GB.
4. **13:36, AF without the root, guard at +6 GB swap or 300 s**: 308 rc 0; 8 stopped by the
   guard (no verdict).
5. **Retry of the 8 with guard at +18 GB**: `Zeta23.MV` rc 0, `Zeta23.PrimeSideA` stopped by
   the guard, `Zeta23.PrimeSideB` rc 0, `Zeta23.Taper` **rc 1** with
   `uncaught exception: failed to read file '…/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.olean'`
   reported for `Zeta23.Taper.Params` at a peak footprint of 52.9 GB (`replay/fail-af-retry.out`).
   This is a failure to read a file, not a kernel rejection: the file's SHA-256 is unchanged
   (`b88840c7…ece76d1e`), and `Zeta23.Taper.Params` had passed alone in step 4 and passed again
   in step 6. We take it to be a resource failure; that is an inference.
6. **`tools/ReplayOne.lean`** for the remaining 7: each rc 0 in 1–3 s, peak footprint ≤ 1.2 GB.

### Cause of the memory growth (read from the source, `src/lean/LeanChecker.lean` of v4.33.1)

- `leanchecker X` replays **every module whose name has prefix `X`**, not only `X`. So
  `leanchecker Zeta23` means all 317 AF modules, and `leanchecker Zeta23.Taper` means
  `Zeta23.Taper` and the 9 modules under `Zeta23/Taper/`.
- All selected modules are replayed **as parallel tasks, each importing its own environment**.
  Memory grows with the number of selected modules; 85 at once gave the 100 GB of step 1.
- For each argument it lists **every `.olean` on the search path** to find the matches; with the
  release (175,187 modules) on the path this alone is slow (the same single module: 50.5 s with
  the release on the path, 12.1 s without).

`tools/ReplayOne.lean` (SHA-256 `29e71f59…f0ae5e5`) contains the function `replayFromImports`
copied verbatim from that source, with a driver that takes module names literally and replays
them one after another. It returns 1 for a nonexistent module. It was used for the 7 modules
only; it has not been reviewed by anyone else.

### Official `leanchecker` for everything (14:40–14:51)

With `LEAN_NUM_THREADS=1` the tasks of `leanchecker` run one after another, and the memory
stays at one environment. Run this way (`replay/official.sh`, `-v`, release off the path):

| Prefix | Modules replayed | rc | Elapsed | Peak footprint |
|---|---|---|---|---|
| `Zeta23.Taper` | 10 | 0 | 31.5 s | 0.63 GB |
| `Zeta23.PrimeSideA` | 13 | 0 | 27.9 s | 0.63 GB |
| `Zeta23.XiPrime.Coeff` | 19 | 0 | 22.3 s | 0.61 GB |
| `Zeta23.XiPrime.ExplicitFormula` | 16 | 0 | 18.7 s | 0.38 GB |
| `Zeta23.XiPrime.QuarticWindow` | 7 | 0 | 15.4 s | 0.63 GB |
| `Zeta23.XiPrime.ZeroCount` | 10 | 0 | 12.0 s | 0.38 GB |
| `Zeta23` (all of AF) | 317 (317 distinct names in the log) | 0 | 419.3 s | 0.66 GB |

So every one of the 90 + 317 modules has passed the official `leanchecker`; **no result in this
record depends on `tools/ReplayOne.lean` any more.** Its 7 results agree with the official ones.
Logs: `replay/official.tsv`, `replay/official-logs/`.

### The tool and the closure

`tools/ReplayOne.lean` contains `unsafe def` (as does the function it copies). It is a checking
tool, outside the closure of the theorems: no file under `lean/` imports it or anything from
`tools/`. Checked on this commit: the import roots occurring under `lean/` are `Mathlib`,
`Zeta23`, `RHBridge`, `RHTriple`, `TripleCorrelation`, `RHTripleIntegration`, and `Main` (the
last in `Unconditional.lean` only).

## Stage 1 and the outcome

Stage 1 made no prediction for stage 3. It listed these as unknown; the outcomes are:

| Listed in stage 1 as unknown | Outcome |
|---|---|
| Whether declaration names of the release collide with AF's or ours | no collision |
| Whether objects built on x86_64 Linux load on arm64 macOS | loaded without error |
| Load time and memory of the release on this machine | final compilation: 1204 s, 5.7 GB peak |

Stage 1's prediction for AF (pins only, 0 source lines changed) held in the from-scratch build.
Nothing was written in advance about the memory need of the replay. Run as five parallel
multi-module jobs it exceeded the machine; run one module at a time it needs at most 3.6 GB
(34.7 GB footprint for the one job that imports the release).

## Not done

comparator; independent kernels (nanoda, lean4lean) on our theorem; any re-check of the release;
negative control of the replay tools (a forged object that they should reject); d = 50
(outside the closure, not ported).
