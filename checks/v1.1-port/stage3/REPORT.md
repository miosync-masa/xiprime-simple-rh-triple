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
| The other 85 modules of this repository | `leanchecker` | **not completed** (process terminated abnormally) |
| The 317 modules of AF | `leanchecker` | **not completed** (machine reset) |
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
  each declaration passing the kernel once at compile time. The replay by `leanchecker`, a
  second pass, finished only for the 5 modules named above.

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

## Replay with `leanchecker`: what happened

Command form: `LEAN_SYSROOT=<4.33.1 toolchain> PATH=<toolchain>/bin:$PATH LEAN_PATH=…
leanchecker <modules…>`; five jobs started together at 11:17:56 (`replay/`).

| Job | Modules | Outcome | Elapsed | Max RSS | Peak footprint |
|---|---|---|---|---|---|
| j1, attempt 1 | 5 (`RHTripleIntegration.*`) | rc 1 — **our path mistake**: `Unconditional.olean` was in a directory the search did not reach; the file was never read | 354.85 s | 8.82 GB | 25.98 GB |
| j1, attempt 2 (12:20:58) | the same 5 | **rc 0** | 818.00 s | 10.48 GB | 34.75 GB |
| j2 | 85 (rest of this repository) | **terminated abnormally** at 12:38:58, no verdict | 4861.09 s | 9.67 GB | 100.02 GB |
| j3, j4, j5 | 317 (AF) | no verdict; machine reset at about 12:58 | — | — | — |

- No job reported a declaration rejected by the kernel. The failures are a wrong path (ours),
  a killed process and a machine reset; the cause of the last two is taken to be memory
  exhaustion (footprint of 100 GB on a 24 GiB machine; swap 11.8 of 13 GB in use at 12:21),
  which is an inference from these numbers, not a diagnosed fact.
- Running five replay jobs at once on this machine was our decision and was the mistake.
- Following the instruction to stop and record on a memory failure, the replay was **not
  restarted**.

## Stage 1 and the outcome

Stage 1 made no prediction for stage 3. It listed these as unknown; the outcomes are:

| Listed in stage 1 as unknown | Outcome |
|---|---|
| Whether declaration names of the release collide with AF's or ours | no collision |
| Whether objects built on x86_64 Linux load on arm64 macOS | loaded without error |
| Load time and memory of the release on this machine | final compilation: 1204 s, 5.7 GB peak |

Stage 1's prediction for AF (pins only, 0 source lines changed) held in the from-scratch build.
Nothing was written in advance about the memory need of the replay; it exceeded the machine.

## Not done

comparator; independent kernels (nanoda, lean4lean) on our theorem; replay of 402 of our and
AF's 407 modules; any re-check of the release; negative control of the replay tool; d = 50
(outside the closure, not ported).
