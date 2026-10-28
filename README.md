# A lower bound of 0.8366 for Lebesgue's universal covering problem

Programs and certificates for the paper *A lower bound of 0.8366 for Lebesgue's universal covering problem*
by Tejasvi Singh Tomar (doi:10.5281/zenodo.23717911). Its supplement, doi:10.5281/zenodo.23717912, holds the large
archives and a copy of this repository.

## Theorem

Let `D` be the disk of diameter 1, let `B_n` be the regular Reuleaux `n`-gon of width 1, and let
`M(T_1, ..., T_m)` be the least area of the convex hull of congruent copies of `T_1, ..., T_m`. Then

    M(D, B_3, B_5, B_7) >= 0.836   and   M(D, B_3, B_5, B_7, B_9) >= 0.8366.

Hence every convex set in the plane that contains a congruent copy of every set of diameter 1 has area at least
0.8366 (Lebesgue's universal covering problem). The previous lower bound was 0.83474, proved by J. Hatchett with
`D`, `B_3` and `B_5` (doi:10.5281/zenodo.22135010). As a test of the method in five dimensions, the paper also proves
`M(D, B_3, B_5) >= 0.8347` (Proposition 4.2), slightly below that bound.

Numerically, these bounds are close to the most that the bodies can give. Local minimization finds a placement of
`D, B_3, B_5, B_7` with hull area 0.8364904560 (`independent/opt8_point.json`) and a placement of `D, B_3, B_5, B_7, B_9`
with hull area 0.8372950064 (`independent/opt11_point.json`). The smallest hull area at a leaf centre is 0.8347836763 in
`cert5d_08347`, 0.8365614 in `cert8d_0836` and 0.8377599866 in `cert11d_08366`.


## Proof outline

1. **Reduction.** The disk is fixed at the origin and the Reuleaux triangle has rotation 0. A placement is a
   point of R^5 (bodies D, B_3, B_5), R^8 (with B_7) or R^11 (with B_7 and B_9). A reflection symmetry and the
   rotational symmetries of the bodies bound the rotations, and a corner estimate bounds the translations of
   every placement with hull area at most the target. This gives a root box.
2. **Box bound.** On a box of placements, finitely many points of the bodies (witnesses) move with their bodies.
   While they stay in angular order around a point of the disk, the area `F(p)` of the polygon they span is at
   most the hull area. `F` is a polynomial in the translations and in the sines and cosines of the angles, and it
   is bounded on the box by a second-order Taylor expansion, with a certified lower bound for the smallest
   eigenvalue of the Hessian and explicit bounds for the variation of the Hessian.
3. **Combination bound.** Where the hull changes its combinatorial type inside a box, the box bounds of several
   witness fans are combined with nonnegative weights that add up to 1, and their gradients are added before
   absolute values are taken. Only the certificate for `D, B_3, B_5, B_7, B_9` uses this step.
4. **Certificate.** A branch-and-bound tree over the root box. Every leaf is closed by the box bound, by the
   combination bound or by the corner estimate.

## Checks at a glance

| Check | What it covers | Details |
|---|---|---|
| `checker/lbcheck.py` (ball arithmetic) and `checker/treecheck.py` | the three certificates | see Checking |
| second verifier (`independent/`), without the Taylor bound | samples of the leaves of `cert5d_08347` and `cert8d_0836`; all leaves of `cert11d_08366` | `independent/README.md`, `CHECKS.md` |
| kernel-checked Lean proofs (`formal/`) | 0.8347, 0.836 and 0.8366, each with a certificate of its own | see Lean proof; `formal/README.md` |
| Lean proof with compiled checks (`formal/`) | 0.8366, on the tree of the kernel-checked proof of 0.8366 | see Lean proof; `formal/README.md` |

## Running times

Wall-clock time per process on loaded x86-64 servers; for `cert11d_08366` the checker ran two processes per physical
core. Lean build times: see Lean proof.

| Run | `cert5d_08347` | `cert8d_0836` | `cert11d_08366` |
|---|---|---|---|
| search, longest part | 308 s | 987 s | 9,556 s |
| search, all parts | 531 s | 8,728 s | 2,847,069 s |
| checker, longest part | about 2 minutes | about 18 minutes | about 88 minutes |
| checker, all parts | about 3 minutes | about 2.7 hours | about 395 hours |
| second verifier | samples of leaves | samples of leaves | all leaves; first pass 3,959.7 CPU-hours (`CHECKS.md`) |

## Contents

| Path | Content |
|---|---|
| `checker/lbcheck.py` | the checker: ball arithmetic (Arb through python-flint, 80 bits); does not import the search; checks all three certificates |
| `checker/treecheck.py` | exact rational decoder of the trees, side files included (standard library and NumPy) |
| `search/lbsearch_v1.py`, `search/lbbnb_v1.py` | the search program that produced `cert5d_08347` (double precision; not part of the proof) |
| `search/lbsearch_v2.py`, `search/lbbnb_v2.py` | the search program that produced `cert8d_0836` (adds a cheaper first witness set) |
| `search/lbsearch_v4.py`, `search/lbbnb_v4.py` | the search program that produced `cert11d_08366` (adds the combination bound) |
| `search/area_bracket.py` | inner and outer polygon areas of the hull at one placement (numerical observations) |
| `certificates/cert5d_08347.tar.xz` | certificate of `M(D, B_3, B_5) >= 0.8347` (16 parts) |
| `certificates/cert8d_0836.tar.xz` | certificate of `M(D, B_3, B_5, B_7) >= 0.836` (24 parts) |
| `certificates/SHA256SUMS` | SHA-256 of the two archives |
| `certificates/README.md` | the format of the certificates and the contents of their archives |
| `certificates/cert11d_08366.sha256` | SHA-256 of the archive of the certificate of `M(D, B_3, B_5, B_7, B_9) >= 0.8366` (2,048 parts), which is too large for this repository and is archived only in the supplement |
| `independent/` | second verifiers, decoders, minimization and tests of the checker, and the run recorded in `full11/`; described in `independent/README.md` |
| `formal/` | the four Lean 4 proofs described below, with their own `README.md` and `SHA256SUMS` |
| `paper/main.tex` | the LaTeX source of the paper |
| `CHECKS.md` | the record of the second verifier's run on all leaves of `cert11d_08366`, and the size and SHA-256 of every archive at the DOI |

The checker is included unmodified, so its docstrings still name the lemmas by the labels used while the proof was
written, call the program `lbcheck_v4.py`, and mention working notes and earlier versions of the program that are not
part of this release.
The labels correspond to the paper as follows: Lemma R is the symmetry lemma (Lemma 2.3), Lemma C the corner lemma
(Lemma 2.4), Lemma F the fan lemma and the fan bound (Lemmas 3.1 and 3.3), the run identity is Lemma 3.4, Lemma T the
Taylor bound (Lemma 3.5, with Lemmas 3.6 and 3.7), and Lemma K the combination bound (Lemma 3.8).

## Checking

Requirements for the checker: Python 3 (tested with 3.12), NumPy (tested with 2.5) and python-flint (tested with 0.9).

    cd certificates
    sha256sum -c SHA256SUMS
    tar -xJf cert5d_08347.tar.xz
    tar -xJf cert8d_0836.tar.xz
    (cd cert5d_08347 && sha256sum -c SHA256SUMS)
    (cd cert8d_0836 && sha256sum -c SHA256SUMS)
    python3 -I ../checker/lbcheck.py cert5d_08347 present
    python3 -I ../checker/lbcheck.py cert5d_08347 $(seq 0 15)
    python3 -I ../checker/lbcheck.py cert8d_0836 present
    python3 -I ../checker/lbcheck.py cert8d_0836 $(seq 0 23)
    python3 -I ../checker/treecheck.py cert5d_08347
    python3 -I ../checker/treecheck.py cert8d_0836

For the third certificate, download `cert11d_08366.tar.xz` from the archive into `certificates/`, then

    sha256sum -c cert11d_08366.sha256
    tar -xJf cert11d_08366.tar.xz
    (cd cert11d_08366 && sha256sum -c SHA256SUMS)
    python3 -I ../checker/lbcheck.py cert11d_08366 present
    seq 0 2047 | xargs -P 8 -I{} sh -c 'python3 -I ../checker/lbcheck.py cert11d_08366 {} > check11_{}.json'
    python3 -I ../checker/treecheck.py cert11d_08366

`present` prints `[true, ...]` when all parts exist and their headers agree. For every part the checker prints a
JSON line, and `treecheck.py` prints a JSON line with `"ok": true` when every leaf box verified by the checker
equals the exact leaf box, the leaves of every grid cell tile it, and every side file lists exactly the leaves with
code `253` of its part. A certificate is accepted when the checker prints a line for every part `0, ..., P-1`, every
line has `"ok": true` and `"fails": 0`, and `treecheck.py` prints `"ok": true`.

The leaf codes are described in `certificates/README.md`. The parts can be checked separately and in parallel. `treecheck.py CERTDIR FIRST LAST` checks the parts
`FIRST, ..., LAST-1`, and `treecheck.py --combine OUTPUT...` adds up the outputs of such runs.

The checker regenerates the witnesses of each leaf with a floating-point heuristic and moves them towards the centres
of their bodies by the factor 1 - 2^-40. At a leaf with code `254` it first uses the coarser witness set (N = 256
directions, epsilon = 1e-5) and, if the checks fail, the finer one (N = 1024, epsilon = 1e-6). It then verifies in ball
arithmetic: membership of the witnesses in their bodies, the angular order of the witnesses on the whole box, the
angle sum at the centre, and the Taylor bound. At a leaf with code `253` it verifies membership, angular order and
angle sum for every fan of the side file. It rejects the leaf if a fan of positive weight fails them, skips the fans
of weight 0 that fail them, and verifies that the combination of the Taylor bounds of the other fans, with the
weights of the side file, exceeds the target. It also verifies the root box against the corner estimate and the
tree structure. Only the inequalities verified in ball arithmetic enter the proof. For each part the checker reports
the smallest difference between an accepted leaf bound and the target. Because the checker accepts a leaf at the
first witness set that passes, this difference is computed from the accepted bounds; another witness set may give a
larger bound at the same leaf. For `cert11d_08366` the smallest difference, 3.2e-11, occurs at a leaf closed with the
coarser witness set. If every leaf with code `254` of the part that contains this leaf is checked with both witness
sets and the larger bound is kept, the smallest difference in the part is 1.05e-6, at a leaf with code `253`. With the
environment variable `LBCHECK_SELFTEST=1` the checker also compares, at every leaf with code `254`, the area `F`
computed from runs of consecutive witnesses on one body with the direct shoelace sum.

## Lean proof (`formal/`)

The directory `formal/` holds the Lean project (`formal/lean/`), its build scripts and the generators of the certificate
modules (`formal/tools/`), and a `SHA256SUMS` for these files. Its `README.md` gives the statements, the trust base,
the build steps and the checks of four Lean 4 proofs, for the toolchain `leanprover/lean4:v4.35.0-rc3` and Mathlib
(tag `v4.35.0-rc3`):

| Proof (namespace) | Bound | Checks run | Cells | Leaves (combination leaves) | Generated modules | Build, single-threaded processes |
|---|---|---|---|---|---|---|
| `LebesgueCover.K3` | `M(D, B_3, B_5) >= 0.8347` | in the kernel | 1,024 | 25,214 (0) | 821 | about 200 hours, at most 10 GB per process |
| `LebesgueCover.K8` | `M(D, B_3, B_5, B_7) >= 0.836` | in the kernel | 65,536 | 278,093 (0) | 9,034 | about 1,440 hours, at most 14 GB per process |
| `LebesgueCover.K11` | `M(D, B_3, B_5, B_7, B_9) >= 0.8366` | in the kernel | 2,048 | 9,239,121 (5,599,347) | 406,888 | about 83,000 hours, at most 61 GB per process (241 GB for the root module) |
| `L11` | `M(D, B_3, B_5, B_7, B_9) >= 0.8366` | as compiled code (`native_decide`) | 2,048 | 9,239,121 (5,599,347) | 77,175 | about 940 hours |

Each proof also derives the bound for universal covers, in both readings of the problem: every set of diameter at most
1, or every convex set of diameter 1 (`main3K` and `weak_main3K` in `K3`, `mainK` and `weak_mainK` in
`K8`, `main5K` and `weak_main5K` in `K11`, `main5` and `weak_main5` in `L11`). The definitions and statements are in `formal/lean/LebesgueCover/Defs.lean` and `DefsK.lean`. The kernel-checked proofs
use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
The proof in `L11` also uses 75,061 auxiliary axioms of `native_decide`, one for each certificate module, which rest on
the Lean compiler and runtime.

All four proofs check certificates of their own, not the certificates in `certificates/`: trees in which the rotations
are given by the half-angle coordinates `s = tan(rho/2)`, whose leaves are closed by one fan or a convex combination of
fans, each bounded by an exact quadratic bound with an exact `LDL^T` factorization instead of the Taylor bound (Section
5.2 of the paper). `K11` uses the tree of `L11`; the search runs that produced this tree took about 3,600 CPU-hours.

The generated modules and their compiled `.olean` files are archived in the supplement, except the compiled files of
`K11` (about 238 GB), for which `k11_sums.tar.zst` lists the SHA-256 of every file of the build, so that a rebuild can
be compared file by file. Loading the shipped
`.olean` files prints the statements and axioms of the final theorems without a rebuild, but does not check their
proofs in the kernel again.

## Search

    cd search
    python3 lbbnb_v1.py 3,5 0.8347 1e-6 PART 16 4,4,4,4,4 OUTDIR                          # cert5d_08347, PART = 0..15
    python3 lbbnb_v2.py 3,5,7 0.836 1e-6 PART 24 4,4,4,4,4,4,4,4 OUTDIR                   # cert8d_0836, PART = 0..23
    python3 lbbnb_v4.py 3,5,7,9 0.8366 1e-6 PART 2048 2,2,2,2,2,2,2,2,2,2,2 OUTDIR        # cert11d_08366, PART = 0..2047

Run the drivers from `search/` without `-I`, because they import the module next to them. The arguments are the
Reuleaux polygons, the target, the search margin, the part, the number of parts, the grid and the output directory.
The search closes a box when its floating-point bound reaches the target plus the margin. `lbsearch_v4.py` also needs
SciPy and highspy (tested with 1.15) for the linear program that chooses the weights of a combination. Rerunning each
version on some parts of its certificate reproduced those parts byte for byte: for `cert5d_08347` and `cert8d_0836` on
the machine where they were made, and for `cert11d_08366` part 1618 on another machine. With other floating-point
libraries the output may differ, but any output is checked in the same way.

## Versions

Version 9 goes with the revised text of the paper, in which Theorem 1.1 states the two new bounds and the bound for
`D, B_3, B_5` is Proposition 4.2. The programs, certificates and Lean proofs are those of version 8; version 9 adds
`paper/main.tex`, `CHECKS.md`, `certificates/README.md` and `independent/README.md`. The comments in `formal/` use the
numbering of version 8, in which the bound for `D, B_3, B_5, B_7, B_9` is the third bound of Theorem 1.1.

## License

Apache License 2.0, see `LICENSE`.

## Citation

See `CITATION.cff`.
