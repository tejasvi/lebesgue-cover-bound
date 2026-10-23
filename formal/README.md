# Lean formalization of lower bounds for Lebesgue's universal covering problem

This directory contains a Lean 4 + Mathlib development with three proofs of lower bounds for the area of universal
covers in the plane:

- **Λ ≥ 0.8366**, through M(D, B₃, B₅, B₇, B₉) ≥ 0.8366: the least area of the convex hull of congruent copies of the
  disk of diameter 1 and the regular Reuleaux triangle, pentagon, heptagon and nonagon of width 1. Its certificate is
  checked by compiled evaluation (`native_decide`).
- **Λ ≥ 0.836**, through M(D, B₃, B₅, B₇) ≥ 0.836 (disk, triangle, pentagon and heptagon).
- **Λ ≥ 0.8347**, through M(D, B₃, B₅) ≥ 0.8347 (disk, triangle and pentagon).

The certificates of the last two proofs are checked by the Lean kernel (`decide +kernel`). Their trusted base is Lean's
kernel, including the kernel's built-in arithmetic on natural numbers, and they use only the three standard axioms.

The three proofs share the definitions, the soundness of the leaf check, the tree lemmas, the vertex tables, the
far-region argument and the reduction of arbitrary isometries to placements in a root box.

## Statements and final theorems

The definitions and statements are in `lean/LebesgueCover/Defs.lean`:
- the plane `EuclideanSpace ℝ (Fin 2)` with Lebesgue measure, and the bodies `disk` and `reuleaux n`;
- universal covers (`IsUniversalCover`: every set of diameter at most 1 has a congruent copy inside, reflections
  allowed), and the Lebesgue constant `lebesgueConstant`, the infimum of the areas of universal covers;
- the weakest reading `IsWeakUniversalCover`: copies of every convex set of diameter exactly 1;
- the hull infima `hull3`, `hull4` and `hull5`;
- the propositions `Hull3Statement`, `Hull4Statement`, `Hull5Statement`, `MainStatement`, `WeakMainStatement` (the two
  readings of Λ ≥ 0.836), `Main5Statement` and `WeakMain5Statement` (the two readings of Λ ≥ 0.8366).

`lean/LebesgueCover/DefsK.lean` adds `Main3Statement` and `WeakMain3Statement`, the two readings of Λ ≥ 0.8347.

The final theorems of the 0.8366 proof are in the generated module `L11/Root11Good.lean` (namespace `L11`; a copy is
in `final/Root11Good.lean`):

```lean
theorem hull5_ge : Hull5Statement             -- M(D, B₃, B₅, B₇, B₉) ≥ 0.8366
theorem main5 : Main5Statement                -- Λ ≥ 0.8366
theorem weak_main5 : WeakMain5Statement       -- the same for every weak universal cover
theorem main_836 : MainStatement              -- Λ ≥ 0.836
theorem weak_main_836 : WeakMainStatement
```

For each of these five, `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` and 75,061 axioms named
`L11.<module>.ok._native.native_decide.ax_1_1`, one for each certificate module (2,048 cell modules `B<c>` and 73,013
subtree modules `S<c>_<k>`). There is no `sorry` and no other axiom.

The final theorems of the 0.836 proof are in the generated module `LebesgueCover/K8/Root4Good.lean` (namespace
`LebesgueCover.K8`; a copy is in `final/Root4Good.lean`):

```lean
theorem hull4_geK : Hull4Statement            -- M(D, B₃, B₅, B₇) ≥ 0.836
theorem mainK : MainStatement                 -- Λ ≥ 0.836
theorem weak_mainK : WeakMainStatement        -- the same for every weak universal cover
```

The final theorems of the 0.8347 proof are in the generated module `LebesgueCover/K3/Root3Good.lean` (namespace
`LebesgueCover.K3`; a copy is in `final/Root3Good.lean`):

```lean
theorem hull3_geK : Hull3Statement            -- M(D, B₃, B₅) ≥ 0.8347
theorem main3K : Main3Statement               -- Λ ≥ 0.8347
theorem weak_main3K : WeakMain3Statement      -- the same for every weak universal cover
```

For each of the six theorems of these two proofs, `#print axioms` gives exactly `propext`, `Classical.choice` and
`Quot.sound`. `MainStatement` and `WeakMainStatement` therefore have two proofs: `main_836` and `weak_main_836` use
compiled evaluation; `mainK` and `weak_mainK` do not.

## Trust base

Each `native_decide` auxiliary of the 0.8366 proof states `decide p = true` for the proposition `p` of one certificate
module: a run of the compiled leaf checker and tree walker on that module's data. It is justified by evaluating `p`
with compiled code instead of the kernel, so `native_decide` trusts the Lean compiler and runtime for these
evaluations. The 0.836 and 0.8347 proofs have no such step: the kernel evaluates their leaf checks and tree walks
(`decide +kernel`).

Everything else is checked by the kernel with the three standard axioms, in all three proofs:
- the soundness of the fast leaf checker `LebFast/Exact.lean` with respect to the reference leaf checker
  (`LebesgueCover/FastBridge.lean`; the reference checker is in `Checker.lean`, `Sound.lean`, `Quad.lean`, `Rot.lean`),
  and of the reference checker with respect to the geometric conclusion "every placement in the box has hull area > τ"
  (`Fan.lean`, `FanLeaf.lean`);
- the tree, cell, block and grid lemmas: the root cells cover the root box (`TreeSound.lean`; for the kernel-checked
  certificates also `TreeK.lean`);
- the tables of Reuleaux vertices, from trigonometric enclosures evaluated in the kernel (`Trig/`, `VertTable.lean`);
- the far region, by a kernel-checked polygon and a corner bound (`Far.lean`; data in `Far11Data.lean`,
  `Far8Data.lean` and `Far5Data.lean`);
- the reduction of arbitrary isometries to placements in the root box: the plane as ℂ, the isometries of ℂ, the
  symmetries of the bodies, and half-angle rotation coordinates (`Reduce.lean`, `Main5.lean`, `Main4.lean`,
  `Main3.lean`). For the 0.836 proof, `Main4.lean` also rotates whole placements by multiples of 2π/3 (see
  Certificates);
- the diameters of the bodies and the passage from the hull bounds to the two readings of Λ (`Diam.lean`,
  `Main3.lean`).

In the 0.836 proof, the support points of each leaf are written as one natural number. The kernel decodes it inside the
leaf check (`LebK/Decode.lean`). The soundness of the leaf check holds for every list of support points, so the decoder
needs no proof of its own.

The certificate data were produced with floating-point heuristics:
- for the 0.8366 proof, by the compiled checker at check time (`LebFast/Heur.lean`);
- for the 0.836 and 0.8347 proofs, offline, and then written into the modules (`tools/gen/`).
The soundness theorems hold for arbitrary data, so these heuristics are not part of the trust base. Neither are the
branch-and-bound searches that produced the trees.

## Contents

- `lean/`: the Lake project.
  - The 38 Lean files of the development, and `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
  - `tools/K3Axioms.lean` and `tools/K8Axioms.lean`: print the axioms of the 0.8347 and 0.836 finals.
  - Two optional tool programs, `tools/HeurTest.lean` and `tools/LeafBench.lean`. They are development programs, not
    part of any proof.
  - `LebesgueCover/` is the Mathlib development listed above.
  - `LebFast/` is the fast checker in core Lean (`Heur`, `Model`, `Exact`, `Driver`, `Tree`, `VT`, and `Root11` with
    the 11D root box), compiled for `native_decide`.
  - `LebK/` holds core-Lean files of the kernel-checked certificates: the root boxes `Root3.lean` (5D) and `Root4.lean`
    (8D), and the decoder `Decode.lean`.
- `final/Root11Good.lean`, `final/Root4Good.lean`, `final/Root3Good.lean`: copies of the three modules with the final
  theorems (also in `l11_sources.tar.zst`, `k8_sources.tar.zst` and `k5_sources.tar.zst`).
- `tools/`:
  - for the 0.8366 proof: `build_l11.sh` and `final_l11.sh` (build); `mkblocks3.py` and `mkroot11.py`, the generators
    of the `L11` modules (`mkroot11.py` reproduces `C*.lean` and `Root11Good.lean` exactly); `count_l11.py` (counts);
  - for the 0.836 proof: `build_k8.sh` (build); in `gen/k8/` (optional), the generator `mkk8.py`, its root box
    `header_k8.json`, and `mkroot8.py`, which reproduces `Root4Good.lean` exactly;
  - for the 0.8347 proof: `build_k5.sh` (build); in `gen/k5/` (optional), the generator `mkk5.py` with its root box
    `header_k5.json`;
  - in `gen/`, used by both kernel-checked proofs: the branch-and-bound search `s_search3k.py` and the floating-point
    pipeline it and the generators use (`leafbound.py`, `s_eval.py`, `s_search.py`, `export_test.py`, `exact.py`).
    These scripts need the paper's `checker/` directory (`lbcheck.py`) in `LEBESGUE_CHECKER` or at
    `tools/gen/checker`.
  - `mkk8.py` and `mkk5.py` reproduce the glue modules (`LebesgueCover/K8/*.lean`, `LebesgueCover/K3/*.lean`) exactly
    from the search output. The leaf data they compute can differ in the last bits of support points between
    floating-point environments, and the kernel checks every such variant all the same.
  - The search that produced the 11D tree is not included; no search is needed to check any of the proofs.
- Six archives distributed with this directory:
  - `l11_sources.tar.zst`: the 77,175 generated modules of the 0.8366 proof under `L11/` and their `SHA256SUMS_lean`:
    - `B<c>` (cell `c`, with its subtrees above a fixed size delegated) and `S<c>_<k>` (the delegated subtrees, at most
      2,997 leaves, almost all at most 600): the certificate, checked by `native_decide`;
    - `G<c>`: per-cell glue (`block_good`);
    - `C<k>`: 64 chunks of 32 cells;
    - `Root11Good`: the root box and the final theorems;
    - `AxL11`: prints the axioms of the finals.
  - `l11_oleans.tar.zst`: the compiled `.olean` files of these modules (toolchain `v4.35.0-rc3`) and their
    `SHA256SUMS_olean`. They let one check the final theorems without the roughly 940 hours of compiled evaluation
    (`native_decide`).
  - `k8_sources.tar.zst`: the 9,034 generated modules of the 0.836 proof (paths relative to this directory) and the
    search output, with their manifest `SHA256SUMS_k8`:
    - `lean/LebK/L8/L<j>_<m>.lean`, 8,777 modules: the leaves, at most 32 per module. Each leaf has its box, its
      support points (one packed natural number), fan centre, `β`, `σ`, and the theorem `ok : leafOKF … = true`
      proved by `decide +kernel`;
    - `lean/LebesgueCover/K8/G000.lean` … `G255.lean`: the tree walks of the cells (units of at most 32 delegated
      leaves or sub-units, each checked by `decide +kernel`) and one chunk theorem per 256 grid cells;
    - `lean/LebesgueCover/K8/Root4Good.lean`: the root box and the final theorems;
    - `tools/gen/k8/s1/`: the search output (one code array per cell), the input of `mkk8.py`.
  - `k8_oleans.tar.zst`: the `.olean` files of these 9,034 modules and of the five library modules of this proof
    (`LebK/Root4`, `LebK/Decode`, `LebesgueCover/Far8Data`, `Main4`, `K8Base`) under `k8_oleans/`, with their
    `SHA256SUMS_k8_olean`. They let one inspect the 0.836 finals without the roughly 1,440 hours of kernel checking.
  - `k5_sources.tar.zst`: the 821 generated modules of the 0.8347 proof (paths relative to this directory) and the
    search output, with their manifest `SHA256SUMS_k5`:
    - `lean/LebK/L/L0000.lean` … `L0787.lean`: the leaves, 32 per module. Each has its box, support points, fan centre,
      `β`, `σ`, and the theorem `ok : leafOKF … = true` proved by `decide +kernel`;
    - `lean/LebesgueCover/K3/G00.lean` … `G31.lean`: the tree walks of the cells (units of at most 32 delegated leaves
      or sub-units, each checked by `decide +kernel`) and one chunk theorem per 32 grid cells;
    - `lean/LebesgueCover/K3/Root3Good.lean`: the root box and the final theorems;
    - `tools/gen/k5/s1/`: the search output (one code array per cell), the input of `mkk5.py`.
  - `k5_oleans.tar.zst`: the `.olean` files of these 821 modules under `k5_oleans/`, with their
    `SHA256SUMS_k5_olean`. They let one inspect the 0.8347 finals without the roughly 200 hours of kernel checking.

## Certificates

The 0.8366 root box has 11 coordinates: the translations of the four Reuleaux polygons relative to the disk, and the
rotations of the pentagon, heptagon and nonagon relative to the triangle, in half-angle coordinates s = tan(ρ/2).
These coordinates and this root box differ from those of the certificate in the paper: the Lean proof checks a
separate tree, built for the leaf model formalized here. The root box is split into 2,048 cells by one bisection per
coordinate. Each cell carries a binary tree. A leaf is closed either by one fan (a polygon of support points with a
quadratic lower bound of its area on the leaf box) or by a convex combination of several fans. In total there are
9,239,121 leaves (3,639,774 single-fan and 5,599,347 combination leaves) and 18,476,194 nodes.

The 0.836 root box has 8 coordinates: the translations of the triangle, pentagon and heptagon, and the rotations of
the pentagon and the heptagon relative to the triangle.
- The rotations are s₂ = tan(ρ₂/2) ∈ [0, 6889/65536] and s₃ = tan(ρ₃/2) ∈ [0, 1973/4096]. The bound 6889/65536 is at
  least tan(π/30), so ρ₂ ranges over [0, π/15]. This suffices because the rotation by 2π/3 about the centre of B₃
  maps B₃ to itself. Rotating a whole placement by 2π/3 about the centre of the disk therefore gives a placement in
  which the triangle is again unrotated, the translations have the same lengths, and the pentagon's rotation is
  shifted by 2π/3. Together with the reflection, this reduces the pentagon's rotation to a third of the range that its
  own symmetries allow.
- The translations range over [−Tᵢ, Tᵢ]² with T = (3351629/2²⁴, 423263/2²¹, 421033/2²¹). These are the bounds of the
  paper's certificate for M(D, B₃, B₅, B₇) enlarged by 0.4%, so that the far polygon closes the complement (area
  0.83617 > 0.836).
- The root box is split into 65,536 cells by two bisections per coordinate. Every leaf of the cell trees is closed by
  one fan: 278,093 leaves, each with its data written out.

The 0.8347 root box has 5 coordinates: the translation of the triangle, and the rotation (s = tan(ρ/2) ∈ [0, 333/1024])
and translation of the pentagon. The translations range over [−T₁, T₁]² and [−T₂, T₂]² with
T = (3267777, 3322521)/2²⁴, slightly larger than the bounds of the paper's 5D certificate, so that the far polygon
closes the complement (area 0.834955 > 0.8347). The root box is split into 1,024 cells by two bisections per
coordinate, and every leaf of the cell trees is closed by one fan: 25,214 leaves.

The two kernel-checked proofs use the leaf model and the checker `leafOKF` of the 0.8366 proof.

## Build

Requirements: `elan` with the toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib at tag `v4.35.0-rc3`
(commit c55e6e786f49), `zstd`.

```sh
cd lean
lake exe cache get                     # prebuilt Mathlib
lake build LebFast LebesgueCover LebK  # the base development, the compiled checker libraries, the root boxes
```

Run this base build before unpacking any of the archives below. After the generated modules of a kernel-checked proof
are unpacked into `lean/`, the globs of `lakefile.toml` include them, and a later `lake build` compiles them as well.

The 0.8366 proof:

```sh
mkdir -p blocks && zstd -dc /path/to/l11_sources.tar.zst | tar -xf - -C blocks
(cd blocks/L11 && sha256sum -c --quiet SHA256SUMS_lean)
bash ../tools/build_l11.sh 64          # certificate and glue modules
bash ../tools/final_l11.sh 32          # chunks, the final theorems, and their axioms
```

`build_l11.sh` compiles the `B` and `S` modules with the compiled checker libraries loaded through `--load-dynlib`. That
takes about 0.37 s per leaf, about 940 hours of single-threaded processes in total, so a few thousand cores take about
an hour. It then compiles the `G` modules. `final_l11.sh` compiles the chunks and `Root11Good` (about 20 s and 10 GB for
the root module) and writes the axioms to `blocks/logs_final/axioms.txt`.

The 0.836 proof:

```sh
bash ../tools/build_k8.sh /path/to/k8_sources.tar.zst 60
```

`build_k8.sh` unpacks the generated modules into `lean/` (and the search output into `tools/gen/k8/s1/`) and checks
`SHA256SUMS_k8`. It compiles every module in its own single-threaded `lean` process: the 8,777 leaf modules, NPAR at a
time, then the 256 chunk modules, then `Root4Good`. Finally it prints the axioms of the finals (`tools/K8Axioms.lean`).
- The leaf modules take about 1,440 hours of single-threaded processes in total: a median of about 9 minutes per
  module, up to 43 minutes, and a median of 3.7 GB per process, up to 14 GB.
- The chunk modules take about 5 hours in total, up to 13 GB each. `Root4Good` takes 10 s.
- On several machines, `SHARD=i NSHARD=n` compiles every n-th leaf module. Collect the leaf `.olean` files on one
  machine and finish there with `SKIP_LEAVES=1` (see the script's header).

The 0.8347 proof:

```sh
bash ../tools/build_k5.sh /path/to/k5_sources.tar.zst
```

`build_k5.sh` unpacks the generated modules into `lean/` (and the search output into `tools/gen/k5/s1/`), checks
`SHA256SUMS_k5`, runs `lake build LebesgueCover.K3.Root3Good` and prints the axioms of the finals
(`tools/K3Axioms.lean`).
- The 788 leaf modules take about 200 hours of single-threaded processes in total, 20 to 70 s per leaf. With 60
  processes on 60 cores, the build took about 4 hours, with up to about 2.3 GB per process.
- The glue modules take minutes, up to about 10 GB for the largest.

To inspect the final theorems from the shipped `.olean` files instead, unpack them after the base build and print the
axioms. This reads the declarations as compiled and does not re-run the kernel on them; checking them again needs a
kernel replay of the `.olean` files. The `L11` modules have their own root and go to a separate directory. The
generated modules of the two kernel-checked proofs share the roots `LebK` and `LebesgueCover` with the development, so
their `.olean` files go into the project's build directory.

```sh
mkdir -p blocks/build && zstd -dc /path/to/l11_oleans.tar.zst | tar -xf - -C blocks/build
(cd blocks/build/L11 && sha256sum -c --quiet SHA256SUMS_olean)
LEAN_PATH=$(lake env printenv LEAN_PATH):$PWD/blocks/build lean blocks/L11/AxL11.lean

zstd -dc /path/to/k8_oleans.tar.zst | tar -xf - --strip-components=1 -C .lake/build/lib/lean
(cd .lake/build/lib/lean && sha256sum -c --quiet SHA256SUMS_k8_olean)
lake env lean tools/K8Axioms.lean

zstd -dc /path/to/k5_oleans.tar.zst | tar -xf - --strip-components=1 -C .lake/build/lib/lean
(cd .lake/build/lib/lean && sha256sum -c --quiet SHA256SUMS_k5_olean)
lake env lean tools/K3Axioms.lean
```

## Checks

`SHA256SUMS` lists every file of this directory; the six archives carry their own manifests.

The modules of the 0.8366 proof were also re-checked separately:
- all 77,201 modules of the closure were replayed in the kernel;
- a seeded 2% sample of the certificate modules, rebuilt with a second build of the compiled checker from the same
  sources, is byte-identical to the original build;
- the statements and axioms of the five final theorems were confirmed.

The two kernel-checked proofs were re-checked separately as well, each on another machine:
- 0.836: Mathlib and the library side were built again from source, and the Lean kernel replayed every module of
  the shipped `.olean` files. All 9,039 were accepted: the 8,777 leaf modules with their 278,093 leaf checks, the
  256 chunk modules, `Root4Good` and the five library modules of this proof (about 1,830 thread-hours). No module
  stores an axiom. The five library modules built there are byte-identical to the shipped ones, and a seeded sample
  of 176 leaf modules, 26 chunk modules and `Root4Good`, compiled again from these sources with the command of
  `build_k8.sh`, is identical to the shipped `.olean` files, constant by constant and byte for byte.
- 0.8347: all 821 generated modules were rebuilt from these sources, so the kernel checked every declaration again,
  including the 25,214 leaf checks (about 136 hours of single-threaded processes). The rebuilt `.olean` files have
  the same imports and constants as the shipped ones. 78 modules were replayed in the kernel: the final module, the
  32 glue modules, the library modules of this proof and 40 seeded leaf modules.
- For each of the two proofs, exports of the lemmas that turn the certificate into the final theorems, of one cell
  unit and of one leaf module with their computations were checked outside the build. leanchecker (Lean's kernel,
  run on an exported file) and lean4lean (an independent implementation of the kernel) accepted all three. nanoda
  (another independent implementation) accepted the first and stopped on the leaf computations at a stack limit.
- Altered inputs were rejected: for both proofs a swapped proof and a leaf with a false claim, and for the 0.836
  proof also a leaf with one changed digit of its packed support points. The statements and axioms of the final
  theorems of both proofs were confirmed.
