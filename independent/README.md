# Programs written separately from the checker

The directory `independent/` holds programs written separately from the checker and the search. In their docstrings,
and in those of the checker and the search programs, "independent" means that a program shares no code with the
programs it checks. None of them imports either program, except the negative tests, which import
`checker/lbcheck.py` in order to test it. They need NumPy, SciPy (tested with 1.18), mpmath (tested with 1.4) and
python-flint, and each is run as `python3 FILE` with the arguments shown below.

| File | Purpose |
|---|---|
| `t1_tree.py CERTDIR LEAVES.npz` | exact decoder of the trees of the first two certificates; writes the leaf boxes |
| `v1_leafcheck.py LEAVES.npz TAU OUT.json IDX ...` | second verifier of leaves of the `D, B_3, B_5` certificate |
| `v8_leafcheck.py LEAVES.npz TAU OUT.json IDX ...` | the same for `D, B_3, B_5, B_7` (uses `gen8.py`) |
| `v2_validate.py`, `v8_validate.py` | comparison of the two verifiers with brute force on a few leaves |
| `h1_hull.py`, `gen8.py` | hull areas from the support functions (`D, B_3, B_5` and `D, B_3, B_5, B_7`) |
| `h2_minsearch.py`, `h8_minsearch.py` | hull areas at leaf centres and local minimization |
| `opt8_point.json` | the placement of `D, B_3, B_5, B_7` found by local minimization, in full precision (hull area 0.83649045598 by `gen8.area`), together with the values of `gen8.area` and `gen8.poly_bounds` at that placement |
| `gen11.py` | the same hull areas for `D, B_3, B_5, B_7, B_9` (imports `gen8.py`) |
| `c11_centres.py CERTDIR FIRST LAST OUT.jsonl` | hull areas at all leaf centres of the parts `FIRST, ..., LAST-1` of `cert11d_08366` |
| `p11_polish.py STARTS.json I0 I1 OUT.jsonl` | local minimization for `D, B_3, B_5, B_7, B_9` from the starts `I0, ..., I1-1` of a list (Nelder-Mead restarts, then Powell) |
| `p11_restarts.py X.json SEED NREST OUT.jsonl` | random restarts around a local minimum, each followed by the same minimization |
| `opt11_point.json` | the placement of `D, B_3, B_5, B_7, B_9` found by local minimization, in full precision (hull area 0.83729500640 by `gen11.area`), with `gen11.poly_bounds` and the polygon areas of `search/area_bracket.py` with 2^24 directions at that placement |
| `l1_lemmas.py` | numerical checks of the reduction lemmas |
| `n1_negative.py`, `n8_negative.py` | negative tests of the checker on the first two certificates |
| `n11_negative.py CERTDIR OUTDIR` | negative tests on the third certificate: modified copies of part 1618 (root, header, tree and side file); run `checker/lbcheck.py OUTDIR/T... 1618` on each |
| `t11_leaf_near_min.py CERTDIR X.json TAU` | runs the checker's leaf test on the leaf of the third certificate that contains the placement `X`, at the certificate's target and at `TAU` |
| `xstar_min11.json` | a placement of `D, B_3, B_5, B_7, B_9` near the numerical minimum |
| `m11_multistart.py NSTART SEED OUT.jsonl` | multistart Nelder-Mead for `D, B_3, B_5, B_7, B_9` from the placement of `opt8_point.json` extended by `B_9` and from random starts |
| `samples/` | leaf indices of the samples verified by the separate verifiers of the first two certificates (`strata_*.json` lists the strata), and `stage1_11d.npz` (the leaves of a sample of the third certificate, drawn by `v11/v11_sample.py` with seed 20261021 and verified before the full run) with the results `stage1_11d.jsonl` |
| `v11/` | the verifier and decoder for the third certificate, with its own `SHA256SUMS`: `v11_leafcheck.py` (leaf verifier), `gen11.py` (its hull geometry; not the same file as `independent/gen11.py`), `treedec11.py` (exact decoder with integer boxes), `v11_sample.py` (draws a sample), `v11_run.py` (runs the verifier on a sample), `box_run11.py` (runs it on all leaves of given parts) and the self-tests `test_*.py` |
| `full11/` | the run of the second verifier on all leaves of `cert11d_08366`; see `../CHECKS.md` |

The verifiers bound the area `F` of the witness polygon on a box without a Taylor remainder. They use neither the
Taylor bound (Lemma 3.5 of the paper) nor the combination bound (Lemma 3.8). The verifier in `v11/` also handles the
leaves with code `253`: it builds the fans of positive weight from the sign vectors and weights of the certificate,
verifies them on the leaf, and bounds their combined area in the same way, which uses only the inequality
`A >= sum_i kappa_i F_i` from the proof of Lemma 3.8. For fixed rotations,
`F` and the determinants that encode the angular order are affine in each translation coordinate, so their minima lie
at vertices of the box of translations, and their minima over the rotations are bounded from below in ball
arithmetic.

Earlier versions of the verifier in `v11/`, with a looser fallback bound for the minima over the rotations, had failed
at some leaves of the sample in `samples/stage1_11d.npz`; the version in `v11/` verified all of them.

`box_run11.py CERTDIR PARTS OUTDIR WORKERS` expects the other files in a subdirectory `v11/` next to it, so copy
`box_run11.py` into `independent/` before running it. `PARTS` is a file with part numbers. Example:

    python3 -I independent/t1_tree.py certificates/cert5d_08347 leaves5.npz
    python3 -I independent/v1_leafcheck.py leaves5.npz 0.8347 v1.json $(cat independent/samples/sample_5d.txt independent/samples/tight_5d.txt)
    python3 -I independent/n1_negative.py certificates/cert5d_08347 leaves5.npz negative_work
    python3 -I independent/v11/v11_run.py independent/samples/stage1_11d.npz stage1_rerun.jsonl 8

## Tests of the checker

| | `cert5d_08347` | `cert8d_0836` | `cert11d_08366` |
|---|---|---|---|
| checker's leaf test at the leaf near a numerical minimizer | passes 0.8347, fails 0.8348 | passes 0.836, fails 0.8365 | passes 0.8366, fails 0.8374 |
| modified root, header, tree or side file | 8 of 8 rejected | 2 of 2 (root) rejected | 7 of 7 rejected |
