# Checks recorded in this release

This file holds the record of the second verifier's run on all leaves of `cert11d_08366` and the size and SHA-256 of
every archive in the supplement (doi:10.5281/zenodo.23717912). `README.md` describes the programs; `formal/README.md`
describes the Lean proofs and their checks.

## Run of the second verifier on all leaves of `cert11d_08366` (`independent/full11/`)

The second verifier verified all 16,193,402 leaves of `cert11d_08366`: a first pass with the verifier of `v11/`, and
two variants of it for the leaves that the first pass did not verify (the pass-1 leftovers below). The directory `full11/` has the layout of the
directory in which these runs were made, so that the accounting program `pass23/final11.py` runs unchanged. Apart from
`full11_pass1.sha256`, every file in it is a copy of a file of that directory.

| Pass | Program | Leaves verified |
|---|---|---|
| 1 | `v11_frozen_8b878f23/v11_leafcheck.py` (the files of `v11/`), bisection of a leaf to depth 4 | 16,191,196 |
| 2 | `v11bc_frozen_12dd7362/v11b_leafcheck.py`: pass 1, with each witness list also tried without the runs of witnesses on one body whose removal decreases the fan area at the point where the fan is built by less than 1e-5 or 1e-4, and bisection to depth 6 | 228 |
| 3 | `v11bc_frozen_12dd7362/v11c_leafcheck.py`: its own fans and weights; fans from the hull at the centre `c`, at the points `c + s * h` of the side file (leaves with code `253`) and at minimizers of the current combination, with witness lists filtered as in pass 2 (1e-5), each verified on the whole leaf; weights from a cutting-plane linear program (SciPy); the combined area bounded as in pass 1; bisection to depth 5 | 1,029 |
| 3d | `v11d_frozen_888b6867/v11c_leafcheck.py`: pass 3 with one fix: when the cutting-plane loop has converged to an optimum below the target, it adds a fan at the minimizer instead of stopping | 949 |

Pass 1 ran on all 2,048 parts with `box_run11.py`, spread over 43 servers. It took 3,959.7 CPU-hours (0.88 s per leaf)
and split 11,046 leaves. Of these, 8,840 then passed, and the other 2,206, the pass-1 leftovers, all failed at
depth 4. They were decoded into
`pass23/fails_a.npz`, `fails_b.npz`, `fails_c1.npz` and `fails_c2.npz`, in the order in which the results of pass 1
came in, and run through the later passes with `pass23/run_pass.py`. Pass 2 ran on 367 leaves of `fails_a`, pass 3 on
the 1,042 leaves of `fails_a` left over by pass 2 (`pass23/logs_p2/pass3_a_idx.txt`), and pass 3d on the 13
leaves left over by pass 3 (`pass23/logs_p2/pass3d_a_idx.txt`) and on the leaves listed in `fails_b_idx.txt`,
`fails_c1_idx.txt` and `fails_c2_idx.txt`. In all passes together, 9,018 leaves passed only after a split (8,840 in pass 1,
136 in pass 2, 35 in pass 3 and 7 in pass 3d). The smallest margins (bound minus 0.8366) were 6.8e-9 in pass 1 (part 691) and 3.6e-7 in the later passes
(part 1715); the output files hold the exact values. The programs and their output call a combination of fans
"Lemma K"; they use only the inequality `A >= sum_i kappa_i F_i` and bound the combined area as above.

| File | Content |
|---|---|
| `v11_frozen_8b878f23/`, `v11bc_frozen_12dd7362/`, `v11d_frozen_888b6867/` | the programs of the passes, each with its own `SHA256SUMS`; each name ends with the first hexadecimal digits of the SHA-256 of a program in it: `v11_leafcheck.py` for `v11_frozen_8b878f23`, `v11c_leafcheck.py` for `v11bc_frozen_12dd7362`, and the corrected `v11c_leafcheck.py` for `v11d_frozen_888b6867` |
| `treedec11_all.json` | the output of the exact decoder `treedec11.py` on all parts (leaf counts per part and code, structural checks) |
| `pass23/fails_*.json`, `pass23/fails_*.npz` | the pass-1 leftovers, as `[part, pos, tag]`, and their exact boxes and side data, written by `v11_sample.py` with the list as targets and no random leaves (it also adds the 33 far leaves) |
| `pass23/fails_*_idx.txt` | the indices of these leaves in the `.npz` files |
| `pass23/run_pass.py PASS CODEDIR LEAVES.npz OUT.jsonl WORKERS [IDXFILE]` | runs pass 2 (`PASS` = 2) or pass 3 (`PASS` = 3) with the programs in `CODEDIR` on the leaves of `LEAVES.npz` or on those listed in `IDXFILE`; pass 3d is pass 3 with `CODEDIR` = `v11d_frozen_888b6867` |
| `pass23/results/pass*.jsonl` | the output of the later passes, one line per leaf; the `.meta` files hold the SHA-256 of the programs that were run |
| `pass23/final11.py` | the accounting program |
| `pass23/FINAL11.json` | its output: `"ALL 16193402 LEAVES VERIFIED"`, 0 unresolved leaves, 0 problems |
| `full11_pass1.sha256` | SHA-256 of `full11_pass1.tar.xz` (116,500,532 bytes), the output of pass 1, which is archived only in the supplement |

The output of pass 1 has one directory per server, renamed `box01`, ..., `box43` for this release, with
`partNNNN.json` (leaf counts, SHA-256 of the input files and of the programs, the leaves not verified, the smallest
margin, CPU time) and `partNNNN_margins.npy` (the margin of each leaf in the order of the decoder, NaN for a leaf not
verified) for each part. `final11.py` checks that every part has a pass-1 result (the archive holds exactly one per part), that its input files have
the SHA-256 listed in the `SHA256SUMS` of the certificate, that the pass-1 programs have the SHA-256 of the files in
`v11_frozen_8b878f23/`, that the leaf counts equal those of `treedec11_all.json` and that every leaf has a result. It
then checks that every pass-1 leftover was verified by a later pass. It matches each result to its leaf
in the `fails_*.npz` files by part and position, and it compares the SHA-256 in the `.meta` files with the programs in
the corresponding directory. The later passes read their leaves from the `fails_*.npz` files, which `v11_sample.py`
decoded from the certificate; `final11.py` does not decode the certificate again. To rerun it, extract `cert11d_08366`
into `certificates/` as above, download `full11_pass1.tar.xz` into `independent/full11/`, and run, from the top
directory of the repository,

    ln -s ../certificates/cert11d_08366 independent/cert11d_08366
    cd independent/full11
    sha256sum -c full11_pass1.sha256
    tar -xJf full11_pass1.tar.xz           # fleet11/results/box01, ..., box43, each with a file DONE
    python3 -I pass23/final11.py
    sha256sum pass23/FINAL11.json

`final11.py` reads only the file `SHA256SUMS` of the certificate. It rewrites `pass23/FINAL11.json`, which should then
be byte-identical to the file in this repository (SHA-256 `abf4552b8a9a77f6f9bb3c25d80b31f9d06592a4ab0193fbac34027b1643d00c`).

## Sizes and checksums of the archives

The supplement holds the archives below (its `SHA256SUMS` lists their SHA-256). Check each archive against this table, or against
that `SHA256SUMS`, before unpacking it. Each `.tar.xz` or `.tar.zst` file decompresses to the `.tar` file of the same name. Each certificate archive holds one directory with the certificate files and their `SHA256SUMS` file. The archive `full11_pass1.tar` holds the directory `fleet11/results`. The two archives of the 0.8366 proof hold the directory `L11`; those of the 0.8347 proof hold the directories `lean` and `tools` (laid out as in `formal/`) and the directory `k5_oleans`; those of the 0.836 proof likewise hold the directories `lean` and `tools` and the directory `k8_oleans`. The `k11_sources` files are uncompressed tar files that hold the per-cell archives in the directory `k11_sources`; `k11_glue.tar` holds the directory `k11_glue` and `k11_sums.tar` the directory `k11_sums`.

| File | Bytes | SHA-256 |
|---|---|---|
| `cert11d_08366.tar.xz` | 293,113,544 | `6b5d28bc488edcfde9c6a49f3cb364f9086f445a58f85f166da23727036cf122` |
| `cert11d_08366.tar` | 1,455,994,880 | `a65f5b3827e9fe63ab56f16d460a99901fc7b447eeca50642e5858c838829dc9` |
| `full11_pass1.tar.xz` | 116,500,532 | `0cf9696eb47681382492bc547d44519beeb69f492ee0cf26c520ec8254e1562b` |
| `full11_pass1.tar` | 136,693,760 | `dad0ce35a5afa73f58daeb3647431365b181d98c42d8e49c029da0c09e727543` |
| `l11_sources.tar.zst` | 133,521,541 | `acb85d373917295c26f77acd2b2144c2f47256fcc6d9418dface3ff78c00133a` |
| `l11_sources.tar` | 504,657,920 | `c99ec9899a240055f7eacff538d7c621c1da963e7dbaa9174280c660cc33e6c2` |
| `l11_oleans.tar.zst` | 481,071,638 | `9a356edf6e801783658a296ebe9f52430212006e4ee700c3be5a1b285f12dbab` |
| `l11_oleans.tar` | 2,282,117,120 | `7da4d1581c5819d2bc74d44f6a043658ced869b76651fc134470cfb24a38fd0a` |
| `k5_sources.tar.zst` | 10,869,411 | `31a2058b782dab1dd5131267bf5a7e075bc343e963703bf684e1ed0c01235f4c` |
| `k5_sources.tar` | 582,707,200 | `634efaabeb9dd805374dab2d6a9ee6bfd68a4e714914958bd264e9316da34f30` |
| `k5_oleans.tar.zst` | 3,568,240,020 | `0caa58bf3ac7f5494053fe948dac88b16d08147c7a55e8334057196357e683e6` |
| `k5_oleans.tar` | 19,179,048,960 | `56af103be2008cf4fed2aee83cdae276bf988a8333d54aa2264057a81b591487` |
| `k8_sources.tar.zst` | 1,155,309,716 | `3a0ff3ea18eb81b481f8a513ba632304af503f6140dfad6479317ec708491191` |
| `k8_sources.tar` | 3,117,680,640 | `107fcd787ee7aaf17cddb572627139a2fe4c8127ea7db3054ff637991eb9b7e5` |
| `k8_oleans.tar.zst` | 936,081,748 | `42091e9314c44daae000798e1bfb85365e00cc22bbb0a6ba73053f5535c5a70e` |
| `k8_oleans.tar` | 4,578,611,200 | `5b782236ab68c01a49c39fe07ec7742d081e8ca445d4eadba203a20865afaac3` |
| `k11_sources_00.tar` | 1,999,370,240 | `4988f043abee0d3fe56ac1c71299b744f9e3b177ae364aec6c03d6fa4fee56fd` |
| `k11_sources_01.tar` | 1,953,228,800 | `cff7f14964da43e6377e91c2c6edf36e1a56cd4109e1bb6fcb7c974efb78805d` |
| `k11_sources_02.tar` | 1,990,543,360 | `594a71631da0b1d9350713bdee8ebe22f26de92cd82381151b05632bde79491d` |
| `k11_sources_03.tar` | 1,974,435,840 | `9fc4e2e23a52438d4414b362fd538c7d49359da2e745308ad940aabc1a8834b9` |
| `k11_sources_04.tar` | 1,993,533,440 | `56990cdf03f34efa25d3b27e8be77a6c04ac062bdb789a4388585ce37a46c59a` |
| `k11_sources_05.tar` | 1,986,344,960 | `18dc1f72307d2c270f5953a45b6f3804997245a91d686fdea64222c25251aab9` |
| `k11_sources_06.tar` | 1,992,171,520 | `c5eea78ec7e518defed7875fc867950e402029fc59fc0201fb46f1732903b005` |
| `k11_sources_07.tar` | 1,991,710,720 | `58cbf33496bf2bfbd2eb3a8f8f5ba212cd18b784b917c81b8ea7e91d09d030f8` |
| `k11_sources_08.tar` | 1,995,776,000 | `8f027c9f91de19f018a758d57b96758e256730c9c2ec96618e2229c7373abf3c` |
| `k11_sources_09.tar` | 1,973,463,040 | `9a891d91c92f29f1d92c537a690110d3e80c2bb40216ea647a93b7d832bbd053` |
| `k11_sources_10.tar` | 1,981,900,800 | `e284645638288c57fd835b9b85397d5774b49a226137fa45b858235bc33610c0` |
| `k11_sources_11.tar` | 1,958,359,040 | `e22c0f731c8a792f2ccb8c0b2412d93ce9cb9ec53d4e3e4a01c799f72974a684` |
| `k11_sources_12.tar` | 1,982,515,200 | `2d13403594c778a0fcd3ed7d97f036501fb37b1539fa55f6355c9e01f9bf2184` |
| `k11_sources_13.tar` | 1,993,185,280 | `c4653a8495a3edc8b71d0c6bec6df4fc2841896a74c984dbc96cb2e6d1497817` |
| `k11_sources_14.tar` | 1,996,615,680 | `ecf3de0f9c1898e401c07a0f0c29dc02473fcdfdb10d5b851275282d29e723d3` |
| `k11_sources_15.tar` | 116,715,520 | `0b705bc049765bb5a30259e7dc0294e9b56bc540bc78856509ff6b8d5b65890c` |
| `k11_glue.tar.zst` | 66,701,378 | `765203c48ea883ec00ce50b1fcc5a48adc9bf7da7e9f4741c3b8a89308faac6c` |
| `k11_glue.tar` | 1,477,488,640 | `76ea62663718b4bdaa4baff1457d0c06c50a2fc2f0edd8cefbac231c9eb8963a` |
| `k11_sums.tar.zst` | 66,568,744 | `1b96415125a178a4c16014a9c7b96c272adc8e32f7ac03291d7d3d95a4aa5234` |
| `k11_sums.tar` | 172,257,280 | `0b6d98ed1e6c124e2a4c7763b117619e20222bf30645527b53a1af52423a966b` |
| `cert8d_0836.tar.xz` | 487,316 | `d8a7f09dc236a7c647147bacc3e903f3c9e2bd2cadb601d000d1a67a2a237681` |
| `cert8d_0836.tar` | 1,617,920 | `12432e0a1e3b8b56a47454eed3cc4d6dac376f0e3525e486492eac6ec31afb03` |
| `cert5d_08347.tar.xz` | 17,308 | `2026ebe7e5339b89542e0429e5ad704b1a956278e3ae455b6d667b4c11892846` |
| `cert5d_08347.tar` | 92,160 | `cb14e4ac6569d4709a83114facb4fc77b731dfd964a483e8238b52147a3c249e` |
