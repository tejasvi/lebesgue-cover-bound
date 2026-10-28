# The certificates

`cert5d_08347.tar.xz` and `cert8d_0836.tar.xz` are in this directory; `cert11d_08366.tar.xz` is archived only at
doi:10.5281/zenodo.23717912 (`cert11d_08366.sha256` gives its SHA-256). `../README.md` explains how to check them.

## Contents of the archives

Each archive contains one directory with the files `partNNNN.json` (header) and `partNNNN.npy` (codes) of every
part and a file `SHA256SUMS` for them. The archive `cert11d_08366.tar.xz` (293,113,544 bytes) also contains the side
files `partNNNN_multi.npz`, the output of the first run of the checker on every part (`checklogs/`, `SUMMARY.txt`)
and copies of the checker and of the search program as they were used (`code/`, byte-identical to
`checker/lbcheck.py`, `search/lbsearch_v4.py` and `search/lbbnb_v4.py`).

## Certificate format

A certificate consists of `P` parts. The header `partNNNN.json` records `ns` (the numbers of corners of the
Reuleaux polygons), `tau` (the target), `lo` and `hi` (the corners of the root box), `split0` (the grid),
`nparts` and `part`, the parameters `N` and `eps` of the witness heuristic, and further search parameters and
statistics that the checker does not use. Coordinates are `(t1x, t1y, rho2, t2x, t2y, ..., rhok, tkx, tky)`. The
first Reuleaux polygon has rotation 0. The root box is cut into the grid cells, listed in the order of
`numpy.ndindex(*split0)`, and part `j` holds the cells `list(numpy.ndindex(*split0))[j::nparts]`. The array
`partNNNN.npy` (`uint8`) describes, for each of these cells in turn, a binary tree in depth-first preorder: a code
`a < dim` splits the current box at the midpoint of coordinate `a`, followed by the trees of the lower and the upper
half. The code `253` marks a leaf closed by the combination bound, `254` a leaf closed by the box bound of step 2 of
the outline, and `255` a leaf closed by the corner estimate. For the leaves with code `253`, the side file
`partNNNN_multi.npz` holds the arrays `pos` (the position of each such leaf in the code array, counted from 0),
`nstruct` (the number of fans of each leaf), and `shifts` and `lam` (one sign vector in `{-1, 0, 1}^dim` and one
weight per fan, with the fans of the leaves in the order of `pos`). The fan with sign vector `s` is built from the support points of the hull at the placement
`c + s * h`, where `c` is the centre of the leaf and `h` its vector of half-widths. No witnesses are stored.
