#!/bin/bash
# usage: build_k5.sh /path/to/k5_sources.tar.zst   (in lean/, after `lake build LebFast LebesgueCover`):
# unpack the generated modules of the kernel-checked three-body certificate (LebK/L, LebesgueCover/K3, and the
# search output under ../tools/gen/k5/s1), check their manifest, build the final theorems and print their axioms.
set -eu
zstd -dc "$1" | tar -xf - -C ..
(cd .. && sha256sum -c --quiet SHA256SUMS_k5)
lake build LebesgueCover.K3.Root3Good
lake env lean tools/K3Axioms.lean
