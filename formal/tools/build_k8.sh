#!/bin/bash
# usage: build_k8.sh /path/to/k8_sources.tar.zst [NPAR]   (in lean/, after `lake build LebFast LebesgueCover LebK`):
# unpack the generated modules of the kernel-checked four-body certificate (LebK/L8, LebesgueCover/K8, and the search
# output under ../tools/gen/k8/s1), check their manifest, compile the leaf modules (NPAR processes, plain `lean`), then
# the chunk modules and the final module, and print the axioms of the final theorems. `-DElab.async=false` keeps each
# process on one thread (theorems are checked one after another), which bounds its memory.
# Several machines: run with SHARD=i NSHARD=n on machine i (it compiles every n-th leaf module of the sorted list,
# starting at the i-th, and stops), collect all .lake/build/lib/lean/LebK/L8/*.olean on one machine, and run there with
# SKIP_LEAVES=1.
set -eu
NPAR=${2:-$(nproc)}
if [ ! -f ../SHA256SUMS_k8 ]; then zstd -dc "$1" | tar -xf - -C ..; fi
(cd .. && sha256sum -c --quiet SHA256SUMS_k8)
LP=$(lake env printenv LEAN_PATH)
B=.lake/build/lib/lean
mkdir -p $B/LebK/L8 $B/LebesgueCover/K8
LOG=${LOG:-$PWD/build_k8_times.txt}   # one line per module: name, exit code, wall seconds, peak RSS (kB)
build() {
  [ -f "$B/$1.olean" ] && return 0
  /usr/bin/time -a -o "$LOG" -f "$1 %x %e %M" env LEAN_PATH="$LP" lean -DElab.async=false -o "$B/$1.olean" -i "$B/$1.ilean" "$1.lean"
}
export -f build; export LP B LOG
if [ "${SKIP_LEAVES:-0}" != 1 ]; then
  ls LebK/L8/ | grep '^L[0-9_]*\.lean$' | LC_ALL=C sort | sed 's/\.lean$//' | \
    awk -v s="${SHARD:-0}" -v n="${NSHARD:-1}" '{ if ((NR - 1) % n == s) print "LebK/L8/" $0 }' | \
    xargs -P "$NPAR" -I{} bash -c 'build {}'
  [ "${NSHARD:-1}" -gt 1 ] && exit 0
fi
ls LebesgueCover/K8/ | grep '^G[0-9]*\.lean$' | sed 's/\.lean$//' | sed 's|^|LebesgueCover/K8/|' | \
  xargs -P "$NPAR" -I{} bash -c 'build {}'
build LebesgueCover/K8/Root4Good
LEAN_PATH=$LP lean tools/K8Axioms.lean
