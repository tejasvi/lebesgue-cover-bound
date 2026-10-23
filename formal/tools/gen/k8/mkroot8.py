"""Root4Good.lean of the kernel-checked 8D certificate (the text mkk8.py writes when one run covers all chunks).
usage: mkroot8.py LEANROOT [J] [CB] [D]"""
import sys, os
out = sys.argv[1]; J = int(sys.argv[2]) if len(sys.argv) > 2 else 256
CB = int(sys.argv[3]) if len(sys.argv) > 3 else 256; d = int(sys.argv[4]) if len(sys.argv) > 4 else 8
ncells = J * CB
txt = ('import LebesgueCover.Main4\n' + ''.join(f'import LebesgueCover.K8.G{j:03d}\n' for j in range(J)) + '\n'
       '/-!\n# `M(D, B₃, B₅, B₇) ≥ 0.836` and `Λ ≥ 0.836` with a kernel-checked certificate\n\n'
       f'The root box is good: its grid of {ncells} cells is covered by {J} chunks of {CB} cells. The certificate '
       'modules use `decide +kernel` only.\n-/\n\n'
       'open LebesgueCover.Fast LebesgueCover.Cert\n\nnamespace LebesgueCover.K8\n\n'
       '/-- The root box is good. -/\n'
       'theorem root4_good : GoodBox ns4 tau4 (fun i => rl4.getD i 0) (fun i => rh4.getD i 0) := by\n'
       f'  refine root_good\' (d := {d}) (e := 2) (B := {CB}) (J := {J}) (fun j hj => ?_) (by norm_num)\n'
       '  interval_cases j\n'
       '  exacts [' + ', '.join(f'chunk{j:03d}' for j in range(J)) + ']\n\n'
       '/-- **`M(D, B₃, B₅, B₇) ≥ 0.836`.** -/\n'
       'theorem hull4_geK : Hull4Statement := hull4_of_root_good root4_good\n\n'
       '/-- **`Λ ≥ 0.836`** for weak universal covers. -/\n'
       'theorem weak_mainK : WeakMainStatement := weak_of_hull4 hull4_geK\n\n'
       '/-- **`Λ ≥ 0.836`.** -/\n'
       'theorem mainK : MainStatement := main_of_hull4 hull4_geK\n\n'
       'end LebesgueCover.K8\n')
open(os.path.join(out, 'LebesgueCover', 'K8', 'Root4Good.lean'), 'w').write(txt)
print('ok')
