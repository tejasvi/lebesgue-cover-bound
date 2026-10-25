"""Kernel-checked certificate for M(D, B3, B5, B7, B9) >= 0.8366 (11D): Lean modules from the audited native
certificate's tree (L11/B<c>.lean, L11/S<c>_<k>.lean: lo, hi, codes, side) and the leaf data printed by k11extract.

Modes:
  leaves EXTRACT_OUT L11DIR LEANROOT   leaf modules LebK/L11/<M>_<j>.lean (at most LB leaves each, DFS order) for every
                                       module M in EXTRACT_OUT; each leaf in namespace LebK.K11.<M>.Q<i> with lo, hi, packed
                                       witnesses, cen, beta, sigma (and lam per fan of a combination leaf) and
                                       `ok : leafOKF … = true` or `ok : combOKF … = true`, proved by `decide +kernel`
  glue L11DIR LEANROOT [MODULES...]    from the tree alone: per subtree module S<c>_<k> the module
                                       LebesgueCover/K11/H<c>_<k>.lean, per cell B<c> the module LebesgueCover/K11/G<c>.lean;
                                       units of at most U delegated items (leaves, sub-units, subtrees) walked by
                                       `walk … .isSome = true := by decide +kernel`, goodness by `cellK_good`
  root LEANROOT                        LebesgueCover/K11/C<kk>.lean (64 chunks of 32 cells) and LebesgueCover/K11/Root11K.lean
Leaf indices i count the 'L' and 'C' codes of M in DFS order (lower half first), as k11extract does."""
import sys, os, re
from fractions import Fraction as Fr
sys.set_int_max_str_digits(0)

SLOT = 152; LB = 32; U = 32; D = 11; CHUNK = 32; NCELLS = 2048
RL11 = [Fr(-1696575, 8388608), Fr(-1696575, 8388608), Fr(0), Fr(-3415393, 16777216), Fr(-3415393, 16777216), Fr(0),
        Fr(-3395327, 16777216), Fr(-3395327, 16777216), Fr(0), Fr(-1692535, 8388608), Fr(-1692535, 8388608)]
RH11 = [Fr(1696575, 8388608), Fr(1696575, 8388608), Fr(333, 1024), Fr(3415393, 16777216), Fr(3415393, 16777216),
        Fr(1973, 4096), Fr(3395327, 16777216), Fr(3395327, 16777216), Fr(1491, 4096), Fr(1692535, 8388608),
        Fr(1692535, 8388608)]
NU = '(mkRat 1 (2 ^ 36))'

# ---------- numbers ----------
def q(x):
    x = Fr(x)
    return f'({x.numerator} / {x.denominator} : Rat)' if x.denominator != 1 else f'({x.numerator} : Rat)'

def arr(v):
    return '#[' + ', '.join(q(x) for x in v) + ']'

def encq(x):
    x = Fr(x); d = x.denominator; e = d.bit_length() - 1
    assert d == 1 << e and e < 256, x
    a = abs(x.numerator); assert a < (1 << 64), x
    return (((a << 8) | e) << 1) | (1 if x.numerator < 0 else 0)

def pack(W):
    n = 0
    for i, (b, x, y) in enumerate(W):
        assert 0 <= b < 16
        slot = (((encq(x) << 73) | encq(y)) << 4) | b
        assert slot < (1 << SLOT)
        n |= slot << (SLOT * i)
    return n

def decq(c):
    s = c % 2; e = (c // 2) % 256; a = c // 512
    return Fr(-a if s == 1 else a, 1 << e)

def unpack(m, n):
    out = []
    for _ in range(m):
        c = n % (1 << SLOT)
        out.append((c % 16, decq(c // 16 // (1 << 73)), decq((c // 16) % (1 << 73))))
        n //= (1 << SLOT)
    return out

def fun(vals, var):
    cases = ''.join(f' | {i} => {q(v)}' for i, v in enumerate(vals) if Fr(v) != 0)
    return f'fun {var} => match {var} with{cases} | _ => 0' if cases else 'fun _ => 0'

# ---------- L11 modules and trees ----------
def strdef(txt, name):
    m = re.search(r'def ' + name + r' : String := "([^"]*)"', txt)
    return m.group(1) if m else None

def gridcells(sp, lo, hi):
    if not sp:
        return [(lo, hi)]
    a = sp[0]; m = (lo[a] + hi[a]) / 2
    h1 = list(hi); h1[a] = m
    l2 = list(lo); l2[a] = m
    return gridcells(sp[1:], lo, h1) + gridcells(sp[1:], l2, hi)

CELLS = gridcells(list(range(D)), RL11, RH11)

def read_l11(path):
    txt = open(path).read()
    tag = os.path.basename(path)[:-5]
    lo, hi = strdef(txt, 'lo'), strdef(txt, 'hi')
    if lo is None:
        assert tag.startswith('B')
        lo, hi = CELLS[int(tag[1:])]
    else:
        lo = [Fr(x) for x in lo.split()]; hi = [Fr(x) for x in hi.split()]
    return tag, lo, hi, strdef(txt, 'codes')

def parse(tag, codes, lo, hi):
    """tree from DFS preorder codes ('0'-'9','a'-'z': split coordinate at the midpoint, lower half first; 'L' single
    leaf, 'C' combination leaf, 'X' delegated subtree)."""
    pos = 0; nleaf = 0; nsub = 0
    def rec(lo, hi):
        nonlocal pos, nleaf, nsub
        ch = codes[pos]; pos += 1
        if ch in 'LC':
            n = dict(k='L', comb=ch == 'C', lo=lo, hi=hi, idx=nleaf); nleaf += 1
            return n
        if ch == 'X':
            n = dict(k='X', lo=lo, hi=hi, sub=nsub); nsub += 1
            return n
        c = int(ch) if ch.isdigit() else ord(ch) - ord('a') + 10
        assert c < len(lo), (tag, ch)
        m = (lo[c] + hi[c]) / 2
        l1, h1 = list(lo), list(hi); h1[c] = m
        l2, h2 = list(lo), list(hi); l2[c] = m
        left = rec(l1, h1)
        return dict(k='S', a=c, lo=lo, hi=hi, l=left, r=rec(l2, h2))
    t = rec(lo, hi)
    assert pos == len(codes), tag
    return t, nleaf, nsub

def items_of(n, out):
    if n['k'] in 'LX':
        out.append(n)
    else:
        items_of(n['l'], out); items_of(n['r'], out)
    return out

def mark(n, Umax):
    if n['k'] in 'LX':
        return 1
    cl, cr = mark(n['l'], Umax), mark(n['r'], Umax)
    if cl + cr <= Umax:
        return cl + cr
    big, small = (n['l'], n['r']) if cl >= cr else (n['r'], n['l'])
    cb, cs = max(cl, cr), min(cl, cr)
    if big['k'] == 'S':
        big['unit'] = True; cb = 1
    if cb + cs > Umax and small['k'] == 'S':
        small['unit'] = True; cs = 1
    return cb + cs

def units_post(n, out):
    if n['k'] == 'S':
        units_post(n['l'], out); units_post(n['r'], out)
        if n.get('unit'):
            out.append(n)
    return out

def unit_walk(u):
    codes, items = [], []
    def rec(n, top):
        if n['k'] in 'LX' or (not top and n.get('unit')):
            codes.append(250); items.append(n); return
        codes.append(n['a']); rec(n['l'], False); rec(n['r'], False)
    rec(u, True)
    return codes, items

def nested(goods):
    s = '.nil'
    for g in reversed(goods):
        s = f'.cons {g} ({s})' if s != '.nil' else f'.cons {g} .nil'
    return s

def leafname(tag, i):
    return f'LebK.K11.{tag}.Q{i}'

def leafmods(tag, nleaf):
    return [f'LebK.L11.{tag}_{j}' for j in range((nleaf + LB - 1) // LB)]

# ---------- leaves ----------
def parse_fan(tok):
    d = {}
    for t in tok.split(' '):
        if '=' in t:
            k, v = t.split('=', 1); d[k] = v
    W = []
    for w in d['W'].split(','):
        b, x, y = w.split(':'); W.append((int(b), Fr(x), Fr(y)))
    return dict(W=W, z=tuple(Fr(v) for v in d['z'].split(':')), beta=[Fr(v) for v in d['beta'].split(',')],
                sigma=[Fr(v) for v in d['sigma'].split(',')], lam=Fr(d['lam']) if 'lam' in d else None)

def parse_line(line):
    toks = line.split(' ')
    kind, mod, idx = toks[0], toks[1], int(toks[2])
    box = {}
    for t in toks[3:]:
        if t.startswith('lo=') or t.startswith('hi='):
            k, v = t.split('=', 1); box[k] = [Fr(x) for x in v.split(',')]
    if kind == 'L':
        fans = [parse_fan(line[line.index(' m='):].strip())]
    else:
        body = line[line.index(' nf=') + 1:]
        body = body[body.index(' ') + 1:]
        fans = [parse_fan(f.strip()) for f in body.split(' | ')]
    return kind, mod, idx, box['lo'], box['hi'], fans

def leaf_block(kind, nm, lo, hi, fans):
    L = [f'namespace {nm}', f'noncomputable def lo : Array Rat := {arr(lo)}', f'noncomputable def hi : Array Rat := {arr(hi)}']
    items = []
    for j, F in enumerate(fans):
        P = pack(F['W'])
        assert unpack(len(F['W']), P) == F['W']
        L.append(f'noncomputable def wit{j} : Nat := {P}')
        L.append(f'noncomputable def cen{j} : Rat × Rat := ({q(F["z"][0])}, {q(F["z"][1])})')
        L.append(f'noncomputable def beta{j} : Nat → Rat := {fun(F["beta"], "i")}')
        L.append(f'noncomputable def sigma{j} : Nat → Rat := {fun(F["sigma"], "a")}')
        if kind == 'C':
            L.append(f'noncomputable def lam{j} : Rat := {q(F["lam"])}')
        items.append(f'(unpackW {len(F["W"])} wit{j})')
    box = '(fun a => lo.getD a 0) (fun a => hi.getD a 0)'
    if kind == 'L':
        L.append(f'theorem ok : leafOKF ns11 VQ {NU} tau11 {box} {items[0]} cen0 beta0 sigma0 = true := by')
    else:
        lst = ', '.join(f'({w}, cen{j}, beta{j}, sigma{j}, lam{j})' for j, w in enumerate(items))
        L.append(f'theorem ok : combOKF ns11 VQ {NU} tau11 {box} [{lst}] = true := by')
    L += ['  decide +kernel', f'end {nm}', '']
    return L

LEAF_HDR = ('import LebFast.Exact\nimport LebFast.VT\nimport LebFast.Root11\nimport LebK.Decode\n\n'
            '/-! Leaves {a}–{b} of module {tag} of the kernel-checked 11D certificate (`M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`): '
            'box, packed witnesses, centre, `β`, `σ` (and weights of combination leaves), and the leaf check by '
            '`decide +kernel`. Generated by gen/k11/mkk11.py. -/\n\n'
            'open LebesgueCover.Fast\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n')

def write_leaves(extract_out, l11dir, root):
    os.makedirs(os.path.join(root, 'LebK', 'L11'), exist_ok=True)
    bymod = {}
    for line in open(extract_out):
        if line.startswith('LFAIL') or line.startswith('CFAIL') or line.startswith('MODERR'):
            raise SystemExit('extractor failure: ' + line[:200])
        if line.startswith('L ') or line.startswith('C '):
            t = line.split(' ', 3); bymod.setdefault(t[1], []).append(line.rstrip('\n'))
    nmods = 0
    for modf, lines in sorted(bymod.items()):
        tag, lo, hi, codes = read_l11(os.path.join(l11dir, modf))
        tree, nleaf, nsub = parse(tag, codes, lo, hi)
        leaves = [n for n in items_of(tree, []) if n['k'] == 'L']
        assert len(lines) == nleaf == len(leaves), (tag, len(lines), nleaf)
        for j, start in enumerate(range(0, nleaf, LB)):
            body = []
            for line in lines[start:start + LB]:
                kind, _, idx, llo, lhi, fans = parse_line(line)
                n = leaves[idx]
                assert idx == n['idx'] and llo == n['lo'] and lhi == n['hi'] and (kind == 'C') == n['comb'], (tag, idx)
                body += leaf_block(kind, leafname(tag, idx), llo, lhi, fans)
            txt = LEAF_HDR.format(a=start, b=min(start + LB, nleaf) - 1, tag=tag) + '\n'.join(body)
            open(os.path.join(root, 'LebK', 'L11', f'{tag}_{j}.lean'), 'w').write(txt)
            nmods += 1
    print('leaf modules', nmods, 'from', len(bymod), 'certificate modules')

# ---------- glue ----------
def unit_block(u, tag, glue_ns):
    codes, items = unit_walk(u)
    refs = []
    for it in items:
        if it['k'] == 'L':
            nm = leafname(tag, it['idx'])
            refs.append((f'{nm}.lo', f'{nm}.hi', f'({"combF_good" if it["comb"] else "leafF_good"} vt11 {nm}.ok)'))
        elif it['k'] == 'X':
            h = f'LebesgueCover.K11.H{tag[1:]}_{it["sub"]}'
            refs.append((f'{h}.lo', f'{h}.hi', f'{h}.good'))
        else:
            refs.append((f'{it["uname"]}.lo', f'{it["uname"]}.hi', f'{it["uname"]}.good'))
    head = [] if u.get('top') else [f'namespace {u["uname"]}']
    tail = [] if u.get('top') else [f'end {u["uname"]}']
    return '\n'.join(head + [
        f'noncomputable def lo : Array Rat := {arr(u["lo"])}',
        f'noncomputable def hi : Array Rat := {arr(u["hi"])}',
        f'theorem walk_ok : (walk ns11 #[] VQ {NU} tau11 {len(codes)} {codes} [] [' + ', '.join(f'({a}, {b})' for a, b, _ in refs)
        + '] lo hi).isSome = true := by',
        '  decide +kernel',
        'theorem good : GoodBox ns11 tau11 (fun i => lo.getD i 0) (fun i => hi.getD i 0) :=',
        f'  cellK_good vt11 ({nested([g for _, _, g in refs])}) walk_ok'] + tail + [''])

def write_glue(l11dir, root, modules):
    os.makedirs(os.path.join(root, 'LebesgueCover', 'K11'), exist_ok=True)
    stats = dict(glue=0, units=0, max_items=0, leaves=0, subtrees=0)
    for modf in modules:
        tag, lo, hi, codes = read_l11(os.path.join(l11dir, modf))
        tree, nleaf, nsub = parse(tag, codes, lo, hi)
        stats['leaves'] += nleaf; stats['subtrees'] += nsub
        if tree['k'] == 'S':
            mark(tree, U)
            us = units_post(tree, [])
        else:
            us = []
        us = [u for u in us if u is not tree]
        for k, u in enumerate(us):
            u['uname'] = f'U{k}'
        top = dict(tree); top['unit'] = True; top['top'] = True; top['uname'] = 'top'
        for u in us + [top]:
            stats['max_items'] = max(stats['max_items'], len(unit_walk(u)[1]))
        stats['units'] += len(us) + 1
        if tag.startswith('S'):
            name = f'H{tag[1:]}'; subs = []
            what = f'Subtree {tag} of the kernel-checked 11D certificate'
        else:
            name = f'G{tag[1:]}'
            subs = [f'LebesgueCover.K11.H{tag[1:]}_{k}' for k in range(nsub)]
            what = f'Cell {tag[1:]} of the kernel-checked 11D certificate'
        ns = f'LebesgueCover.K11.{name}'
        txt = ('import LebesgueCover.K11Base\n' + ''.join(f'import {m}\n' for m in leafmods(tag, nleaf))
               + ''.join(f'import {s}\n' for s in subs) + '\n'
               f'/-! {what}: tree walks with delegated items (leaves, sub-units'
               + (', subtrees' if subs else '') + ') by `decide +kernel`, and the goodness of its box. '
               'Generated by gen/k11/mkk11.py. -/\n\n'
               'open LebesgueCover.Fast LebesgueCover.Cert\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
               f'namespace {ns}\n\n' + '\n'.join(unit_block(u, tag, ns) for u in us + [top]) + f'\nend {ns}\n')
        open(os.path.join(root, 'LebesgueCover', 'K11', f'{name}.lean'), 'w').write(txt)
        stats['glue'] += 1
    print('glue', stats)

# ---------- chunks and root ----------
def write_root(root):
    os.makedirs(os.path.join(root, 'LebesgueCover', 'K11'), exist_ok=True)
    J = NCELLS // CHUNK
    for j in range(J):
        cis = list(range(j * CHUNK, (j + 1) * CHUNK))
        cl = ', '.join(f'(G{ci}.lo, G{ci}.hi)' for ci in cis)
        txt = ('import LebesgueCover.K11Base\n' + ''.join(f'import LebesgueCover.K11.G{ci}\n' for ci in cis) + '\n'
               f'/-! Cells {cis[0]}–{cis[-1]} of the kernel-checked 11D certificate: the chunk theorem. '
               'Generated by gen/k11/mkk11.py. -/\n\n'
               'open LebesgueCover.Fast LebesgueCover.Cert LebesgueCover.K11\n\nset_option maxHeartbeats 0\n'
               'set_option maxRecDepth 100000\n\nnamespace LebesgueCover.K11\n\n'
               f'theorem chunk{j:02d} : ∀ c ∈ ((gridCells (gridSplits {D} 1) rl11 rh11).drop ({j} * {CHUNK})).take {CHUNK},\n'
               '    GoodBox ns11 tau11 (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) := by\n'
               f'  have e : ((gridCells (gridSplits {D} 1) rl11 rh11).drop ({j} * {CHUNK})).take {CHUNK} = [{cl}] := by\n'
               '    decide +kernel\n'
               '  rw [e]\n'
               f'  exact AllGood.mem ({nested([f"G{ci}.good" for ci in cis])})\n\n'
               'end LebesgueCover.K11\n')
        open(os.path.join(root, 'LebesgueCover', 'K11', f'C{j:02d}.lean'), 'w').write(txt)
    txt = ('import LebesgueCover.Main5\nimport LebesgueCover.Diam\n'
           + ''.join(f'import LebesgueCover.K11.C{j:02d}\n' for j in range(J)) + '\n'
           '/-!\n# `M(D, B₃, B₅, B₇, B₉) ≥ 0.8366` and `Λ ≥ 0.8366` with a kernel-checked certificate\n\n'
           f'The root box is good: its grid of {NCELLS} cells is covered by {J} chunks of {CHUNK} cells. The certificate '
           'modules use `decide +kernel` only.\n-/\n\n'
           'open LebesgueCover.Fast LebesgueCover.Cert\n\nnamespace LebesgueCover.K11\n\n'
           '/-- The root box is good. -/\n'
           'theorem root11_good : GoodBox ns11 tau11 (fun i => rl11.getD i 0) (fun i => rh11.getD i 0) := by\n'
           f'  refine root_good\' (d := {D}) (e := 1) (B := {CHUNK}) (J := {J}) (fun j hj => ?_) (by norm_num)\n'
           '  interval_cases j\n'
           '  exacts [' + ', '.join(f'chunk{j:02d}' for j in range(J)) + ']\n\n'
           '/-- **`M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`.** -/\n'
           'theorem hull5_geK : Hull5Statement := hull5_of_root_good root11_good\n\n'
           '/-- **`Λ ≥ 0.8366`** for weak universal covers. -/\n'
           'theorem weak_main5K : WeakMain5Statement := weak5_of_hull5 hull5_geK\n\n'
           '/-- **`Λ ≥ 0.8366`.** -/\n'
           'theorem main5K : Main5Statement := main5_of_hull5 hull5_geK\n\n'
           'end LebesgueCover.K11\n')
    open(os.path.join(root, 'LebesgueCover', 'K11', 'Root11K.lean'), 'w').write(txt)
    print('root: chunks', J)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'leaves':
        write_leaves(sys.argv[2], sys.argv[3], sys.argv[4])
    elif mode == 'glue':
        l11dir, root = sys.argv[2], sys.argv[3]
        mods = sys.argv[4:] or sorted(f for f in os.listdir(l11dir) if re.match(r'^[BS]\d+(_\d+)?\.lean$', f))
        write_glue(l11dir, root, mods)
    elif mode == 'root':
        write_root(sys.argv[2])
    else:
        raise SystemExit(__doc__)
