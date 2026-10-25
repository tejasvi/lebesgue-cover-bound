import LebFast.Tree
import LebFast.VT
import LebFast.Root11

/-!
# Leaf data of the 11D certificate, for kernel-checked modules (pilot tool)

For each B/S module of the native certificate, walk its tree as `LebFast.Tree.walk` does and print, for every leaf,
the exact data that the compiled checker accepts: for a single-fan leaf the witnesses, fan centre, `β` and `σ` of the
first passing proposal over a list of witness-set sizes `N`; for a combination leaf one such fan per side entry with
its weight (first passing scale over the same size list, all fans at one scale). Every printed leaf passed
`leafOKF` / `combOKF` here (compiled).
usage: k11extract LISTFILE OUTFILE SPEC MULTS   (SPEC = N:E7 pairs for single fans, eps = E7·1e-7, e.g.
256:1000,256:300,256:100,1024:10; MULTS = eps multipliers for combination fans, e.g. 10,3,1)
-/

open LebesgueCover.Fast

def ratS (q : Rat) : String := if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

def strDef (txt name : String) : String :=
  let key := s!"def {name} : String := \""
  match txt.splitOn key with
  | [_, rest] => (rest.splitOn "\"").headD ""
  | _ => ""

def fanStr (W : List (Nat × (Rat × Rat))) (z : Rat × Rat) (β σ : Nat → Rat) (nb nv : Nat) : String :=
  let ws := ",".intercalate (W.map fun (b, (x, y)) => s!"{b}:{ratS x}:{ratS y}")
  let bs := ",".intercalate ((List.range nb).map fun i => ratS (β i))
  let ss := ",".intercalate ((List.range nv).map fun a => ratS (σ a))
  s!"m={W.length} W={ws} z={ratS z.1}:{ratS z.2} beta={bs} sigma={ss}"

/-- Nearest multiple of `2^-e`. -/
def rNear (e : Nat) (q : Rat) : Rat := mkRat (Rat.floor (q * (2 ^ e : Nat) + 1 / 2)) (2 ^ e)
/-- Smallest multiple of `2^-e` that is `≥ q`. -/
def rUp (e : Nat) (q : Rat) : Rat := mkRat (Rat.ceil (q * (2 ^ e : Nat))) (2 ^ e)

/-- Short data: witnesses shrunk by `1 - 2^(1-e)` towards their body's centre and rounded to `2^-e` (so they stay in
the body), `z` and `β` rounded to `2^-e`, `σ` rounded up to `2^-e`; the exact check decides whether it is used. -/
def roundFan (e nb nv : Nat) (W : List (Nat × (Rat × Rat))) (z : Rat × Rat) (β σ : Nat → Rat) :
    List (Nat × (Rat × Rat)) × (Rat × Rat) × (Nat → Rat) × (Nat → Rat) :=
  let sh : Rat := 1 - mkRat 1 (2 ^ (e - 1))
  let W' := W.map fun (b, (x, y)) => (b, (rNear e (x * sh), rNear e (y * sh)))
  let bA := (Array.range nb).map fun i => rNear e (β i)
  let sA := (Array.range nv).map fun a => rUp e (σ a)
  (W', (rNear e z.1, rNear e z.2), fun i => bA.getD i 0, fun a => sA.getD a 0)

/-- Single-fan leaf: first passing size. -/
def singleData (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat)
    (Ns : List (Nat × Nat)) (es : List Nat) : Option (String × String) := Id.run do
  let L := mkLeaf ns.length (lo.map ratToFloat) (hi.map ratToFloat)
  let pl := centrePlace L
  for (N, e7) in Ns do
    match proposeAt bs L pl N (Float.ofNat e7 * 1e-7) with
    | none => pure ()
    | some P =>
      let (W, z, β, σ) := exactData P
      if leafOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) W z β σ then
        for e in es do
          let (W', z', β', σ') := roundFan e (ns.length + 1) L.nv W z β σ
          if leafOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) W' z' β' σ' then
            return some (s!"{N}:{e7} e={e}", fanStr W' z' β' σ' (ns.length + 1) L.nv)
        return some (s!"{N}:{e7} e=0", fanStr W z β σ (ns.length + 1) L.nv)
  return none

/-- Combination leaf: all fans at one scale; at multiplier `k` a fan uses `(256, k·1e-5)` if cheap, else `(1024, k·1e-6)`
(`k = 1`: the certificate's own sets). -/
def combData (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat)
    (fs : List (Bool × List Int × Rat)) (divs es : List Nat) : Option (Nat × String) := Id.run do
  let L := mkLeaf ns.length (lo.map ratToFloat) (hi.map ratToFloat)
  for dv in divs do
    let props := fs.map fun (cheap, sv, lam) =>
      (proposeAt bs L (shiftPlace L sv) (if cheap then 256 else 1024) (Float.ofNat dv * (if cheap then 1e-5 else 1e-6)), lam)
    if props.all (fun (P, _) => P.isSome) then
      let fans := props.map fun (P, lam) =>
        let d := exactData (P.getD default)
        (d.1, d.2.1, d.2.2.1, d.2.2.2, lam)
      if combOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) fans then
        let mut best := (0, fans)
        for e in es do
          let fans' := fans.map fun (W, z, β, σ, lam) =>
            let (W', z', β', σ') := roundFan e (ns.length + 1) L.nv W z β σ
            (W', z', β', σ', rNear e lam)
          if best.1 = 0 && combOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) fans' then
            best := (e, fans')
        let strs := best.2.map fun (W, z, β, σ, lam) => s!"lam={ratS lam} " ++ fanStr W z β σ (ns.length + 1) L.nv
        return some (dv, s!"e={best.1} nf={fans.length} " ++ " | ".intercalate strs)
  return none

/-- Walk one tree, collecting output lines; `none` on a structural error. -/
partial def walkOut (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (Ns : List (Nat × Nat))
    (divs es : List Nat)
    (tag : String) (cs : List Nat) (sd : List (List (Bool × List Int × Rat))) (lo hi : Array Rat)
    (acc : Array String) (idx : Nat) : Option (List Nat × List (List (Bool × List Int × Rat)) × Array String × Nat) :=
  match cs with
  | [] => none
  | c :: cs =>
    let box := s!"lo={",".intercalate (lo.toList.map ratS)} hi={",".intercalate (hi.toList.map ratS)}"
    if c = 254 then
      match singleData ns bs V ν τ lo hi Ns es with
      | some (ne, s) => some (cs, sd, acc.push s!"L {tag} {idx} N={ne} {box} {s}", idx + 1)
      | none => some (cs, sd, acc.push s!"LFAIL {tag} {idx} {box}", idx + 1)
    else if c = 252 then
      match sd with
      | [] => none
      | f :: sd' =>
        match combData ns bs V ν τ lo hi f divs es with
        | some (dv, s) => some (cs, sd', acc.push s!"C {tag} {idx} mult={dv} {box} {s}", idx + 1)
        | none => some (cs, sd', acc.push s!"CFAIL {tag} {idx} {box}", idx + 1)
    else if c = 250 then some (cs, sd, acc, idx)
    else if c < lo.size then
      let m := (lo[c]! + hi[c]!) / 2
      match walkOut ns bs V ν τ Ns divs es tag cs sd lo (hi.set! c m) acc idx with
      | none => none
      | some (cs', sd', acc', idx') => walkOut ns bs V ν τ Ns divs es tag cs' sd' (lo.set! c m) hi acc' idx'
    else none

def main (args : List String) : IO Unit := do
  let [listF, outF, specS, multS, esS] := args | IO.eprintln "usage: k11extract LISTFILE OUTFILE N:E7,... K,K,...1 E,E,...|0"
  let Ns := (specS.splitOn ",").map fun t => match t.splitOn ":" with
    | [a, b] => (a.toNat!, b.toNat!) | _ => (256, 100)
  let divs := (multS.splitOn ",").map String.toNat!
  let es := ((esS.splitOn ",").map String.toNat!).filter (· > 0)
  let ns := ns11; let bs := (ns.map mkFBody).toArray; let ν : Rat := mkRat 1 (2 ^ 36)
  let grid := (gridCells (gridSplits 11 1) rl11 rh11).toArray
  let files := (← IO.FS.lines listF).toList.filter (· ≠ "")
  let h ← IO.FS.Handle.mk outF .write
  for f in files do
    let txt ← IO.FS.readFile f
    let tag := (f.splitOn "/").getLastD f
    let (lo, hi) := if strDef txt "lo" ≠ "" then (parseRatList (strDef txt "lo"), parseRatList (strDef txt "hi"))
      else grid.getD (((tag.drop 1).takeWhile Char.isDigit).toNat!) (#[], #[])
    let cs := decodeCodes (strDef txt "codes"); let sd := decodeSide (strDef txt "side")
    let t0 ← IO.monoMsNow
    match walkOut ns bs VQ ν tau11 Ns divs es tag cs sd lo hi #[] 0 with
    | some ([], [], acc, n) =>
      for l in acc do h.putStrLn l
      h.putStrLn s!"MOD {tag} leaves={n} ms={(← IO.monoMsNow) - t0}"
    | _ => h.putStrLn s!"MODERR {tag}"
    h.flush
