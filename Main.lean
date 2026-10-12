import Tally.Families.GridIndepFast
import Tally.Families.BarArrayMain

/-- Command-line runner (unverified use of the verified engine, for timings and
cross-checks): `tally-lean n` prints `(GridIndep.fspec n).count` (A006506 n);
`tally-lean bar k n` prints `(BarArray.fspec n k).count` (A145789 for k = 4,
A145757 for k = 3, A145773 for k = 2). Time it externally. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [s] =>
    match s.toNat? with
    | some n =>
      IO.println s!"grid n={n} count={(Tally.GridIndep.fspec n).count}"
      return 0
    | none => IO.eprintln "usage: tally-lean <n> | tally-lean bar <k> <n>"; return 1
  | ["bar", ks, ns] =>
    match ks.toNat?, ns.toNat? with
    | some k, some n =>
      IO.println s!"bar k={k} n={n} count={(Tally.BarArray.fspec n k).count}"
      return 0
    | _, _ => IO.eprintln "usage: tally-lean <n> | tally-lean bar <k> <n>"; return 1
  | _ => IO.eprintln "usage: tally-lean <n> | tally-lean bar <k> <n>"; return 1
