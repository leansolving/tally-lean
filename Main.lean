import Tally.Engine
import Tally.Families.GridIndep
import Tally.Families.BarArrayMain

/-- Layer-by-layer run of the sequential engine with the number of states and the resident
set size (Linux `/proc/self/status`) after every layer; for memory diagnostics. -/
def trace {L : Nat} (σ : Tally.Spec UInt64 L 2) : IO Unit := do
  let mut m : Std.HashMap UInt64 Nat := (∅ : Std.HashMap UInt64 Nat).insert σ.root 1
  let t0 ← IO.monoMsNow
  for i in [0:L] do
    m := σ.advance i m
    let rss ← (do
      let st ← IO.FS.readFile "/proc/self/status"
      let ls := st.splitOn "\n"
      let r := (ls.find? (·.startsWith "VmRSS:")).getD "VmRSS: ?"
      let h := (ls.find? (·.startsWith "VmHWM:")).getD "VmHWM: ?"
      pure s!"{r.drop 6 |>.trim} hwm={h.drop 6 |>.trim}") <|> pure "n/a"
    IO.println s!"layer={i + 1} states={m.size} t_ms={(← IO.monoMsNow) - t0} rss={rss}"
    (← IO.getStdout).flush
  IO.println s!"count={σ.finalSum m}"

/-- Command-line runner (unverified use of the verified engine, for timings and
cross-checks): `tally-lean n` prints `(GridIndep.fspec n false).count` (A006506 n);
`tally-lean hex n` prints `(GridIndep.fspec n true).count` (A066864 n);
`tally-lean bar k n` prints `(BarArray.fspec n k).count` (A145789 for k = 4,
A145757 for k = 3, A145773 for k = 2). Time it externally. -/
def main (args : List String) : IO UInt32 := do
  let usage := "usage: tally-lean [par <P>] <n> | tally-lean [par <P>] hex <n> | tally-lean [par <P>] bar <k> <n>"
  match args with
  | ["trace", "hex", ns] =>
    match ns.toNat? with
    | some n => trace (Tally.GridIndep.fspec n true); return 0
    | none => IO.eprintln usage; return 1
  | ["trace", ns] =>
    match ns.toNat? with
    | some n => trace (Tally.GridIndep.fspec n false); return 0
    | none => IO.eprintln usage; return 1
  | "par" :: ps :: rest =>
    match ps.toNat?, rest with
    | some P, [ns] =>
      match ns.toNat? with
      | some n => IO.println s!"grid n={n} P={P} count={Tally.Spec.countPar (Tally.GridIndep.mkSpec n false) (Tally.GridIndep.mkPart n (Nat.log2 P)) P}"; return 0
      | none => IO.eprintln usage; return 1
    | some P, ["hex", ns] =>
      match ns.toNat? with
      | some n => IO.println s!"hex n={n} P={P} count={Tally.Spec.countPar (Tally.GridIndep.mkSpec n true) (Tally.GridIndep.mkPart n (Nat.log2 P)) P}"; return 0
      | none => IO.eprintln usage; return 1
    | some P, ["bar", ks, ns] =>
      match ks.toNat?, ns.toNat? with
      | some k, some n =>
        IO.println s!"bar k={k} n={n} P={P} count={Tally.Spec.countPar (Tally.BarArray.mkSpec n k) (fun _ => Tally.hashPart) P}"; return 0
      | _, _ => IO.eprintln usage; return 1
    | _, _ => IO.eprintln usage; return 1
  | [s] =>
    match s.toNat? with
    | some n =>
      IO.println s!"grid n={n} count={(Tally.GridIndep.fspec n false).count}"
      return 0
    | none => IO.eprintln usage; return 1
  | ["hex", ns] =>
    match ns.toNat? with
    | some n =>
      IO.println s!"hex n={n} count={(Tally.GridIndep.fspec n true).count}"
      return 0
    | none => IO.eprintln usage; return 1
  | ["bar", ks, ns] =>
    match ks.toNat?, ns.toNat? with
    | some k, some n =>
      IO.println s!"bar k={k} n={n} count={(Tally.BarArray.fspec n k).count}"
      return 0
    | _, _ => IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
