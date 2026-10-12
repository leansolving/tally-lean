import Lake
open Lake DSL

package "tally" where
  version := v!"0.1.0"

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib "Tally" where
  roots := #[`Tally]
  -- native code for the engine, so that `native_decide` (which runs through
  -- `evalConst`) executes compiled code instead of the IR interpreter
  precompileModules := true

lean_exe "tally-lean" where
  root := `Main

/-- Value theorems (`A n = N`) that run the engine through `native_decide`.
Kept in a separate library so that Lake loads the precompiled `Tally` modules
as native code (plugins) while elaborating them; each proof goes through an
out-of-line compiled checker (e.g. `GridIndep.checkCount`), otherwise the
compiler inlines the engine into the proof's auxiliary declaration and the IR
interpreter runs it 10-20x slower. -/
lean_lib "TallyValues" where
  roots := #[`TallyValues]
