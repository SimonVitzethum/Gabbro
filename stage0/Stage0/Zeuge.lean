/-
  File:      stage0/Stage0/Zeuge.lean
  Subject:   The witness of stage 0 (`Boot/Laufzeit.lean`): a minimal Gabbro program with a call, a branch, a
             narrowing and a loop, accepted by `AkzeptiertX`, run by the kernel on an input.
-/
import Stage0.Laufzeit

namespace Gabbro.Stage0.Zeuge

open Gabbro.Grammatik Gabbro.Stage0 Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Upper-case ASCII: `gross` maps `a .. z` to `A .. Z` and leaves every other byte; `main` applies it to every
    input byte and sets the output length to the input length. -/
def gross : String :=
  "module m { static mut ein_len : u32 in 0 .. 8 = 0; static mut aus_len : u32 in 0 .. 8 = 0; " ++
  "table io count 8 { slot { ein : u32 in 0 .. 255, aus : u32 in 0 .. 255, } } " ++
  "impl fn gross(b : u32 in 0 .. 255) -> u32 in 0 .. 255 { " ++
  "if b >= 97 { narrow b to 97 .. 122 else { return b; } return b - 32; } return b; } " ++
  "impl fn main(t : ptr<normal, rw> io) effects { reads t.slots, writes t.slots, reads ein_len, writes aus_len } { " ++
  "traverse k over slots of t by unvisited touches writes t.slots { " ++
  "let c : u32 in 0 .. 255 = gross(t.slots[k].ein); t.slots[k].aus = c; } aus_len = ein_len; } }"

set_option maxRecDepth 100000 in
/-- **Stage 0 runs it**: `"abC"` becomes `"ABC"`, computed by the kernel through the pipeline, the checker and
    machine G. -/
theorem boot_gross : (boot {} gross [97, 98, 67]).toOption = some [65, 66, 67] := by
  decide +kernel

/-- **The witness of `boot_ist_maschine`**: its premise holds at a non-degenerate run, so its conclusion -- a `rufAt`
    run of the pipeline's program from the declared initial memory -- is inhabited. -/
theorem boot_ist_maschine_zeuge :
    ∃ (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn) (o : Orte u) (hs : GabbroV.sp0OkB u = true)
      (σ σ' : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params o.main))
      (v : ErgVal (declOf u) ((declOf u).erg o.main)),
      uebersetzeAllg gross = .ok ⟨u, P, fs⟩ ∧ Parser.Cover.Differenz.akzeptiertU u = .ok true ∧ imKernB u = true ∧
      startWelt u o hs [97, 98, 67] = .ok σ ∧
      rufAt P (orakelLeer (declOf u)) ({} : Budget).passes ({} : Budget).tiefe o.main σ ρ = .ok σ' v ∧
      ausgabe u o σ' = .ok [65, 66, 67] := by
  apply boot_ist_maschine
  cases h : boot {} gross [97, 98, 67] with
  | error e =>
    have := boot_gross
    rw [h] at this
    cases this
  | ok a =>
    have := boot_gross
    rw [h] at this
    cases this
    rfl

end Gabbro.Stage0.Zeuge
