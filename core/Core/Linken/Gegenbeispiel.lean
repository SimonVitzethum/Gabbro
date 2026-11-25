module

public import Core.Linken.Modul
public import Core.Annahme.Annahme
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme

/-- A fragment from a plain instruction list: no clauses, empty scope, no entries, no memory. -/
def codeFrag (code : List Befehl) : Fragment :=
  ⟨code, .leer, [], fun _ => none, .leer⟩

theorem codeFrag_code (code : List Befehl) : (codeFrag code).code = code :=
  rfl

theorem codeFrag_klauseln (code : List Befehl) : (codeFrag code).klauseln = .leer :=
  rfl

/-- Part A: straight-line code dividing 10 by 2. -/
def fragA : Fragment :=
  codeFrag [.literal 0 10, .literal 1 2, .teilen 0]

/-- Part B: straight-line code with a back jump to its own start. -/
def fragB : Fragment :=
  codeFrag [.literal 0 5, .literal 1 0, .zurueckSprung 3]

theorem fragA_code : fragA.code = [.literal 0 10, .literal 1 2, .teilen 0] :=
  rfl

theorem fragB_code : fragB.code = [.literal 0 5, .literal 1 0, .zurueckSprung 3] :=
  rfl

/-- The two modules carry no interface: the point is control flow, not calls. -/
def modulA : Modul :=
  { name := "a", fragment := fragA, exporte := [], importe := [] }

def modulB : Modul :=
  { name := "b", fragment := fragB, exporte := [], importe := [] }

/-- The witness plan: A linked before B, entry at A. -/
def planAB : Bauplan :=
  { module := [modulA, modulB], abhaengigkeiten := [], plattform := .x86_64, einstieg := "a" }

/-- The current link check accepts the witness plan. -/
theorem planAB_ok : bauplanOk planAB = true := by
  decide

/-- The linked code is the concatenation: the divider runs with B's divisor. -/
theorem planAB_code : (verknuepfteFragmente planAB).code =
    [.literal 0 10, .literal 1 2, .teilen 0, .literal 0 5, .literal 1 0, .zurueckSprung 3] := by
  rfl

/-- Linking the witness plan succeeds under the current check. -/
theorem planAB_linke : linke planAB = some (verknuepfteFragmente planAB) := by
  unfold linke
  rw [if_pos planAB_ok]

/-- Every instruction of B is guard-free. -/
theorem fragB_guard (b : Befehl) (present : b ∈ fragB.code) (frame : Rahmen) :
    b.guard frame = none := by
  rw [fragB_code] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

/-- Part B alone is accepted: guard-free with empty clauses. -/
theorem fragB_akzeptiert : Akzeptiert (fragB.einheit .x86_64) :=
  Fragment.akzeptiert_ohne_bedarf fragB _ (codeFrag_klauseln _) (fun b present frame => fragB_guard b present frame)

end Gabbro.Core.Linken
