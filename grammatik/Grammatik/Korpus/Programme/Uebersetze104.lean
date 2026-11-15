/-
  File:      Grammatik/Korpus/Programme/Uebersetze104.lean
  Subject:   witness home of the concrete 104 pins of the
             surface-to-U elaborator (`Parser.Elab.Uebersetze.Teil.Teil16`):
             the elaboration pin `u104elab`, the lowering pin `u104lower`,
             the projections they are checked through, the declaration data
             agreement `u104data`, and the fragment/footprint checks
             `u104fragment`/`u104fuss` on the Lean-parsed program.

  Pure move out of `Teil16` (AGENTS.md §5: heavy kernel evaluation
  belongs in a witness module of its own): no statement or name
  changes, same namespace, `Teil16` keeps only the generic `beq*`
  shape equalities.
-/
module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil16
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

theorem u104elab : beqElabU (elabU items104) (.ok uExp104) = true := by
  cbv

/-! ## The 104 instance: lowering pin, data, checks -/

/-- The lowered 104 program is the exporter's `gP`/`gFs`
    (definitional: proof irrelevance covers the proof terms). -/
theorem u104lower :
    lowerProg uExp104 =
      .ok (G104_referenz.gP, G104_referenz.gFs) := by cbv

/-- Projections of the elaborated program (the left column of
    the data agreement below). -/
def uAnzahl104 (u : UProg) : Int :=
  match u.tabs with
  | [t] => t.count
  | _ => -1

def uWeite104 (u : UProg) : Int × Int :=
  match u.tabs with
  | [{ name := _, count := _, cols := [(_, w)], bools := _, arena := _, opts := _, shared := _, von := _, werte := _, wraps := _, sumNamen := _, sumFelder := _, kanten := _, idxNamen := _, breiten := _, owner := _, space := _ }] => w
  | _ => (-1, -1)

def uRang104 (u : UProg) : Int :=
  match u.locks with
  | [l] => l.rank
  | _ => -1

def uFn104 (u : UProg) (n : String) : Option UFn :=
  u.fns.find? (fun f => strEq f.name n)

def uParams104 (u : UProg) (n : String) : List Ty :=
  match uFn104 u n with
  | .some f => f.params.map (·.2)
  | .none => []

def uHeld104 (u : UProg) (n : String) : List String :=
  match uFn104 u n with
  | .some f => f.held
  | .none => []

def uSchreibt104 (u : UProg) (n : String) : List String :=
  match uFn104 u n with
  | .some f => f.puts
  | .none => []

/-- Declaration data agreement, construct by construct: the
    elaborated data agrees with the exporter's `gD` (via
    `u104lower`) and with the hand translation's `r4D` -- same
    shape as `export104_data`. -/
theorem u104data :
    uAnzahl104 uExp104 = 2 ∧
    r4D.count () = 2 ∧
    uWeite104 uExp104 = (0, 100) ∧
    r4D.typ () () = .int 0 100 ∧
    uRang104 uExp104 = 0 ∧
    r4D.rang () = 0 ∧
    uParams104 uExp104 "einzahlen" = [.ptr (.table 0 (true, true)), .index 2, .int 0 10] ∧
    r4D.params r4Ein = [.ptr (.table 0 (true, true)), .index 2, .int 0 10] ∧
    uParams104 uExp104 "lies" = [.ptr (.table 0 (true, false)), .index 2] ∧
    r4D.params r4Lies = [.ptr (.table 0 (true, false)), .index 2] ∧
    uHeld104 uExp104 "einzahlen" = ["M"] ∧
    r4D.haelt r4Ein = [()] ∧
    uSchreibt104 uExp104 "einzahlen" = ["Konto"] ∧
    r4D.schreibt r4Ein () = true ∧
    uSchreibt104 uExp104 "lies" = [] ∧
    r4D.schreibt r4Lies () = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The fragment check on the Lean-parsed program. -/
theorem u104fragment :
    (match lowerProg uExp104 with
     | .ok (P, fs) => programmImFragmentG P fs
     | .error _ => false) = true := by
  rw [u104lower]
  exact export104_fragment

/-- The footprint check on the Lean-parsed program. -/
theorem u104fuss :
    (match lowerProg uExp104 with
     | .ok (P, fs) => fussOrtGB P fs
     | .error _ => false) = true := by
  rw [u104lower]
  exact export104_fuss

end Gabbro.Grammatik.Parser.Uebersetze

#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104elab
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104lower
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104data
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104fragment
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104fuss
