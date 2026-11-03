/- C16 inventory item 16 (kernel half): connected export -- the export claim
    and its refusals.

    `CheckExportAnspruch` is what full closure needs at the kernel level: the
    resolved probe, gate and Duty names denote this check's fields and the
    check expands exactly. From it the gate discharge (`export_gate_treu`)
    follows by construction. The elaborator-side resolution (`uCheckIdx` over
    the actual `elabU` output, the source-text chain and the `declOf` Duty
    gap) lives in `Parser/Elab/Uebersetze/Pruefung/Export.lean`, which may
    import the elaborator; this file stays on the kernel side so `Satz.lean`
    keeps its import order.

    Refusals: a forged report (a completion claimed for a check whose probe
    never expanded, or with surplus outcomes) completes nothing, and a
    dropped Duty (no gate consuming it) discharges nothing. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section ExportAnspruch

variable [DecidableEq D.Fn]

/-- The export claim: the resolved probe, gate and Duty names denote this
    check's fields and the check expands exactly. -/
def CheckExportAnspruch (P : Programm D) (probe : D.Fn) (gates : List D.Fn)
    (duty : D.Marke × Nat) (c : CheckDecl D) : Prop :=
  c.probe = probe ∧ c.gates = gates ∧ c.duty = duty ∧ CheckExpansion P c

/-- The expansion travels with the claim. -/
theorem export_expansion {P : Programm D} {probe : D.Fn} {gates : List D.Fn}
    {duty : D.Marke × Nat} {c : CheckDecl D}
    (h : CheckExportAnspruch P probe gates duty c) : CheckExpansion P c :=
  h.2.2.2

/-- The claimed gates discharge the claimed Duty. -/
theorem export_gate_treu {P : Programm D} {probe : D.Fn} {gates : List D.Fn}
    {duty : D.Marke × Nat} {c : CheckDecl D}
    (h : CheckExportAnspruch P probe gates duty c) {g : D.Fn}
    (hg : g ∈ gates) : duty ∈ (D.signatur g).konsumiert := by
  obtain ⟨rfl, rfl, rfl, hexp⟩ := h
  exact CheckExpansion.gate_konsumiert hexp hg

/-! ## Refusals: forged reports and dropped Duties -/

/-- A check whose probe is one of its gates never expands: the fixture with
    the probe mistaken for a gate. -/
def pruefCAnderes : CheckDecl pruefD :=
  { pruefC with gates := [true] }

/-- The forged expansion is refused: probe freshness fails. -/
theorem expansion_fremd_abgelehnt : ¬ CheckExpansion pruefP pruefCAnderes :=
  fun h => absurd (List.mem_singleton_self _) (CheckExpansion.probe_frisch h)

/-- A completion claimed for the forged check completes nothing. -/
theorem abschluss_fremd_zeuge :
    ¬ CheckAbschluss pruefP pruefCAnderes messBerichtWahr :=
  fun h => expansion_fremd_abgelehnt h.1

/-- A surplus floor outcome completes nothing, even on the admitted check. -/
theorem abschluss_fremd_ueberhang_zeuge :
    ¬ CheckAbschluss pruefP pruefC
      { proben := [], boeden := [true], urteil := true } := by
  intro h
  exact absurd h.2.2 (by decide)

/-- A check with no consuming gate: the Duty would be dropped. -/
def pruefCOhneTor : CheckDecl pruefD :=
  { pruefC with gates := [] }

/-- A dropped Duty discharges nothing: no gate consumes it. -/
theorem entladung_ohne_tor {P : Programm D} {r : CheckReport} {g : D.Fn} :
    ¬ CheckEntladung P pruefCOhneTor r g := by
  intro h
  exact absurd h.2.2 (by decide)

end ExportAnspruch

end Gabbro.Grammatik
