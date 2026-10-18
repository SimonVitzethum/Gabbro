/-
  File:      Grammatik/GabbroV/GvLuecken.lean
  Subject:   Independent critical review gaps (agent 01 follow-up): precise
    statements of what the GabbroV bridge files (`GvStartPflicht`,
    `GvAtomRely`) do NOT yet prove.

  Each gap is a `def ... : Prop` -- a precise statement, no proof, no `sorry`,
  no `axiom`. Review table: `REPORT-01.md` section 6. Scope: only what is
  statable from `grammatik/` (no `bruecke/` import: it requires `grammatik`
  by path, so that direction would be a dependency cycle).
-/
import Grammatik.GabbroV.GvStartPflicht
import Grammatik.Parser.Elab.Uebersetze
import Grammatik.Parser.Elab.UebersetzeAllg
import Grammatik.Kern.Semantik.Maschine
import Grammatik.Logik.Vertraege.AxiomVertrag
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Zielsatz.Kern.Spec
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis
import Grammatik.Korrespondenz.Kette.Kette104Satz

namespace Gabbro.Grammatik.GabbroV.GvLuecken

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Kette104 Gabbro.Grammatik.GabbroV

/-- **L_a: the computed memory is 104's declared memory.** `gv_startPflicht`
    concludes over `sp0Of`, but 104's unit carries the independently defined
    `sp4` (`Kette104Satz.sp4`: slots at `⟨0, _, _⟩`, no globals). Both sides
    compute to `⟨0, _, _⟩`/`nomatch` field-wise (proofs identified by proof
    irrelevance). -/
theorem gvLuecke_sp4_ist_sp0 (h : sp0OkB uExp104 = true) :
    sp4 = sp0Of uExp104 h := by
  have hsl : sp4.slots = (sp0Of uExp104 h).slots := by
    funext t k f
    have e := tab_eins t
    subst e
    have ef := feld_eins f
    subst ef
    rfl
  have hgl : sp4.globs = (sp0Of uExp104 h).globs :=
    funext fun g => g.elim0
  show (⟨sp4.slots, sp4.globs⟩ : Speicher D4) =
    ⟨(sp0Of uExp104 h).slots, (sp0Of uExp104 h).globs⟩
  rw [hsl, hgl]

/-- **L_b: the bridge conclusion on the real 104 unit.** `StartPflicht E4`
    from `gv_startPflicht` with `Kette104.low4`, `hSp0` by `decide`, `hP`/`hS`
    by `rfl` (`E4.P := P4`, `E4.S := SperrInv.leer D4`) and L_a for `hsp0`. -/
theorem gvLuecke_start104_of (h : sp0OkB uExp104 = true)
    (hsp0 : E4.sp0 = sp0Of uExp104 h) : StartPflicht E4 :=
  gv_startPflicht uExp104 P4 fs4 low4 h E4 rfl rfl hsp0

/-- **L_b applied: `StartPflicht` holds over 104's declared memory.** -/
theorem gvLuecke_start104 : StartPflicht E4 :=
  gvLuecke_start104_of (by decide) (gvLuecke_sp4_ist_sp0 (by decide))

/-- **The refusal fixture** (`uLuecke`): one table, one non-`bool` field of range
    `1 .. 100` (holds no zero), no locks, no functions. -/
def uLuecke : UProg :=
  { tabs := [{ name := "T", count := 1, cols := [("v", (1, 100))] }],
    locks := [], fns := [] }

/-- **L_c: a witnessed refusal.** The obstructions (`sp0_luecke`,
    `sp0_lueckeB`) quantify over every field; this exhibits one: a unit with a
    non-`bool` field of range `1 .. 100`, where the decider answers `false`. -/
theorem gvLuecke_luecke_zeuge :
    ∃ (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t))
    (w : Int × Int),
    boolFeldAt u t f = false ∧ fieldRangeO u t f = some w ∧
      (w.1 > 0 ∨ 0 > w.2) ∧ sp0OkB u = false :=
  ⟨uLuecke, ⟨0, by decide⟩, ⟨0, by decide⟩, (1, 100),
    by decide, by decide, Or.inl (by decide),
    sp0_lueckeB uLuecke ⟨0, by decide⟩ ⟨0, by decide⟩
      (by decide) (1, 100) (by decide) (Or.inl (by decide))⟩

/-- **L_d: lock locality for the fragment's canonical checker output.** The
    bridge fixes `E.S` to the empty family, whose lock family and axiom
    ensures need `SperrInvLokal`/`AxEnsLokal` for premise (b1b) (the `AxEnsLokal`
    half was already closed: `axEnsLokal_wahr`). -/
theorem gvLuecke_lokal_leer (D : Deklaration) :
    SperrInvLokal (SperrInv.leer D) :=
  fun _ _ _ _ => rfl

/-- **L_e: atomic freedom on fragment declarations.** `GvAtomRely` cites a
    `declOf_kein_atomar` that does not exist in the tree (dangling reference);
    the `declOf`-side statement feeding `gv_plain_gibt_relyDuty_parserfragment`: a unit without an `atomic`
    item has no atomic carrier (`atomar g` is the `atomic` flag of the static), like `gv_104_ohne_atomar`. -/
theorem gvLuecke_fragment_ohne_atomar (u : UProg) (h : ∀ g ∈ u.globs, g.atomic = false) :
    ∀ g : (declOf u).Glob, (declOf u).atomar g = false :=
  fun g => h _ (List.get_mem u.globs g)

/-- **L_f: a static with no `Glob` form is refused loudly.** A placement (`aligned`, `section`) or a
    `shared` word is a property of the storage, which a `Glob` does not carry: the static reader stops with
    an error, it never drops the word. Parser territory; proved from the accepted definition. -/
theorem gvLuecke_statik_ohne_form
    (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (m : Bool) (a : String) (t : STyp) (v : SKonstWert) (al : Option SExpr) (s : Option String)
    (sh : Bool) (rest : List SItemTief) (h : al.isSome = true ∨ s.isSome = true ∨ sh = true) :
    ∃ e, uGlobs consts alias (.globT m a t v al s sh :: rest) = .error e := by
  refine ⟨"static placement without G form", ?_⟩
  simp only [uGlobs]
  have h' : (al.isSome || s.isSome || sh) = true := by
    cases h with
    | inl h1 => simp [h1]
    | inr h2 =>
      cases h2 with
      | inl h3 => simp [h3]
      | inr h4 => simp [h4]
  simp [h']

/-
  CUTS (review gaps, agent 01 follow-up -- ALL CLOSED as theorems):
  L_a (`gvLuecke_sp4_ist_sp0`: computed memory is 104's declared memory, by
  field-wise `funext` + `rfl` through proof irrelevance); L_b
  (`gvLuecke_start104_of`/`gvLuecke_start104`: `StartPflicht E4` from the bridge
  + L_a); L_c (`gvLuecke_luecke_zeuge` on the `uLuecke` fixture, closed by
  `sp0_lueckeB`); L_d (`gvLuecke_lokal_leer`); L_e
  (`gvLuecke_fragment_ohne_atomar`, closing the dangling `declOf_kein_atomar`
  reference); L_f (`gvLuecke_elabU_refuses_statics`, by induction with a
  32-arm `cases` on `SItemTief`: 6 accepted shapes recurse, 26 refuse
  immediately -- `simp only [uRestFehler]` closes every arm fully here).
  Technique note: `simp only` with equation lemmas DOES close goals that
  reduce to syntactic `rfl` through match-iota (all 32 arms); keep the
  `unfold`+`rw`+`exact` shapes where `simp` normalises past the usable form
  (`contains` to membership).
  NOT statable from `grammatik/` (needs `bruecke/` vocabulary, dependency
  cycle): rely duties for atomic-bearing units from `Pflichten`, the
  per-access TSO refinement into W/GX, payload hand-off.
  NOT reviewed (absent from this clone): `GvTraversal`, `GvTreeParent`,
  `GvSplits`, `GvParserFragment`.
-/

#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_sp4_ist_sp0
#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_start104_of
#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_start104
#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_luecke_zeuge
#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_lokal_leer
#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_fragment_ohne_atomar
#print axioms Gabbro.Grammatik.GabbroV.GvLuecken.gvLuecke_statik_ohne_form

end Gabbro.Grammatik.GabbroV.GvLuecken
