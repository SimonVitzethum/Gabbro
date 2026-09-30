import Grammatik.Schlusssatz
import Bruecke.Pruefung
import Bruecke.Start
import Bruecke.Atomar

/-!
# P6: the duties of a SOURCE TEXT, computed in Lean -- and one generic theorem over every source

The principle (Simon, 2026-09-30): nothing in the compiler or the checker is there for particular
programs; GabbroV is proved ALWAYS right by generic theorems over every source text. This file is
that statement for premise (b) of the goal theorem:

* `Pflichten src` is a `Prop` COMPUTED from the text: the Lean front end `uebersetzeAllg` elaborates
  `src` (`uOf`), and the duties are `meetsU` of every function (the statement a person proves),
  next to the Bool checks of the unit's shape (`nullB`, `stimmigB`, `rangB`). Nothing printed by
  Rust is in it.
* `nutzer_aus_quelle` is the theorem over EVERY `src`: if the front end accepts `src` and
  `Pflichten src` is proved, premise (b) (`NutzerPflicht`, and with the atomic rely
  `NutzerPflichtA`) holds for the unit `einheitAllg` built from what the front end produced.
* `einheitAllg` is the unit: the parsed program, no lock invariant, the trivial axiom ensures, no
  declared start, the ZERO memory (the C's statics are zero-initialised). A field whose range
  does not contain 0 has no zero memory -- `nullB` refuses it by name, and no theorem here
  claims anything about such a unit.

What a person (or `gabbro prove --template`) supplies for a concrete text is a WITNESS `u` with
`uOf src = some u`, checked by the kernel against the text (`decide +kernel`): an untrusted hint,
like a proof term. The statement stays the computed one.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The elaborated program of a source text, if the Lean front end accepts it. -/
def uOf (src : String) : Option UProg :=
  match uebersetzeAllg src with
  | .ok ⟨u, _, _⟩ => some u
  | .error _ => none

/-- Every declared field's range contains 0: the zero memory exists. -/
def nullB (u : UProg) : Bool :=
  u.tabellen.all fun t => t.felder.all fun f => decide (f.2.1 ≤ 0) && decide (0 ≤ f.2.2)

theorem null_bereich {u : UProg} (h : nullB u = true) (t : Fin u.tabellen.length)
    (f : Fin (fieldCount u t)) (w : Int × Int) (hw : fieldRangeO u t f = some w) :
    w.1 ≤ 0 ∧ 0 ≤ w.2 := by
  unfold fieldRangeO at hw
  cases hf : (tabAt u t).felder[f.val]? with
  | none => rw [hf] at hw; simp at hw
  | some e =>
    rw [hf] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    subst hw
    have hte : tabAt u t ∈ u.tabellen := List.get_mem _ _
    have hfe : e ∈ (tabAt u t).felder := List.mem_of_getElem? hf
    unfold nullB at h
    rw [List.all_eq_true] at h
    have h1 := h _ hte
    rw [List.all_eq_true] at h1
    have h2 := h1 _ hfe
    simpa using h2

/-- The zero memory of the parser's declaration. -/
def nullSp (u : UProg) (h : nullB u = true) : Speicher (declOf u) where
  slots := fun t _ f => by
    show Wert (declOf u) (typAt u t f)
    unfold typAt
    cases hw : fieldRangeO u t f with
    | none => exact (⟨0, Int.le_refl _, Int.le_refl _⟩ : Zahl 0 0)
    | some w =>
      have := null_bereich h t f w hw
      exact (⟨0, this.1, this.2⟩ : Zahl w.1 w.2)
  globs := fun g => nomatch g

/-- The unit of a source the front end accepts: the parsed program, no lock invariant, the
    trivial axiom ensures, no declared start, the zero memory. -/
def einheitAllg (u : UProg) (P : Programm (declOf u)) (h : nullB u = true) : Zielsatz.Einheit (declOf u) where
  P := P
  S := SperrInv.leer (declOf u)
  Q := axWahr (declOf u)
  starts := []
  sp0 := nullSp u h

/-- The duties of a source text: THE STATEMENT, computed. `u` is not a free parameter: `uOf src =
    some u` fixes it, so a witness can only be the front end's own output. -/
def Pflichten (src : String) : Prop :=
  ∃ u : UProg, uOf src = some u ∧ nullB u = true ∧ stimmigB u = true ∧
    rangB u (rangAuto u) = true ∧
    ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body

/-- The lowering is the last stage of the front end. -/
theorem lower_of_uebersetze {src : String} {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    lowerAllg u = .ok (P, fs) := by
  unfold uebersetzeAllg at h
  cases hl : Parser.lex src with
  | error e => simp [hl] at h
  | ok toks =>
    simp only [hl] at h
    cases hp : Parser.parseTopTief toks with
    | error e => simp [hp] at h
    | ok items =>
      simp only [hp] at h
      cases he : elabU (pre108 items) with
      | error e => simp [he] at h
      | ok u' =>
        simp only [he] at h
        cases hw : lowerAllg u' with
        | error e => simp [hw] at h
        | ok r =>
          obtain ⟨P', fs'⟩ := r
          simp only [hw, Except.ok.injEq] at h
          injection h with h1 h2
          subst h1
          have h3 := eq_of_heq h2
          injection h3 with h4 h5
          subst h4 h5
          exact hw

theorem uOf_eq {src : String} {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) : uOf src = some u := by
  unfold uOf
  rw [h]

/-- **PREMISE (b) OF THE GOAL THEOREM FOR EVERY SOURCE TEXT** the Lean front end accepts, from the
    computed duties `Pflichten src` -- generic in `src`, no per-program fact in the statement. -/
theorem nutzer_aus_quelle {src : String} (hp : Pflichten src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨u', hu', hn, hs, hr, hz⟩ := hp
  rw [uOf_eq h] at hu'
  injection hu' with hu'
  subst hu'
  exact ⟨hn, bruecke_nutzer (lower_of_uebersetze h) (stimmig_of hs) (rangAuto u) (rang_of hr) hz
    _ rfl rfl rfl⟩

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`). -/
theorem nutzerA_aus_quelle {src : String} (hp : Pflichten src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) := by
  obtain ⟨hn, hb⟩ := nutzer_aus_quelle hp h
  exact ⟨hn, Zielsatz.nutzerPflichtA_ohne_atomar (declOf_kein_atomar u) hb⟩

#print axioms nutzer_aus_quelle
#print axioms nutzerA_aus_quelle

/-! ## The closed chain of a table-free unit, from the source

`Kette src` (`Grammatik/Schlusssatz.lean`) is the data of the translation-validation chain of a source
text: the parsed unit, the checker's Bool, premise (b), the emitter's layout and the correspondence
certificate. For a unit WITHOUT tables (and, as always here, without globals) the emitter's layout is
EMPTY -- there is no table block and no global block -- so it needs no per-program data: `emitLayLeer`.
`ketteAllg` assembles the chain from the generic pieces, and a per-program instance supplies only what
is a WITNESS: the Bool proofs (`decide`) and the certificate literal `gabbro corr-lean` prints, which
`korrOk` checks. Premise (b) is `nutzer_aus_quelle`. -/

/-- The emitter's layout of a unit with no tables and no globals: nothing is laid out. -/
def emitLayLeer (u : UProg) (ht : u.tabellen = []) : EmitLay (declOf u) where
  lay := fun _ => none
  tnr := fun t => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  tnr_inj := fun t _ _ => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  trec := fun t => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  lay_tab := fun t => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  trec_wf := fun t => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  trec_count := fun t => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  fnr := fun t _ => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  fnr_lt := fun t _ => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  fnr_inj := fun t _ _ _ => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  fnr_fits := fun t _ => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- `nullB` is part of the computed duties. -/
theorem pflichten_null {src : String} (hp : Pflichten src) {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) : nullB u = true := by
  obtain ⟨u', hu', hn, _⟩ := hp
  rw [uOf_eq h] at hu'
  injection hu' with hu'
  subst hu'
  exact hn

/-- The enumeration of the functions of a generically lowered unit. -/
def aufzFn (u : UProg) : Zielsatz.Aufzaehlung (declOf u).Fn := ⟨List.finRange u.fns.length, List.mem_finRange⟩

/-- The enumeration of the locks. -/
def aufzLock (u : UProg) : Zielsatz.Aufzaehlung (declOf u).Lock := ⟨List.finRange u.sperren.length, List.mem_finRange⟩

/-- The enumeration of the carriers of a unit with no tables and no globals: none. -/
def aufzTraegerLeer (u : UProg) (ht : u.tabellen = []) : Zielsatz.Aufzaehlung ((declOf u).Tab ⊕ (declOf u).Glob) :=
  ⟨[], fun c => match c with
    | .inl t => absurd (t : Fin u.tabellen.length).isLt (by simp [ht])
    | .inr g => nomatch g⟩

/-- **THE CLOSED CHAIN OF A TABLE-FREE UNIT, from its source text.** Premises: the computed duties
    `Pflichten src` (GabbroV's proofs), the front end's acceptance, the unit has no tables, the
    checker's Bool (a computation) and the certificate with its check (`korrOk`, a computation). -/
def ketteAllg {src : String} (hp : Pflichten src) {u : UProg} {P : Programm (declOf u)}
    {fs0 : List (declOf u).Fn} (h : uebersetzeAllg src = .ok ⟨u, P, fs0⟩) (ht : u.tabellen = [])
    (zert : KCert (declOf u))
    (hakz : akzeptiert_pruefer.akzeptiert (einheitAllg u P (pflichten_null hp h))
      (aufzFn u).1 (aufzLock u).1 (aufzTraegerLeer u ht).1 = true)
    (hz : korrOk (emitLayLeer u ht) fnNr zert P (aufzFn u).1 = true) : Kette src where
  u := u
  E := einheitAllg u P (pflichten_null hp h)
  fs0 := fs0
  uebersetzt := h
  fs := aufzFn u
  ls := aufzLock u
  cs := aufzTraegerLeer u ht
  akzeptiert := hakz
  nutzer := (nutzer_aus_quelle hp h).2
  EL := emitLayLeer u ht
  zert := zert
  zertOk := hz

end Gabbro.Bruecke
