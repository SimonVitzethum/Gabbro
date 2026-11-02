module

public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Speichermodell.Adressen.Platzierung

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/Platzierung.lean
  Subject:   **C14: static placement read off the source.** The alignment and the section of every
             `static` (`.globT`), kept instead of dropped, as `PlatzEintrag`s with the identity of the
             object (module path and name), the evaluated alignment, the section name and whether the
             static is written; and the Bool that admits them against a checked profile policy.

  * `platzL` -- the placement requests of an item list; an alignment that is no constant (a literal or a
    constant name) is refused, a missing alignment is `1`;
  * `platzB` -- every entry has a power-of-two alignment (`ausrichtungB`) and a section the policy knows,
    neither writable-and-executable nor mismatched with the static's mutability; object identities are
    distinct;
  * `platzOk_von_platzB` -- the model consequence: with the exporter's correspondence from the model's
    globals to their entries and a layout whose bases lie on the alignments, `PlatzOk` holds.

  The elaborator keeps refusing `static` placement (`uGlobs`: "static placement requires Stage-0 global base alignment, section-policy binding and image relocation correspondence") until the
  layout, startup initialisation and image relocation proofs of IR-03/06/12 consume this certificate:
  metadata alone discharges no placement.
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

/-- One static's placement request. -/
structure PlatzEintrag where
  objekt : List String
  ausrichtung : Nat
  abschnitt : Option String
  schreibbar : Bool
  deriving DecidableEq, Repr

mutual
/-- The literal constants of an item (`const N : T = 8;`), modules opened. -/
def konstenI : SItemTief → List (String × Nat)
  | .modT _ b => konstenL b
  | .pubT it => konstenI it
  | .gateT it => konstenI it
  | .constT n _ (.one (.lit v)) => [(n, v)]
  | _ => []
/-- The list form. -/
def konstenL : List SItemTief → List (String × Nat)
  | [] => []
  | it :: rest => konstenI it ++ konstenL rest
end

/-- An alignment expression: a literal or a literal constant. -/
def ausrichtungWert (ks : List (String × Nat)) : SExpr → Option Nat
  | .lit k => some k
  | .variable c => (ks.find? (fun p => strEq p.1 c)).map (·.2)
  | _ => none

mutual
/-- The placement requests of an item, with the module path they stand in. -/
def platzI (ks : List (String × Nat)) (modul : List String) : SItemTief → Except String (List PlatzEintrag)
  | .modT n b => platzL ks (modul ++ [n]) b
  | .pubT it => platzI ks modul it
  | .gateT it => platzI ks modul it
  | .globT m n _ _ al sec _ =>
    match al with
    | none => .ok [⟨modul ++ [n], 1, sec, m⟩]
    | some e =>
      match ausrichtungWert ks e with
      | some a =>\n        if ausrichtungB a then .ok [⟨modul ++ [n], a, sec, m⟩]\n        else .error "static alignment must be a positive power of two"
      | none => .error "static alignment is not a constant"
  | _ => .ok []
/-- The list form. -/
def platzL (ks : List (String × Nat)) (modul : List String) :
    List SItemTief → Except String (List PlatzEintrag)
  | [] => .ok []
  | it :: rest =>
    match platzI ks modul it with
    | .error e => .error e
    | .ok a =>
      match platzL ks modul rest with
      | .error e => .error e
      | .ok b => .ok (a ++ b)
end

/-- The placement requests of a (selected) tree. -/
def platzierungVon (items : List SItemTief) : Except String (List PlatzEintrag) :=
  platzL (konstenL items) [] items

/-- Distinct object identities. -/
def eindeutigB : List (List String) → Bool
  | [] => true
  | x :: xs => !(xs.any (fun y => decide (y = x))) && eindeutigB xs

/-- One entry against the checked policy (section name to rights). -/
def eintragOk (pol : List (String × Zugriff)) (e : PlatzEintrag) : Bool :=
  ausrichtungB e.ausrichtung &&
    match e.abschnitt with
    | none => true
    | some s =>
      match pol.find? (fun p => strEq p.1 s) with
      | none => false
      | some p => p.2.wxFrei && p.2.lesen && (p.2.schreiben == e.schreibbar)

/-- **The placement requests are admitted** against the policy. -/
def platzB (pol : List (String × Zugriff)) (es : List PlatzEintrag) : Bool :=
  es.all (eintragOk pol) && eindeutigB (es.map (·.objekt))

/-- The policy as the function the model asks for. -/
def politikFun (pol : List (String × Zugriff)) : AbschnittPolitik :=
  fun s => (pol.find? (fun p => strEq p.1 s)).map (·.2)

theorem platzB_eintrag {pol : List (String × Zugriff)} {es : List PlatzEintrag}
    (h : platzB pol es = true) {e : PlatzEintrag} (he : e ∈ es) : eintragOk pol e = true := by
  simp only [platzB, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 e he

theorem eintragOk_ausrichtung {pol : List (String × Zugriff)} {e : PlatzEintrag}
    (h : eintragOk pol e = true) : ausrichtungB e.ausrichtung = true := by
  simp only [eintragOk, Bool.and_eq_true] at h
  exact h.1

theorem eintragOk_abschnitt {pol : List (String × Zugriff)} {e : PlatzEintrag}
    (h : eintragOk pol e = true) {s : String} (hs : e.abschnitt = some s) :
    ∃ z, politikFun pol s = some z ∧ z.wxFrei = true ∧ z.lesen = true ∧ z.schreiben = e.schreibbar := by
  simp only [eintragOk, Bool.and_eq_true, hs] at h
  obtain ⟨_, h2⟩ := h
  cases hf : pol.find? (fun p => strEq p.1 s) with
  | none => simp [hf] at h2
  | some p =>
      simp only [hf, Bool.and_eq_true, beq_iff_eq] at h2
      refine ⟨p.2, ?_, h2.1.1, h2.1.2, h2.2⟩
      simp [politikFun, hf]

/-- The model placement of a correspondence from the model's globals to their source entries. -/
def platzVon (D : Deklaration) (gl : D.Glob → PlatzEintrag) : Platzierung D :=
  ⟨fun g => (gl g).ausrichtung, fun g => (gl g).abschnitt⟩

/-- **Admitted placements give `PlatzOk`**: every global's entry is among the admitted ones, and the layout
    puts every base on its alignment. -/
theorem platzOk_von_platzB {D : Deklaration} (lay : AdressLayout D) (pol : List (String × Zugriff))
    (es : List PlatzEintrag) (gl : D.Glob → PlatzEintrag) (hmem : ∀ g, gl g ∈ es)
    (h : platzB pol es = true) (hbase : ∀ g, lay.gbasis g % (gl g).ausrichtung = 0) :
    PlatzOk lay (platzVon D gl) (politikFun pol) (fun g => (gl g).schreibbar) := by
  refine ⟨fun g => eintragOk_ausrichtung (platzB_eintrag h (hmem g)), hbase, ?_⟩
  intro g s hs
  exact eintragOk_abschnitt (platzB_eintrag h (hmem g)) hs

end Gabbro.Grammatik.Parser.ProfilBindung
