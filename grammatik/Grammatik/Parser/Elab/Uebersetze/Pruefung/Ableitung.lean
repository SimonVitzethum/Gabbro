/- C16 close-out (1): from the elaborated unit to the kernel descriptor.

    The lead's Marke-carrying declaration (`declOf` with `Marke = Fin u.marken.length`,
    C12) closes the gap `uCheckDecl_unbewohnt` pinned: the Duty of every elaborated
    check resolves to a declared linear mark of `declOf u` through the C12 mark table
    (`markFin`), and `uCheckDecl`/`uCheckDecls` derive the kernel `CheckDecl`s --
    the probe and the Duty-consuming gate wrappers (`torHuellenName`) resolved by
    name, the measured places rendered without inventing tables, one floor entry per
    elaborated floor (source floors name no gate; the expected verdict of a written
    floor is that it holds -- the floor-to-gate binding and evaluation stay the
    C16/C08 remainder the admission does not decide).

    `nimmtAt_singleton`/`gibtAt_singleton` carry the Duty through the signatures:
    a probe with `nimmt = gibt = [duty]` consumes and produces exactly that mark
    (`mkSig`/`sigAt`), and no table owner is ever produced (`eigner_nie_erzeugt`,
    refused up front by `uGibtPruef`). `checkOkB_abgeleitet` admits a derived check
    in `checkB` from its elaborated shape; `checkB_einzeln` lifts one admitted check
    to the unit admission. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.SondeCode
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2
public import Grammatik.Parser.Elab.Generic.SignatureData
public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The Duty of a check as a declared mark: its index in the unit's mark table
    (C12), refused by name when undeclared. -/
def uDutyIdx (u : UProg) (c : UCheck) : Except String (Fin u.marken.length) :=
  match hm : markFin u.marken c.duty with
  | some i => .ok i
  | none => .error ("duty unknown: " ++ c.duty)

/-- A resolved Duty names its mark-table entry. -/
theorem uDutyIdx_trifft (u : UProg) (c : UCheck) (i : Fin u.marken.length)
    (h : uDutyIdx u c = .ok i) : markFin u.marken c.duty = some i := by
  have h2 : (uDutyIdx u c).toOption = some i := by rw [h]; rfl
  have h3 : (uDutyIdx u c).toOption = markFin u.marken c.duty := rfl
  rw [h3] at h2
  exact h2

/-- A resolved Duty is declared: its name stands in the mark table. -/
theorem uDutyIdx_deklariert (u : UProg) (c : UCheck) (i : Fin u.marken.length)
    (h : uDutyIdx u c = .ok i) : c.duty ∈ u.marken := by
  have hm := uDutyIdx_trifft u c i h
  have he : u.marken.get i = c.duty := markFin_get u.marken c.duty i hm
  rw [← he]
  exact List.get_mem u.marken i

/-- A measured place rendered without inventing tables: the variable, the
    dotted field path, the indexed slot path. -/
def messOrtName : UMessOrt → String
  | .variable n => n
  | .feld b f => b ++ "." ++ f
  | .stelle b f i => b ++ "." ++ f ++ "[" ++ toString i ++ "]"

/-- One elaborated check as a kernel descriptor over the unit's own declaration:
    the probe and the Duty-consuming gate wrappers resolved by name (the wrapper,
    not the written gate, is what `CheckDecl.gates` names), the Duty resolved
    against the mark table at stage 0, one floor entry per elaborated floor. -/
def uCheckDecl (u : UProg) (c : UCheck) : Except String (CheckDecl (declOf u)) := do
  let duty ← uDutyIdx u c
  let p ← fnIdx u.fns c.probe
  let gs ← uSeq (c.tore.map fun g => fnIdx u.fns (torHuellenName c.name g))
  .ok { name := c.name, claim := c.claim, misst := c.misst.map messOrtName,
    gates := gs, probe := p, duty := (duty, 0),
    boden := c.boeden.map fun _ => ("", true),
    sonde := c.sonde, testbau := c.testbau }

/-- Every elaborated check of the unit as a kernel descriptor. -/
def uCheckDecls (u : UProg) : Except String (List (CheckDecl (declOf u))) := do
  uSondenPruef u
  uSeq (u.checks.map (uCheckDecl u))

/-- The derivation from resolved parts: the record the derivation builds. -/
theorem uCheckDecl_ok (u : UProg) (c : UCheck)
    (i : Fin u.marken.length) (p : Fin u.fns.length) (gs : List (Fin u.fns.length))
    (hi : uDutyIdx u c = .ok i) (hp : fnIdx u.fns c.probe = .ok p)
    (hg : uSeq (c.tore.map fun g => fnIdx u.fns (torHuellenName c.name g)) = .ok gs) :
    uCheckDecl u c = .ok { name := c.name, claim := c.claim,
      misst := c.misst.map messOrtName, gates := gs, probe := p, duty := (i, 0),
      boden := c.boeden.map fun _ => ("", true),
      sonde := c.sonde, testbau := c.testbau } := by
  unfold uCheckDecl
  rw [hi, hp, hg]

/-- The derived Duty is the resolved mark at stage 0. -/
theorem uCheckDecl_duty (u : UProg) (c : UCheck) (d : CheckDecl (declOf u))
    (i : Fin u.marken.length) (p : Fin u.fns.length) (gs : List (Fin u.fns.length))
    (hi : uDutyIdx u c = .ok i) (_hp : fnIdx u.fns c.probe = .ok p)
    (_hg : uSeq (c.tore.map fun g => fnIdx u.fns (torHuellenName c.name g)) = .ok gs)
    (hd : d = { name := c.name, claim := c.claim,
      misst := c.misst.map messOrtName, gates := gs, probe := p, duty := (i, 0),
      boden := c.boeden.map fun _ => ("", true),
      sonde := c.sonde, testbau := c.testbau }) :
    d.duty = (i, 0) ∧ markFin u.marken c.duty = some d.duty.1 := by
  subst hd
  exact ⟨rfl, by simpa using uDutyIdx_trifft u c i hi⟩

/-! ## The Duty through the signatures -/

/-- A singleton `nimmt` resolves to exactly that mark at stage 0. -/
theorem nimmtAt_singleton (u : UProg) (f : UFn) (m : String)
    (i : Fin u.marken.length)
    (h1 : f.nimmt = [m]) (h2 : markFin u.marken m = some i) :
    nimmtAt u f = [(i, 0)] := by
  simp [nimmtAt, h1, h2]

/-- A singleton `gibt` resolves to exactly that mark at stage 0, where no table
    claims it as its owner (the `uGibtPruef` side, kept by `eigner_nie_erzeugt`). -/
theorem gibtAt_singleton (u : UProg) (f : UFn) (m : String)
    (i : Fin u.marken.length)
    (h1 : f.gibt = [m]) (h2 : markFin u.marken m = some i)
    (h3 : u.tabs.all (fun t => decide (t.owner ≠ some m)) = true) :
    gibtAt u f = [(i, 0)] := by
  simp [gibtAt, h1, h2, h3]

/-! ## The derived check in `checkB` -/

/-- A check in the derived shape is admitted: the probe answers `Bool` on a
    reason-free channel, threads exactly the Duty, stays read-only over the
    given carriers, and every gate wrapper discharges that same Duty. -/
theorem checkOkB_abgeleitet (u : UProg) (P : Programm (declOf u))
    (tabs : List (declOf u).Tab) (globs : List (declOf u).Glob)
    (fns : List (declOf u).Fn)
    (c : UCheck) (duty : Fin u.marken.length)
    (probe : Fin u.fns.length) (gates : List (Fin u.fns.length))
    (d : CheckDecl (declOf u))
    (hd : d = { name := c.name, claim := c.claim,
      misst := c.misst.map messOrtName, gates := gates, probe := probe,
      duty := (duty, 0), boden := c.boeden.map fun _ => ("", true),
      sonde := c.sonde, testbau := c.testbau })
    (herg : (fnAt u probe).ergTy = some .bool)
    (hgru : (fnAt u probe).gruende = 0)
    (hnimmt : (fnAt u probe).nimmt = [c.duty])
    (hgibt : (fnAt u probe).gibt = [c.duty])
    (hmark : markFin u.marken c.duty = some duty)
    (heigner : u.tabs.all (fun t => decide (t.owner ≠ some c.duty)) = true)
    (hro_t : tabs.all (fun t => !(((declOf u).signatur probe).schreibt t)) = true)
    (hro_g : globs.all (fun g => !(((declOf u).signatur probe).gschreibt g)) = true)
    (hgates_nimmt : ∀ g ∈ gates, (fnAt u g).nimmt = [c.duty])
    (hprobe_mem : probe ∈ fns)
    (hgates_mem : ∀ g ∈ gates, g ∈ fns)
    (hfrisch : probe ∉ gates)
    (hnodup : gates.Nodup)
    (hrahmen : rahmenOkB P tabs globs fns d = true) :
    checkOkB P tabs globs fns d = true := by
  subst hd
  have hkons : ((declOf u).signatur probe).konsumiert = [(duty, 0)] := by
    show (sigAt u probe.val).konsumiert = _
    rw [sigAt_konsumiert, nimmtAt_singleton u _ _ _ hnimmt hmark]
  have hprod : ((declOf u).signatur probe).produziert = [(duty, 0)] := by
    show (sigAt u probe.val).produziert = _
    rw [sigAt_produziert, gibtAt_singleton u _ _ _ hgibt hmark heigner]
  have hergS : (declOf u).erg probe = some .bool := by
    rw [erg_eq, herg]
  have hgruS : ((declOf u).signatur probe).gruende = 0 := by
    have e : (sigAt u probe.val).gruende = (fnAt u probe).gruende := by
      rw [sigAt_get]
    rw [show (declOf u).signatur probe = sigAt u probe.val from rfl, e, hgru]
  have hgates_all : gates.all
      (fun g => decide ((duty, 0) ∈ ((declOf u).signatur g).konsumiert) &&
        decide (g ∈ fns)) = true := by
    refine List.all_eq_true.mpr fun g hg => ?_
    have hk : ((declOf u).signatur g).konsumiert = [(duty, 0)] := by
      show (sigAt u g.val).konsumiert = _
      rw [sigAt_konsumiert, nimmtAt_singleton u _ _ _ (hgates_nimmt g hg) hmark]
    simp only [hk, decide_eq_true_eq, List.mem_singleton, Bool.and_eq_true]
    exact ⟨rfl, hgates_mem g hg⟩
  have htor : toreEindeutig gates = true := toreEindeutig_iff.mpr hnodup
  unfold checkOkB
  rw [decide_eq_true hergS, decide_eq_true hgruS,
    decide_eq_true (show ((declOf u).signatur probe).konsumiert = [(duty, 0)] from hkons),
    decide_eq_true (show ((declOf u).signatur probe).produziert = [(duty, 0)] from hprod),
    hro_t, hro_g, hgates_all, htor,
    decide_eq_true hfrisch, decide_eq_true hprobe_mem, hrahmen]

/-- One admitted check is the unit admission over its singleton. -/
theorem checkB_einzeln (u : UProg) (P : Programm (declOf u))
    (tabs : List (declOf u).Tab) (globs : List (declOf u).Glob)
    (fns : List (declOf u).Fn) (d : CheckDecl (declOf u))
    (h : checkOkB P tabs globs fns d = true) :
    checkB P tabs globs fns [d] = true := by
  unfold checkB
  simp only [List.all_cons, List.all_nil, h, Bool.true_and]
  decide

end Gabbro.Grammatik.Parser.Uebersetze
