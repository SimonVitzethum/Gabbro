/- Part 2 of 7 of `RufMaschineG`: the step relation of the call machine G. Its 86 rules live in
   `RufMaschineG/Schritt/G1` … `G7` (one inductive per group, every file below 500 lines); this file
   joins them and generates the constructor theorems `RufSchrittG.blatt` … with the old signatures. -/
module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G1
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G2
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G3
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G4
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G5
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G6
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G7
public meta import Lean.Elab.Command

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **One step of the call machine with compound statements.** `blatt`,
    `ruf`, `rueck` are the F steps (residues wrapped in `GRest.ende`); the
    `dann*`/`ende*`/`frei`/`trav`/`wieder`/`ewig` steps unfold compounds
    into the continuation residue. Reads go through the read world
    `(weltVon).lese Λ orte` exactly as `execStmt` reads them.

    Lock discipline (repaired 2026-09-13): a lock is taken ONLY by the
    `locks` unfold (`dannLocks`) and released ONLY by its release marker
    (`freiGib`, the `frei` peels of `leave`/`next`, or one head scope
    of `rueckFreigabe`/`rueckFreigabeLetzte`) -- the structured
    `locks L { … }` of the surface language. The bare `nimmt`/`gibt` steps
    of the old PC machine (take or release any lock at any time) are gone;
    a start thread holds its signature locks from the start machine on
    (`RufStartG`). Every step that reads the thread world (`weltVon`, a
    `lese`) or writes memory demands `HeldIn` of the head's static
    holdings: every lock they name is held. (Until the held-set relaxation of
    2026-09-13 it demanded `HeldGenau`, EQUAL sets; a callee now runs under
    the extra locks of its caller -- `RufPasst.hh` is `⊆` -- and those are
    held by the thread but not named by the callee frame.) Hence "static
    holdings ⊆ held locks" is an invariant of every run
    (`rufG_haelt_statisch`), and the side condition always holds. -/
inductive RufSchrittG (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | g1 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG1 P O passes M f M') : RufSchrittG P O passes M f M'
  | g2 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG2 P O passes M f M') : RufSchrittG P O passes M f M'
  | g3 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG3 P O passes M f M') : RufSchrittG P O passes M f M'
  | g4 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG4 P O passes M f M') : RufSchrittG P O passes M f M'
  | g5 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG5 P O passes M f M') : RufSchrittG P O passes M f M'
  | g6 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG6 P O passes M f M') : RufSchrittG P O passes M f M'
  | g7 {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
      (h : RufSchrittG7 P O passes M f M') : RufSchrittG P O passes M f M'

end Gabbro.Grammatik

/-- **The 80 rules as constructor theorems of `RufSchrittG`.** For every constructor `c` of a group
    `RufSchrittG<k>` this adds `RufSchrittG.c` with exactly the signature `c` had when the rules formed one
    inductive, proved by `RufSchrittG.g<k> (c …)`; building a step reads as before. -/
meta def ruf_schritt_konstruktoren : Lean.Elab.Command.CommandElabM Unit :=
  Lean.Elab.Command.liftTermElabM do
    let env ← Lean.getEnv
    for k in List.range 7 do
      let grp := Lean.Name.mkStr `Gabbro.Grammatik s!"RufSchrittG{k + 1}"
      let some (.inductInfo ind) := env.find? grp | throwError "missing {grp}"
      let wrap := Lean.Name.mkStr `Gabbro.Grammatik.RufSchrittG s!"g{k + 1}"
      for c in ind.ctors do
        let some (.ctorInfo ci) := env.find? c | throwError "missing {c}"
        let lvls := ci.levelParams.map Lean.Level.param
        let (type, value) ← Lean.Meta.forallTelescope ci.type fun xs body => do
          let args := body.getAppArgs
          let newBody := Lean.mkAppN (.const `Gabbro.Grammatik.RufSchrittG lvls) args
          let proof := Lean.mkAppN (.const wrap lvls) (args.push (Lean.mkAppN (.const c lvls) xs))
          return (← Lean.Meta.mkForallFVars xs newBody, ← Lean.Meta.mkLambdaFVars xs proof)
        let name := Lean.Name.mkStr `Gabbro.Grammatik.RufSchrittG c.getString!
        Lean.addDecl (.thmDecl { name, levelParams := ci.levelParams, type, value })

run_cmd ruf_schritt_konstruktoren
