/- C16: the generated Boolean producers -- from `can_fail` to `UFn`.

   `uProbeFn` elaborates one check's `can_fail` body into an ordinary
   parameterless Boolean function under the generated name
   (`probeFnName`): the head is synthesized (`bool`, no reason channel,
   no held locks, no written tables), the contracts are empty and the
   body runs through the ordinary `elabFn` pipeline after source-indexed
   recording inserts typed sample/floor calls at its actual returning sites.
   The bundle includes those private ordinary reporter functions. Only parser-shaped bodies
   (`SAnw.block`, what `parseBlock` produces) elaborate; anything else
   keeps the named refusal. In particular a probe never calls another
   probe: probes elaborate against the written heads only, so naming a
   probe is an unknown-function error, never an independent invocation.
   A generated name that meets a written function, a foreign body or an
   earlier probe is refused, never merged. The probe consumes and produces the
   check's Duty (`dutyName` as both `nimmt` and `gibt`, C16 mark threading);
   read-only shape, Boolean exits and gate consumption are decided by the checker
   (`CheckAdmission`), not here. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Recording

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- The synthesized head of a probe: implemented, parameterless, `bool`,
    reason-free and clause-free. -/
def probeSig (pname : String) : FnSig :=
  { art := "", name := pname, params := [], res := some (.atom "bool"), fehler := none, klauseln := [] }

/-- Elaborate one check's `can_fail` body into its generated producer. -/
def uProbeFn (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (whys : List UWhy)
    (sums : List USum) (devs : List String) (regs : List UReg) (zustaende : List UZustand)
    (specs : List (String × List String × SExpr)) (arrKonst : List (String × USide))
    (zeiger : List String) (zb : Nat) (c : SCheck) : Except String (UFn × List UFn) := do
  match c.canFail with
  | .block ss ende =>
    let pname := probeFnName c.cname
    match elabKopf consts alias tabs locks globs whys sums (probeSig pname) devs zeiger zb with
    | .error e => .error e
    | .ok (kopf, schreibt) =>
      let ctx := uCtxVon alias consts tabs locks globs kopf pname [] whys sums regs zustaende specs arrKonst
      let (recorded, reporters, sampleHeads, _) ←
        recordCheckCode koepfe c 100000 ctx 0 (.block ss ende)
      match elabFn ctx (koepfe ++ sampleHeads) [] recorded with
      | .error e => .error e
      | .ok (gives, needs, body, r) => .ok ({ name := pname, params := [], kinds := [], res := none, resBool := true, resOpt := none, resSum := none, resWhy := none, resTy := none, gruende := 0, held := [], puts := schreibt, gputs := [], nimmt := [dutyName c.cname], gibt := [dutyName c.cname], gives := gives, needs := needs, body := body, ret := r, boden := none }, reporters)
  | _ => .error "check body without G form"

/-- A generated name that meets a written function or foreign body is refused. -/
def uProbeNeu (belegt : List String) (bekannt : List String) (pname : String) : Except String Unit :=
  if belegt.any (fun n => strEq n pname) || bekannt.any (fun n => strEq n pname) then .error ("duplicate probe: " ++ pname) else .ok ()

def uProbeFnsAux (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (whys : List UWhy)
    (sums : List USum) (devs : List String) (regs : List UReg) (zustaende : List UZustand)
    (specs : List (String × List String × SExpr)) (arrKonst : List (String × USide))
    (zeiger : List String) (zb : Nat) (belegt bekannt : List String) : List SCheck → Except String (List UFn)
  | [] => .ok []
  | c :: rest =>
    match uProbeNeu belegt bekannt (probeFnName c.cname) with
    | .error e => .error e
    | .ok _ =>
      match uProbeFn consts alias tabs locks globs koepfe whys sums devs regs zustaende specs arrKonst zeiger zb c with
      | .error e => .error e
      | .ok (f, reporters) =>
        match uProbeFnsAux consts alias tabs locks globs koepfe whys sums devs regs zustaende specs arrKonst zeiger zb belegt (probeFnName c.cname :: bekannt) rest with
        | .error e => .error e
        | .ok fs => .ok (f :: (reporters ++ fs))

/-- Elaborate every `can_fail` body of the unit into its generated producer. -/
def uProbeFns (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (whys : List UWhy)
    (sums : List USum) (devs : List String) (regs : List UReg) (zustaende : List UZustand)
    (specs : List (String × List String × SExpr)) (arrKonst : List (String × USide))
    (zeiger : List String) (zb : Nat) (belegt : List String) (checks : List SCheck) : Except String (List UFn) :=
  uProbeFnsAux consts alias tabs locks globs koepfe whys sums devs regs zustaende specs arrKonst zeiger zb belegt [] checks

end Gabbro.Grammatik.Parser.Uebersetze
