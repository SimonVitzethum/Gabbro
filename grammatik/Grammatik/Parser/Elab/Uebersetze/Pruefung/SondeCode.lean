module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- One private adapter per check/external-probe binding. Source identifiers
    cannot spell this name. The exact external text stays in `UCheck.sonde`. -/
def sondeFnName (checkName externalName : String) : String :=
  checkName ++ "#sonde#" ++ externalName

/-- An external counterprobe is an ordinary Boolean function or C08 binding.
    Declaring its label does not manufacture a successful external run. -/
def uSondeFn (fns : List UFn) (foreignHeads : List UFnKopf)
    (c : UCheck) (externalName : String) : Except String UFn := do
  let body ← match fns.find? (fun f => strEq f.name externalName) with
    | some f =>
      if !f.params.isEmpty || !f.resBool || f.gruende != 0 then
        .error ("counterprobe requires a parameterless reason-free bool function: " ++ externalName)
      else if !f.nimmt.isEmpty || !f.gibt.isEmpty then
        .error ("counterprobe cannot transfer a Duty: " ++ externalName)
      else .ok [UStmt.bindCall "ans" externalName []]
    | none => match foreignHeads.find? (fun k => strEq k.name externalName) with
      | none => .error ("unbound counterprobe: " ++ externalName)
      | some k =>
        if !k.names.isEmpty || !k.griffe.isEmpty || !k.resBool || k.kanal.isSome then
          .error ("counterprobe requires a parameterless reason-free bool binding: " ++ externalName)
        else .ok [UStmt.bindAx "ans" externalName []]
  .ok {
    name := sondeFnName c.name externalName
    params := []
    kinds := []
    res := none
    resBool := true
    held := []
    puts := []
    gives := []
    needs := []
    body := body
    ret := .bool (.var "ans")
  }

/-- Generate the actual counterprobe calls and enforce one-to-one ownership
    before an elaborated unit can reach lowering or `checkB`. -/
def uSondenFns (fns : List UFn) (foreignHeads : List UFnKopf) :
    List UCheck → Except String (List UFn)
  | [] => .ok []
  | c :: rest => do
    let more ← uSondenFns fns foreignHeads rest
    match c.sonde with
    | none => .ok more
    | some (externalName, _) =>
      if rest.any (fun d => d.sonde.any (fun pair => strEq pair.1 externalName)) then
        .error ("counterprobe bound to multiple checks: " ++ externalName)
      else
        let adapter ← uSondeFn fns foreignHeads c externalName
        .ok (adapter :: more)

/-- Recheck generated adapter resolution when deriving descriptors. A modified
    unit cannot retain a counterprobe label after dropping its executable call. -/
def uSondenPruef (u : UProg) : Except String Unit := do
  let names := u.checks.filterMap fun c => c.sonde.map Prod.fst
  if (uEindeutig names).length != names.length then
    throw "counterprobe bound to multiple checks"
  for c in u.checks do
    match c.sonde with
    | none => pure ()
    | some (externalName, _) =>
      let some adapter := u.fns.find? fun f => strEq f.name (sondeFnName c.name externalName)
        | throw ("unbound counterprobe: " ++ externalName)
      let body ← match u.fns.find? (fun f => strEq f.name externalName) with
        | some f =>
          if !f.params.isEmpty || !f.resBool || f.gruende != 0 ||
              !f.nimmt.isEmpty || !f.gibt.isEmpty then
            .error ("counterprobe function changed: " ++ externalName)
          else .ok [UStmt.bindCall "ans" externalName []]
        | none => match u.axs.find? (fun a => strEq a.name externalName) with
          | none => .error ("unbound counterprobe: " ++ externalName)
          | some a =>
            if !a.params.isEmpty || a.res != some Ty.bool || a.gruende != 0 then
              .error ("counterprobe binding changed: " ++ externalName)
            else .ok [UStmt.bindAx "ans" externalName []]
      if !adapter.params.isEmpty || !adapter.resBool || adapter.gruende != 0 ||
          !adapter.nimmt.isEmpty || !adapter.gibt.isEmpty ||
          adapter.body != body || adapter.ret != URet.bool (.var "ans") then
        throw ("counterprobe adapter changed: " ++ externalName)

end Gabbro.Grammatik.Parser.Uebersetze
