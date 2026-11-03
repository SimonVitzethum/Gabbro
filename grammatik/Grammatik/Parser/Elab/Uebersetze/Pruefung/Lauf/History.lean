module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Herkunft
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Recording
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
public import Grammatik.Kern.Syntax.Satz.PruefungReplay
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Copyable observations only. A floor is a Bool, never an integer silently
    interpreted as a successful verdict. Capabilities have no encoding here. -/
inductive CheckAtom where
  | number (value : Int)
  | truth (value : Bool)
  deriving DecidableEq, Repr

def checkAtom (D : Deklaration) : (ty : Ty) → Wert D ty → Option CheckAtom
  | .int _ _, value => some (.number value.n)
  | .bool, value => some (.truth value)
  | _, _ => none

/-- These are the actual parameter values saved by G/GX, not a report
    supplied by a caller of the replay function. -/
def checkEnvAtoms {D : Deklaration} : {Γ : Ctx} → Env D Γ → List (Option CheckAtom)
  | _, .nil => []
  | _, @Env.cons _ ty _ value rest => checkAtom D ty value :: checkEnvAtoms rest

def CheckAtom.sample : CheckAtom → Int
  | .number value => value
  | .truth value => if value then 1 else 0

def checkFloorAtom : CheckAtom → Option Bool
  | .truth value => some value
  | .number _ => none

/-- Decode a source-indexed reporter activation. Missing locals are explicitly
    absent; missing required arguments or floor values refuse the record. -/
def decodeCheckSamples (site : UCheckReturn) (atoms : List (Option CheckAtom)) :
    Option (List CheckProbe) :=
  site.samples.mapM fun (place, position) => do
    match position with
    | none => pure { ort := place, punkt := site.point, wert := 0, gelesen := false }
    | some position =>
      let atom ← (atoms[position]?).join
      pure { ort := place, punkt := site.point, wert := atom.sample, gelesen := true }
def decodeCheckFloors (site : UCheckReturn) (atoms : List (Option CheckAtom)) :
    Option (List Bool) :=
  (List.range site.floorCount).mapM fun i => do
    let atom ← (atoms[site.floorStart + i]?).join
    checkFloorAtom atom

def decodeCheckWritten (site : UCheckReturn) (atoms : List (Option CheckAtom)) : Option Bool :=
  (atoms[site.floorStart + site.floorCount]?).join >>= checkFloorAtom

def decodeCheckReturn (site : UCheckReturn) (atoms : List (Option CheckAtom))
    (verdict : Bool) : Option CheckReport := do
  let samples ← decodeCheckSamples site atoms
  let floors ← decodeCheckFloors site atoms
  let written ← decodeCheckWritten site atoms
  if verdict != floors.foldl (fun result floor => result && floor) written then none
  else pure { proben := samples, boeden := floors, urteil := verdict }

/-- Every successful record proves its actual samples, every floor result,
    and the exact conjunction with the written verdict. An unrelated Bool or
    a report with fabricated sample values cannot satisfy this statement. -/
theorem decodeCheckReturn_origin (site : UCheckReturn) (atoms : List (Option CheckAtom))
    (verdict : Bool) (report : CheckReport)
    (origin : decodeCheckReturn site atoms verdict = some report) :
    decodeCheckSamples site atoms = some report.proben ∧
      decodeCheckFloors site atoms = some report.boeden ∧
      ∃ written, decodeCheckWritten site atoms = some written ∧
        report.urteil = report.boeden.foldl (fun result floor => result && floor) written := by
  cases hs : decodeCheckSamples site atoms with
  | none => simp [decodeCheckReturn, hs] at origin
  | some samples =>
    cases hf : decodeCheckFloors site atoms with
    | none => simp [decodeCheckReturn, hs, hf] at origin
    | some floors =>
      cases hw : decodeCheckWritten site atoms with
      | none => simp [decodeCheckReturn, hs, hf, hw] at origin
      | some written =>
        by_cases hv : verdict = floors.foldl (fun result floor => result && floor) written
        · simp [decodeCheckReturn, hs, hf, hw, hv] at origin
          cases origin
          exact ⟨hs, hf, written, hw, hv⟩
        · simp [decodeCheckReturn, hs, hf, hw, hv] at origin

/-- Read the actual saved arguments and actual returned Bool of a private
    reporter. No values are recovered from a later shared-memory snapshot. -/
def actualCheckReturn (u : UProg) (f : (declOf u).Fn)
    (env : Env (declOf u) ((declOf u).params f))
    (value : ErgVal (declOf u) ((declOf u).erg f)) : Option (String × CheckReport) := do
  let site ← (fnAt u f).checkReturn
  match he : (declOf u).erg f with
  | some .bool =>
    let report ← decodeCheckReturn site (checkEnvAtoms env) (he ▸ value)
    pure (site.check, report)
  | _ => none

/-- A completed Duty is consumed only once, choosing the most recent live
    invocation. The copyable report remains in history after retirement. -/
def consumeCheckEntry {D : Deklaration} (gate : D.Fn) :
    List (CheckEvidenz D) → Option (List (CheckEvidenz D))
  | [] => none
  | entry :: rest =>
    if entry.lebt then some ({ entry with lebt := false, tor := some gate } :: rest)
    else (consumeCheckEntry gate rest).map (entry :: ·)

/-- Equal values from different completed invocations remain different
    observation points. Pairing is ghost provenance, not a runtime clock. -/
def stampCheckReport (activation : Nat) (report : CheckReport) : CheckReport :=
  { report with proben := report.proben.map fun sample =>
      { sample with punkt := Nat.pair activation sample.punkt } }

theorem stampCheckReport_values (activation : Nat) (report : CheckReport) :
    (stampCheckReport activation report).proben.map (fun p => (p.ort, p.wert, p.gelesen)) =
      report.proben.map (fun p => (p.ort, p.wert, p.gelesen)) ∧
    (stampCheckReport activation report).boeden = report.boeden ∧
    (stampCheckReport activation report).urteil = report.urteil := by
  simp [stampCheckReport, List.map_map]

structure CheckGhostState (D : Deklaration) where
  frames : List D.Fn := []
  pending : Option CheckReport := none
  /-- Newest entry first, like the underlying G/GX call log. -/
  history : List (CheckEvidenz D) := []
  refused : Bool := false
  nextActivation : Nat := 0
  activation : Nat := 0

/-- The ghost update at the actual return. A reporter belongs to the current
    probe activation; only that probe's normal pop appends completed evidence.
    A consumer's return retires one existing entry, including its explicit
    reason-return policy. Unrelated activations preserve the history. -/
def checkGhostStep (u : UProg) (c : CheckDecl (declOf u))
    (consumer gate : (declOf u).Fn) (state : CheckGhostState (declOf u)) :
    RufEreignisF (declOf u) → CheckGhostState (declOf u)
  | .eintritt f _ _ =>
    { state with frames := f :: state.frames,
      pending := if f = c.probe then none else state.pending,
      activation := if f = c.probe then state.nextActivation else state.activation,
      nextActivation := if f = c.probe then state.nextActivation + 1 else state.nextActivation }
  | .rueck f env value s0 s1 => Id.run do
    let mut result := { state with frames := state.frames.drop 1 }
    if state.frames.head? != some f then
      return { result with refused := true }
    if f = c.probe then
      match state.pending with
      | some report =>
        if rueckUrteil c (.rueck f env value s0 s1) = some report.urteil then
          result := { result with pending := none,
            history := ⟨c.probe, report, true, none⟩ :: state.history }
        else result := { result with pending := none, refused := true }
      | none => result := { result with refused := true }
    else if f = consumer then
      match consumeCheckEntry gate state.history with
      | some history => result := { result with history }
      | none => result := { result with refused := true }
    else if (state.frames.drop 1).head? == some c.probe then
      match actualCheckReturn u f env value with
      | some (name, report) =>
        if name == c.name then result :=
          { result with pending := some (stampCheckReport state.activation report) }
      | none => pure ()
    return result
  | .why f _ _ _ _ =>
    let result := { state with frames := state.frames.drop 1,
      pending := if f = c.probe then none else state.pending }
    if state.frames.head? != some f then { result with refused := true }
    else if f = consumer then
      match consumeCheckEntry gate state.history with
      | some history => { result with history }
      | none => { result with refused := true }
    else result

/-- G/GX logs are newest-first. Fold in execution order, append evidence only
    at normal probe returns, and keep the report after physical consumption. -/
def checkGhostHistory (u : UProg) (c : CheckDecl (declOf u))
    (consumer gate : (declOf u).Fn) (log : List (RufEreignisF (declOf u))) :
    CheckGhostState (declOf u) :=
  log.reverse.foldl (checkGhostStep u c consumer gate) {}

/-- Each new G/GX call event updates the existing history once. The real
    machine prepends events; replay reverses that convention exactly once. -/
theorem checkGhostHistory_event (u : UProg) (c : CheckDecl (declOf u))
    (consumer gate : (declOf u).Fn) (event : RufEreignisF (declOf u))
    (log : List (RufEreignisF (declOf u))) :
    checkGhostHistory u c consumer gate (event :: log) =
      checkGhostStep u c consumer gate (checkGhostHistory u c consumer gate log) event := by
  simp [checkGhostHistory, List.reverse_cons, List.foldl_append]

/-- An actually run check cannot finish with an unconsumed Duty or an invalid
    second consumption. Merely declaring a check still makes no run occur. -/
def checkGhostComplete {D : Deklaration} (state : CheckGhostState D) : Bool :=
  !state.refused && state.pending.isNone && state.history.all (fun entry => !entry.lebt)

/-- A reporter's actual parameter capture is appended at its enclosing
    probe's actual normal return. This is the generic return-site law used
    with `checkGhostHistory_event`, for G and GX alike. -/
theorem checkGhostStep_probe_return (u : UProg) (c : CheckDecl (declOf u))
    (consumer gate reporter : (declOf u).Fn)
    (notProbe : reporter ≠ c.probe) (notConsumer : reporter ≠ consumer)
    (args : Env (declOf u) ((declOf u).params reporter))
    (value : ErgVal (declOf u) ((declOf u).erg reporter))
    (probeArgs : Env (declOf u) ((declOf u).params c.probe))
    (probeValue : ErgVal (declOf u) ((declOf u).erg c.probe))
    (before after : World (declOf u)) (report : CheckReport)
    (actual : actualCheckReturn u reporter args value = some (c.name, report))
    (verdict : rueckUrteil c (.rueck c.probe probeArgs probeValue before after) =
      some report.urteil) (history : List (CheckEvidenz (declOf u))) :
    (checkGhostStep u c consumer gate
      (checkGhostStep u c consumer gate
        { frames := [reporter, c.probe], history := history }
        (.rueck reporter args value before after))
      (.rueck c.probe probeArgs probeValue before after)).history =
        ⟨c.probe, stampCheckReport 0 report, true, none⟩ :: history := by
  simp [checkGhostStep, stampCheckReport, notProbe, notConsumer, actual, verdict]

/-- A real report's samples and floor outcomes survive consumption verbatim.
    This strengthens replay with its actual parameter provenance. -/
theorem replayEintrag_from_samples (u : UProg) (c : CheckDecl (declOf u))
    (site : UCheckReturn) {Γ : Ctx} (env : Env (declOf u) Γ)
    (verdict : Bool) (report : CheckReport) (gate : (declOf u).Fn)
    (origin : decodeCheckReturn site (checkEnvAtoms env) verdict = some report) :
    decodeCheckSamples site (checkEnvAtoms env) =
      some (replayEintrag c report gate).bericht.proben ∧
    decodeCheckFloors site (checkEnvAtoms env) =
      some (replayEintrag c report gate).bericht.boeden ∧
    ∃ written, decodeCheckWritten site (checkEnvAtoms env) = some written ∧
      (replayEintrag c report gate).bericht.urteil =
        report.boeden.foldl (fun result floor => result && floor) written :=
  decodeCheckReturn_origin site (checkEnvAtoms env) verdict report origin

/-- No report can be consumed twice without another producer completion. -/
theorem consumeCheckEntry_once (D : Deklaration) (c : CheckDecl D)
    (report : CheckReport) (gate : D.Fn) :
    consumeCheckEntry gate [⟨c.probe, report, true, none⟩] =
      some [replayEintrag c report gate] ∧
    consumeCheckEntry gate [replayEintrag c report gate] = none := ⟨rfl, rfl⟩

/-- Both memory models consult the same actual call data; ghost history never
    reads the presented weak-memory world, nor adds executable runtime work. -/
def checkGhostGX (u : UProg) (M : RufMaschineG (declOf u)) (thread : Faden)
    (c : CheckDecl (declOf u)) (consumer gate : (declOf u).Fn) :=
  checkGhostHistory u c consumer gate (M.faeden thread).log

theorem checkGhostGX_log (u : UProg) (M : RufMaschineG (declOf u)) (thread : Faden)
    (c : CheckDecl (declOf u)) (consumer gate : (declOf u).Fn) :
    checkGhostGX u M thread c consumer gate =
      checkGhostHistory u c consumer gate (M.faeden thread).log := rfl

end Gabbro.Grammatik.Parser.Uebersetze
