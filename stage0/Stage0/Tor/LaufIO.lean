/-
  File:      stage0/Stage0/Tor/LaufIO.lean
  Subject:   **Stage 0 with real system calls.** Two phases:

  1. `ausfuehrenLauf` (IO) runs the threads round robin; before a thread steps, the question its step asks
     (`frage?`) is answered by the real system call (`ausfuehren`) and filed in the log; the step itself is `zug`
     under the oracle of the log so far. It records the schedule.
  2. `nachspiel` (pure) replays the schedule from the start machine under the oracle of the WHOLE log, each step by
     `zug`, checking that every question it meets is in the log with the same argument words. Its result carries
     `RufErreichbarG`: `nachspiel_ist_lauf` -- the run is a run of the thread machine under the oracle that answers
     with the observed system-call results.

  A thread asks under a key (its trace length) at most once; two threads asking under the same key cannot be told
  apart by the model's oracle, so phase 1 refuses that run instead of guessing.
-/
import Stage0.Tor.Ausfuehren
import Stage0.Lauf.Boot

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- A machine whose threads outside `aktiv` hold nothing (the half of `Stand` that does not depend on the oracle). -/
structure RStand (D : Deklaration) (aktiv : List Faden) where
  M : RufMaschineG D
  ruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []

/-- One step of the first thread in `fs` that steps, its question answered first. `wer` files which thread asked
    under each key. -/
def versuche (u : UProg) (P : Programm (declOf u)) (passes : Nat) (tore : List Tor) {aktiv : List Faden}
    (s : RStand (declOf u) aktiv) (log : List (Antwort (declOf u))) (wer : List (Nat × Faden)) :
    List {f // f ∈ aktiv} → IO (Option (Faden × RStand (declOf u) aktiv × List (Antwort (declOf u)) × List (Nat × Faden)))
  | [] => pure none
  | ⟨f, hf⟩ :: fs => do
    let (log', wer') ← match frage? s.M f with
      | some q =>
        let k := q.2.1.spur.length
        match wer.find? (·.1 == k) with
        | some (_, g) =>
          if g == f then pure (log, wer)
          else throw (IO.userError s!"stage0: threads {g} and {f} ask under the same key {k}; the model cannot tell them apart")
        | none => do
          let a ← ausfuehren u tore q
          pure (log ++ [a], wer ++ [(k, f)])
      | none => pure (log, wer)
    match zug P (orakelLog log') passes (orakelLog_treu _) s.M f aktiv s.ruhe with
    | some z =>
      pure (some (f, ⟨z.1, fun g hg => by
        rw [rufSchrittG_fremd z.2 g (fun e => hg (e ▸ hf))]
        exact s.ruhe g hg⟩, log', wer'))
    | none => versuche u P passes tore s log' wer' fs

/-- **Phase 1**: at most `n` steps with real system calls; the log and the schedule. -/
def ausfuehrenLauf (u : UProg) (P : Programm (declOf u)) (passes : Nat) (tore : List Tor) {aktiv : List Faden} :
    Nat → List {f // f ∈ aktiv} → RStand (declOf u) aktiv → List (Antwort (declOf u)) → List (Nat × Faden) →
    List Faden → IO (RStand (declOf u) aktiv × List (Antwort (declOf u)) × List Faden)
  | 0, _, s, log, _, plan => pure (s, log, plan.reverse)
  | n + 1, reihe, s, log, wer, plan => do
    match ← versuche u P passes tore s log wer reihe with
    | some (f, s', log', wer') => ausfuehrenLauf u P passes tore n (nachRunde reihe f) s' log' wer' (f :: plan)
    | none => pure (s, log, plan.reverse)

/-- The replay meets a question: it must be in the log with the same argument words. -/
def frageImLog (u : UProg) (log : List (Antwort (declOf u))) (M : RufMaschineG (declOf u)) (f : Faden) : Bool :=
  match frage? M f with
  | some q =>
    match log.find? (·.schluessel == q.2.1.spur.length), argWorte u _ q.2.2 with
    | some a, .ok ws => a.worte == ws.map (fun w => match w with
        | ArgWort.zahl z => z
        | ArgWort.puffer t _ => -1 - (t.val : Int))
    | _, _ => false
  | none => true

/-- **Phase 2**: replay the schedule under the oracle of the whole log. -/
def nachspielen (u : UProg) (P : Programm (declOf u)) (passes : Nat) (log : List (Antwort (declOf u)))
    {M0 : RufMaschineG (declOf u)} {aktiv : List Faden} :
    List Faden → Stand P (orakelLog log) passes M0 aktiv → Except String (Stand P (orakelLog log) passes M0 aktiv)
  | [], s => .ok s
  | f :: plan, s =>
    if hf : f ∈ aktiv then
      if frageImLog u log s.M f then
        match zug P (orakelLog log) passes (orakelLog_treu _) s.M f aktiv s.ruhe with
        | some z =>
          nachspielen u P passes log plan ⟨z.1, .schritt _ _ f s.erreicht z.2, fun g hg => by
            rw [rufSchrittG_fremd z.2 g (fun e => hg (e ▸ hf))]
            exact s.ruhe g hg⟩
        | none => .error "the replay does not step where the run did"
      else .error "the replay asks a question the run did not answer"
    else .error "the schedule names a thread that does not run"

/-- **The replayed run and its output.** -/
def nachspiel (u : UProg) (P : Programm (declOf u)) (o : Orte u) (B : Budget) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params o.main)) (hl : (offen (startSpur (D := declOf u) o.main)).isEmpty = true)
    (log : List (Antwort (declOf u))) (plan : List Faden) : Except String (List UInt8) := do
  let M0 := startG P o σ ρ
  let s0 : Stand P (orakelLog log) B.passes M0 [0] := Stand.start M0 [0] (fun g _ => by
    show offen (startSpur (D := declOf u) o.main) = []
    simpa using hl)
  let s ← nachspielen u P B.passes log plan s0
  if fertig s.M 0 then ausgabe u o (s.M.weltVon 0) else throw "main did not end"

/-- **The run with system calls is the thread machine**: every output of the replay is read from a machine reachable
    from the start machine by `RufSchrittG` under the oracle answering with the observed system-call results, in
    which thread 0 has ended. -/
theorem nachspiel_ist_lauf {u : UProg} {P : Programm (declOf u)} {o : Orte u} {B : Budget} {σ : World (declOf u)}
    {ρ : Env (declOf u) ((declOf u).params o.main)} {hl} {log : List (Antwort (declOf u))} {plan : List Faden}
    {aus : List UInt8} (h : nachspiel u P o B σ ρ hl log plan = .ok aus) :
    ∃ M : RufMaschineG (declOf u),
      RufErreichbarG P (orakelLog log) B.passes (startG P o σ ρ) M ∧ fertig M 0 = true ∧
        ausgabe u o (M.weltVon 0) = .ok aus := by
  unfold nachspiel at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i s _
    split at h
    · exact ⟨s.M, s.erreicht, by assumption, h⟩
    · cases h

/-- The subset of stage 0 with system calls: every foreign body is a gate bound on this machine; no device register,
    no open region. -/
def imKernIO (u : UProg) (tore : List Tor) : Bool :=
  u.axs.all (fun a => tore.any (·.name == a.name)) && u.regs.isEmpty && u.tabs.all (fun t => t.von.isNone)

/-- **STAGE 0 with system calls**: check, run with real system calls (phase 1), replay (phase 2). A program that
    binds no gate gets the input bytes `ein` in `io.ein`; one that binds gates reads for itself, and `ein` is not
    run. -/
def bootIO (B : Budget) (src : String) (ein : IO (List UInt8)) : IO (Except String (List UInt8)) := do
  match lex src with
  | .error _ => pure (.error "lex")
  | .ok toks =>
    match parseTopTief toks with
    | .error e => pure (.error e)
    | .ok items =>
      match elabU (pre108 items), toreVon (uMembers (pre108 items)) with
      | .error e, _ | _, .error e => pure (.error e)
      | .ok u, .ok tore =>
        match akzeptiertU u with
        | .error e => pure (.error e)
        | .ok false => pure (.error "refused by the checker (AkzeptiertX)")
        | .ok true =>
          if imKernIO u tore = false then pure (.error "outside the stage-0 subset") else
          match orteVon u with
          | .error e => pure (.error e)
          | .ok o =>
            if h : sp0OkB u = true then
              match lowerAllg u with
              | .error e => pure (.error e)
              | .ok (P, _) =>
                let bytes ← if tore.isEmpty then ein else pure []
                match startWelt u o h bytes with
                | .error e => pure (.error e)
                | .ok σ =>
                  match zeigerArgs ((declOf u).params o.main) with
                  | none => pure (.error "main takes a parameter that is not a table pointer")
                  | some ρ =>
                    if hl : (offen (startSpur (D := declOf u) o.main)).isEmpty = true then
                      let M0 := startG P o σ ρ
                      let r0 : RStand (declOf u) [0] := ⟨M0, fun g _ => by
                        show offen (startSpur (D := declOf u) o.main) = []
                        simpa using hl⟩
                      let (_, log, plan) ← ausfuehrenLauf u P B.passes tore B.schritte [⟨0, by simp⟩] r0 [] [] []
                      pure (nachspiel u P o B σ ρ hl log plan)
                    else pure (.error "main holds locks by signature")
            else pure (.error "no declared initial memory (sp0)")

end Gabbro.Stage0
