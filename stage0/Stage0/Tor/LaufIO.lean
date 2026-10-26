/-
  File:      stage0/Stage0/Tor/LaufIO.lean
  Subject:   **Stage 0 with real system calls on real OS threads.** Two phases:

  1. `faden` (IO): every running thread of the machine (`main` and the program's roots, `anfaengeVon`) runs on an OS
     thread of its own. A step of the fast machine (`Schnell/`) is taken under the world lock (`weltNimm`, a futex
     word), under the oracle of the answers logged so far, and filed in the schedule. A question (`frage?`) is answered by the
     real system call OUTSIDE the lock, so a thread blocked in the kernel holds up no other; the answer is filed
     under its key (`schluessel`) and the thread steps with it. A thread that cannot step sleeps until another
     one has stepped (`weltWarte`).
  2. `nachspielen` (pure) replays the schedule on the fast machine under the oracle of the WHOLE log, every question
     it meets answered in the log. Its result carries `RufErreichbarG`: `nachspiel_ist_lauf`
     -- the run is a run of the thread machine under the oracle that answers with the observed system-call results.

  Two threads asking under one key could not be told apart by the oracle: phase 1 refuses that run instead of
  guessing, and also a question whose arguments moved while its system call ran.
-/
import Stage0.Tor.Ausfuehren
import Stage0.Lauf.Boot

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- **What the threads of phase 1 share**, under the world lock. -/
structure Geteilt (u : UProg) (n : Nat) where
  s : FStand n (declOf u)
  log : List (Antwort (declOf u)) := []
  /-- The keys asked, with the thread that asked. -/
  wer : List ((Nat × List Int) × Faden) := []
  /-- The schedule, newest first. -/
  plan : List Faden := []
  schritte : Nat := 0
  /-- `some (.ok ())` once thread 0 has ended, `some (.error e)` once the run stopped. -/
  ende : Option (Except String Unit) := none

/-- The key a question of thread `f` is answered under. -/
def schluessel {u : UProg} {n : Nat} (s : FStand n (declOf u)) (f : Faden)
    (q : Σ a : (declOf u).Ax, World (declOf u) × Env (declOf u) ((declOf u).aparams a)) : Nat × List Int :=
  (fremdZahl q.2.1.spur + s.c f, kfVon u q.1 q.2.2)

section Phase1

variable (u : UProg) (P : Programm (declOf u)) (B : Budget) (tore : List Tor) (ww : World (declOf u))
  (M0 : RufMaschineG (declOf u)) {n : Nat} (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = [])
  (ref : IO.Ref (Geteilt u n))

/-- Under the lock: the step of thread `f`, filed; `false` when it cannot step. -/
def schritt (g : Geteilt u n) (f : Faden) : IO Bool := do
  match g.s.schritt P (kfVon u) g.log B.passes ww M0 h0 f with
  | some ⟨t, _⟩ =>
    let k := g.schritte + 1
    let ende := if fertig (t.F ww M0) 0 then some (.ok ())
      else if k ≥ B.schritte then some (.error "the step budget ran out") else none
    ref.set { g with s := t, plan := f :: g.plan, schritte := k, ende }
    pure true
  | none => pure false

/-- Under the lock: stop the run with an error. -/
def stopp (g : Geteilt u n) (e : String) : IO Unit :=
  ref.set { g with ende := some (.error e) }

/-- **One thread of phase 1**, until the run ends. -/
partial def faden (f : Faden) : IO Unit := do
  weltNimm
  let g ← ref.get
  if g.ende.isSome then
    weltGib
    return
  let weiter (ok : Bool) : IO Unit := do
    if ok then
      weltGib
      weltWecke
    else
      let gen ← weltGeneration
      weltGib
      weltWarte gen
    faden f
  match frage? (g.s.F ww M0) f with
  | none => weiter (← schritt u P B ww M0 h0 ref g f)
  | some q =>
    let k := schluessel g.s f q
    match g.wer.find? (·.1 == k) with
    | some (_, h) =>
      if h == f then weiter (← schritt u P B ww M0 h0 ref g f)
      else
        stopp u ref g s!"threads {h} and {f} ask under the same key; the oracle cannot tell them apart"
        weiter true
    | none =>
      ref.set { g with wer := (k, f) :: g.wer }
      weltGib
      let a ← (ausfuehren u tore (g.s.c f) q).toBaseIO
      weltNimm
      let g ← ref.get
      match a with
      | .error e =>
        stopp u ref g (toString e)
        weiter true
      | .ok a =>
        let g := { g with log := g.log ++ [a] }
        match frage? (g.s.F ww M0) f with
        | some q' =>
          if schluessel g.s f q' == k then weiter (← schritt u P B ww M0 h0 ref g f)
          else
            stopp u ref g "the arguments of a system call moved while it ran"
            weiter true
        | none =>
          stopp u ref g "a thread's question vanished while its system call ran"
          weiter true

end Phase1

/-- The replay meets a question: it must be answered in the log. -/
def frageImLog {u : UProg} {n : Nat} (log : List (Antwort (declOf u))) (ww : World (declOf u))
    (M0 : RufMaschineG (declOf u)) (s : FStand n (declOf u)) (f : Faden) : Bool :=
  match frage? (s.F ww M0) f with
  | some q => log.any (·.schluessel == schluessel s f q)
  | none => true

/-- **Phase 2**: replay the schedule under the oracle of the whole log. -/
def nachspielen (u : UProg) (P : Programm (declOf u)) (passes : Nat) (log : List (Antwort (declOf u)))
    (ww : World (declOf u)) (M0 : RufMaschineG (declOf u)) {n : Nat} (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) :
    List Faden → SStand P (kfVon u) log passes ww M0 n → Except String (SStand P (kfVon u) log passes ww M0 n)
  | [], s => .ok s
  | f :: plan, s =>
    if hf : f < n then
      if frageImLog log ww M0 s.s f then
        match s.schritt h0 f hf with
        | some s' => nachspielen u P passes log ww M0 h0 plan s'
        | none => .error "the replay does not step where the run did"
      else .error "the replay asks a question the run did not answer"
    else .error "the schedule names a thread that does not run"

/-- **The replayed run and its output.** -/
def nachspiel (u : UProg) (P : Programm (declOf u)) (o : Orte u) (B : Budget) (σ : World (declOf u)) (m : Anfang u)
    (rs : List (Anfang u)) (hl : (offen (startSpur (D := declOf u) m.1)).isEmpty = true)
    (log : List (Antwort (declOf u))) (plan : List Faden) : Except String (List UInt8) := do
  let s ← nachspielen u P B.passes log σ (startG P σ m rs) (startG_ruhe P σ m rs hl) plan
    (SStand.start P (kfVon u) log B.passes σ (startG P σ m rs) (rs.length + 1))
  let F := s.s.F σ (startG P σ m rs)
  if fertig F 0 then ausgabe u o (F.weltVon 0) else throw "main did not end"

/-- **The run with system calls is the thread machine**: every output of the replay is read from a machine reachable
    from the start machine by `RufSchrittG` under the oracle answering with the observed system-call results, in
    which thread 0 has ended. -/
theorem nachspiel_ist_lauf {u : UProg} {P : Programm (declOf u)} {o : Orte u} {B : Budget} {σ : World (declOf u)}
    {m : Anfang u} {rs : List (Anfang u)} {hl} {log : List (Antwort (declOf u))} {plan : List Faden}
    {aus : List UInt8} (h : nachspiel u P o B σ m rs hl log plan = .ok aus) :
    ∃ M : RufMaschineG (declOf u),
      RufErreichbarG P (orakelZ (kfVon u) 0 log) B.passes (startG P σ m rs) M ∧ fertig M 0 = true ∧
        ausgabe u o (M.weltVon 0) = .ok aus := by
  unfold nachspiel at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i s _
    obtain ⟨M, hr, hF⟩ := s.steht
    split at h
    · rename_i hf
      refine ⟨M, hr, ?_, ?_⟩
      · rw [hF, fertig_normal] at hf
        exact hf
      · rw [hF] at h
        rw [← h]
        exact ausgabe_welt o _ _ _
    · cases h

/-- The subset of stage 0 with system calls: every foreign body is a gate bound on this machine; no device register,
    no open region. -/
def imKernIO (u : UProg) (tore : List Tor) : Bool :=
  u.axs.all (fun a => tore.any (·.name == a.name)) && u.regs.isEmpty && u.tabs.all (fun t => t.von.isNone)

/-- **Phase 1 on OS threads**: thread 0 on the calling thread, every other running thread on a dedicated one. The
    log and the schedule once the run ended. -/
def mehrfach (u : UProg) (P : Programm (declOf u)) (B : Budget) (tore : List Tor) (ww : World (declOf u))
    (M0 : RufMaschineG (declOf u)) {n : Nat} (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) :
    IO (Except String (List (Antwort (declOf u)) × List Faden)) := do
  let ref ← IO.mkRef ({ s := FStand.start ww M0 n } : Geteilt u n)
  for f in List.range n do
    if f != 0 then
      let _ ← IO.asTask (prio := .dedicated) (faden u P B tore ww M0 h0 ref f)
  faden u P B tore ww M0 h0 ref 0
  let g ← ref.get
  match g.ende with
  | some (.error e) => pure (.error e)
  | _ => pure (.ok (g.log, g.plan.reverse))

/-- **STAGE 0 with system calls**: check, run on OS threads with real system calls (phase 1), replay (phase 2). A
    program that binds no gate gets the input bytes `ein` in `io.ein`; one that binds gates reads for itself, and
    `ein` is not run. -/
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
              match lowerAllg u, anfaengeVon u o with
              | .error e, _ | _, .error e => pure (.error e)
              | .ok (P, _), .ok (m, rs) =>
                let bytes ← if tore.isEmpty then ein else pure []
                match startWelt u o h bytes with
                | .error e => pure (.error e)
                | .ok σ =>
                  if hl : (offen (startSpur (D := declOf u) m.1)).isEmpty = true then
                    match ← mehrfach u P B tore σ (startG P σ m rs) (n := rs.length + 1)
                        (startG_ruhe P σ m rs hl) with
                    | .error e => pure (.error e)
                    | .ok (log, plan) => pure (nachspiel u P o B σ m rs hl log plan)
                  else pure (.error "main holds locks by signature")
            else pure (.error "no declared initial memory (sp0)")

end Gabbro.Stage0
