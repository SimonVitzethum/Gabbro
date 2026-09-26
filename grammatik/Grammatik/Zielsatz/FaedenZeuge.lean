/-
  File:      Grammatik/Zielsatz/FaedenZeuge.lean -- the witnesses of the 2026-09-26 diff
             (threads created at run time; Opus agent A, OFFEN O21/O22).

  NON-DEGENERATE RUNS, memory-changing and multi-step, on the thread machine:
  * §2 `sj_lauf` -- a `start` spawns TWO threads, BOTH step (each writes the table) and
    finish, the starter waits for them while it holds nothing (`JoinWartet` in between,
    `sj_wartet_dazwischen`), the join fires only once both are finished, and the starter then
    takes two steps of its own (a call and a write) -- `sj_nicht_degeneriert`.
  * §3 `kw2_lauf` -- a `child` is spawned by a live parent and runs CONCURRENTLY with it: parent
    call, child write, parent write, and the parent never waits (`kw2_nicht_degeneriert`).
  * §4 `spawn_start_ziel`, `spawn_kind_ziel` -- THE GOAL ON SPAWN RUNS of an ACCEPTED unit:
    probe B's pool routine `haupt` (lock-guarded writer, ZielOrtZeuge.lean) as a run-time root
    (`gestartet`). The concrete checker accepts the units, (b)-(d) hold, and on a run in which
    the idle root starts two `haupt` threads (resp. a live `haupt` spawns a `haupt` child) and
    the spawned threads step and take the lock, `gabbro_ziel` gives every leg of `ZielF`.
  REFUSALS:
  * §5 `start_nicht_poolsicher_abgelehnt` -- a `start` of a root that writes a table unguarded
    (`hauptB` of the two-thread fixture) is refused by the checker Bool, at the pool component
    (the model side of `N462`); the same routine as an ordinary declared start is accepted.
  * §5 `kind_unter_sperre_abgelehnt` -- a `child` region inside `locks L` lifts to a root that
    needs `L` at entry (`wrap` of probe B, which holds the lock by signature); the Bool refuses
    it at the root component (`wurzelnB`, the model side of `N456`).
  * §5 `start_unter_sperre_kein_schritt` -- the model side of `N461`: no step makes a thread
    that holds a lock a joining starter; instantiated on probe B's run where thread 0 holds the
    lock (`start_unter_sperre_zeuge`).
-/
import Grammatik.Zielsatz.FaedenVor
import Grammatik.Zielsatz.PoolZeuge
import Grammatik.RufAdaequatG
import Grammatik.CloneHandoff

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. Two step shapes of the witness program `rufPF` -/

/-- The world after the writing leaf, from any memory: slot 0 := 2. -/
def outW (sp : Speicher rufDF) : World rufDF :=
  (((sp.welt []).lese (Signatur.anfang rufDF (rufDF.signatur rufIncF)) []).schreibSlot ()
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) 0 () ⟨2, by decide, by decide⟩)

theorem leaf_ok (sp : Speicher rufDF) : (execStmt rufOF 0 (R := keinRuf)
    (V := vertragVon rufDF rufIncF)
    (Λ := Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Λ' := Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF (sp.welt []) rufRhoF) =
    Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) (outW sp) rufRhoF := by
  unfold leafSF outW
  rfl

/-- A thread at the writing root's body. -/
def schreiberFaden (stapel : List (RufRahmenG rufDF)) (s0 : World rufDF)
    (log : List (RufEreignisF rufDF)) : RufFadenG rufDF :=
  ⟨stapel, ⟨rufIncF, rufRhoF, s0, ⟨false, rufDF.params rufIncF,
    Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF, .ende (.cons leafSF restF)⟩⟩,
    [], log⟩

/-- The same thread after its write: at the return. -/
def geschriebenFaden (stapel : List (RufRahmenG rufDF)) (s0 : World rufDF)
    (log : List (RufEreignisF rufDF)) (sp : Speicher rufDF) : RufFadenG rufDF :=
  ⟨stapel, ⟨rufIncF, rufRhoF, s0, ⟨false, rufDF.params rufIncF,
    Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF, .ende restF⟩⟩,
    (outW sp).spur, log⟩

/-- **The write step**: a thread at the writing body writes slot 0 := 2, from any memory. -/
theorem schreib_schritt (M : RufMaschineG rufDF) (t : Faden) (stapel : List (RufRahmenG rufDF))
    (s0 : World rufDF) (log : List (RufEreignisF rufDF))
    (hz : M.faeden t = schreiberFaden stapel s0 log) :
    ∃ M', RufSchrittG rufPF rufOF 0 M t M' ∧
      M'.faeden t = geschriebenFaden stapel s0 log M.speicher ∧
      M'.speicher = (outW M.speicher).speicher ∧ ∀ u, u ≠ t → M'.faeden u = M.faeden u := by
  have hw : M.weltVon t = M.speicher.welt [] := by
    unfold RufMaschineG.weltVon; rw [hz]; rfl
  have hstep : execStmt rufOF 0 keinRuf (V := vertragVon rufDF rufIncF) leafSF (M.weltVon t)
      rufRhoF = Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) (outW M.speicher) rufRhoF := by
    rw [hw]; exact leaf_ok M.speicher
  have herw : Erw (M.weltVon t) (outW M.speicher) := by
    refine ⟨(outW M.speicher).spur, ?_, ?_⟩
    · rw [hw]; exact (List.append_nil _).symm
    · intro e he
      simp [outW, World.schreibSlot, World.lese, World.merke] at he
      rcases he with rfl | he
      · rfl
      · simp [World.storeSlot, Speicher.welt] at he
  obtain ⟨M', hs, hZ⟩ := w_blatt (P := rufPF) (O := rufOF) (passes := 0) hz
    (leafSF : Stmt rufDF (vertragVon rufDF rufIncF) false _ _ _) restF rufRhoF leafSF_blatt rfl
    (heldLeerF _).heldIn (outW M.speicher) rufRhoF hstep herw
  exact ⟨M', hs, hZ.1, hZ.2, fun u hu => rufSchrittG_fremd hs u hu⟩

/-- A thread at the caller's body (`false`: it calls the writing function). -/
def rufenderFaden (stapel : List (RufRahmenG rufDF)) (s0 : World rufDF)
    (log : List (RufEreignisF rufDF)) : RufFadenG rufDF :=
  ⟨stapel, ⟨rufCallerF, rhoCallerF, s0, ⟨false, rufDF.params rufCallerF,
    Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF, .ende rufCallerRumpfF⟩⟩,
    [], log⟩

/-- The caller frame suspended past its call. -/
def gerufenRahmen (s0 : World rufDF) : RufRahmenG rufDF :=
  ⟨rufCallerF, rhoCallerF, s0,
   ⟨false, rufDF.params rufCallerF, nach rufDF rufIncF [], rhoCallerF, .ende callerRestG⟩⟩

/-- **The call step**: a thread at the caller's body enters the writing function, from any
    memory; afterwards it stands at the writing body one frame deep. -/
theorem ruf_schritt (M : RufMaschineG rufDF) (t : Faden) (stapel : List (RufRahmenG rufDF))
    (s0 : World rufDF) (log : List (RufEreignisF rufDF))
    (hz : M.faeden t = rufenderFaden stapel s0 log) :
    ∃ M', RufSchrittG rufPF rufOF 0 M t M' ∧
      (∃ r, M'.faeden t = schreiberFaden (r :: stapel) (M.speicher.welt [])
        (RufEreignisF.eintritt rufIncF rufRhoF (M.speicher.welt []) :: log)) ∧
      M'.speicher = M.speicher ∧ ∀ u, u ≠ t → M'.faeden u = M.faeden u := by
  have hw : M.weltVon t = M.speicher.welt [] := by
    unfold RufMaschineG.weltVon; rw [hz]; rfl
  have hhead : (M.faeden t).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .ende (.cons (.call rufIncF rufArgsF rufHpF rfl)
         ((rufDF_params rufCallerF).symm ▸
           (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
             Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
           Endblock rufDF (vertragVon rufDF rufCallerF) false
             (rufDF.params rufIncF) (nach rufDF rufIncF [])))⟩ := by
    rw [hz]; rfl
  have hΛ : HeldIn ([] : List (Res rufDF)) (offen (M.faeden t).spur) := (heldLeerF _).heldIn
  have hs0 : M.speicher.welt [] = (M.weltVon t).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF, hw]; rfl
  have hrho : rufRhoF = evalArgs (M.speicher.welt []) rufArgsF (M.speicher.welt []) rhoCallerF :=
    rfl
  have hneu : (M.speicher.welt []).spur = [] ++ (M.faeden t).spur := by rw [hz]; rfl
  have hs := RufSchrittG.ruf (P := rufPF) (O := rufOF) (passes := 0) M t false
    (rufDF.params rufCallerF) [] rufIncF rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho
    _ hneu
  refine ⟨_, hs, ?_, rfl, fun u hu => rufSchrittG_fremd hs u hu⟩
  have hst : (M.faeden t).stapel = stapel := by rw [hz]; rfl
  have hl : (M.faeden t).log = log := by rw [hz]; rfl
  simp only [rufUpdateG_self]
  rw [hst, hl]
  exact ⟨_, rfl⟩

/-- A thread that stands at the return of its only frame is finished. -/
theorem geschrieben_fertig {M : RufMaschineG rufDF} {t : Faden} {s0 : World rufDF}
    {log : List (RufEreignisF rufDF)} {sp : Speicher rufDF}
    (h : M.faeden t = geschriebenFaden [] s0 log sp) : FertigG M t := by
  unfold FertigG; rw [h]; exact ⟨rfl, rfl⟩

/-- A thread at the writing body is not finished. -/
theorem schreiber_nicht_fertig {M : RufMaschineG rufDF} {t : Faden}
    {stapel : List (RufRahmenG rufDF)} {s0 : World rufDF} {log : List (RufEreignisF rufDF)}
    (h : M.faeden t = schreiberFaden stapel s0 log) : ¬ FertigG M t := by
  unfold FertigG; rw [h]; intro ⟨_, h2⟩; exact Bool.false_ne_true h2

/-- The write leaves an event in the writer's own trace. -/
theorem outW_spur_ne (sp : Speicher rufDF) : (outW sp).spur ≠ [] := by
  simp [outW, World.schreibSlot, World.lese, World.merke]

/-- Slot 0 holds 2 after the write, from any memory. -/
theorem outW_slot (sp : Speicher rufDF) :
    (outW sp).speicher.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) :=
  rfl

/-! ## 2. `start`: two roots spawned, both step and finish, the join, the starter goes on -/

/-- Threads 1 and 2 sit at the writing root `true`; every other thread runs the caller. -/
def sjInit : Faden → Σ f : rufDF.Fn, Env rufDF (rufDF.params f) :=
  fun t => if t = 1 ∨ t = 2 then ⟨rufIncF, rufRhoF⟩ else ⟨rufCallerF, rhoCallerF⟩

/-- Threads 1 and 2 are dormant slots. -/
def sjLebt0 : Faden → Bool := fun t => !(decide (t = 1) || decide (t = 2))

def sjK0 : FadenMaschine rufDF := FadenStart rufPF spF sjInit sjLebt0

/-- The machine right after thread 0 starts the roots on 1 and 2 and waits. -/
def sjK1 : FadenMaschine rufDF :=
  ⟨sjK0.m, fun t => if t ∈ [1, 2] then true else sjK0.lebt t,
   fun t => if t = 0 then [1, 2] else sjK0.wartet t,
   fun t => if t ∈ [1, 2] then sjK0.rang 0 + 1 else sjK0.rang t, sjK0.uhr + 1⟩

theorem sj_schritt1 : FadenSchritt rufPF rufOF 0 sjK0 sjK1 :=
  FadenSchritt.start sjK0 0 [1, 2] rfl rfl rfl (by decide)

theorem sj_f0 : sjK0.m.faeden 0 =
    rufenderFaden [] (spF.welt []) [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] :=
  rfl

theorem sj_f1 : sjK0.m.faeden 1 =
    schreiberFaden [] (spF.welt []) [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := rfl

theorem sj_f2 : sjK0.m.faeden 2 =
    schreiberFaden [] (spF.welt []) [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := rfl

/-- **THE START-AND-JOIN RUN.** Thread 0 starts the dormant roots 1 and 2 (holding nothing) and
    waits; root 1 writes and finishes, root 2 writes and finishes; only then the join fires;
    thread 0 goes on with a call and a write of its own. Memory slot 0 moves from 0 to 2 by
    root 1's write. -/
theorem sj_lauf : ∃ K2 K3 K4 K5 K6 : FadenMaschine rufDF,
    FadenErreichbar rufPF rufOF 0 sjK0 K6 ∧
    -- the spawn: 1 and 2 dormant before, live after, 0 waits for both, holding nothing
    sjK0.lebt 1 = false ∧ sjK0.lebt 2 = false ∧ sjK1.lebt 1 = true ∧ sjK1.lebt 2 = true ∧
    sjK1.wartet 0 = [1, 2] ∧ offen (sjK1.m.faeden 0).spur = [] ∧
    -- root 1 stepped and finished, root 2 not yet: the starter WAITS (a join wait)
    FertigG K2.m 1 ∧ ¬ FertigG K2.m 2 ∧ JoinWartet K2 0 ∧ K2.wartet 0 = [1, 2] ∧
    -- both roots stepped (each writes: its own trace carries the event) and finished
    FertigG K3.m 1 ∧ FertigG K3.m 2 ∧ (K3.m.faeden 1).spur ≠ [] ∧ (K3.m.faeden 2).spur ≠ [] ∧
    -- the join ends the wait
    FadenSchritt rufPF rufOF 0 K3 K4 ∧ K4.wartet 0 = [] ∧ K4.m = K3.m ∧
    -- the starter goes on: a call (one frame deep), then a write of its own
    (K6.m.faeden 0).stapel.length = 1 ∧ (K6.m.faeden 0).spur ≠ [] ∧ K5.m ≠ K6.m ∧
    -- the memory moved: slot 0 was 0, root 1 wrote 2
    sjK0.m.speicher.slots () 0 () = (⟨0, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
    K2.m.speicher.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) := by
  -- root 1 writes
  obtain ⟨M2, s2, h2f, h2s, h2o⟩ := schreib_schritt sjK1.m 1 _ _ _ sj_f1
  let K2 : FadenMaschine rufDF := ⟨M2, sjK1.lebt, sjK1.wartet, sjK1.rang, sjK1.uhr⟩
  have t2 : FadenSchritt rufPF rufOF 0 sjK1 K2 := FadenSchritt.lauf sjK1 1 M2 rfl rfl s2
  -- root 2 writes
  have hz2 : M2.faeden 2 = schreiberFaden [] (spF.welt [])
      [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := by
    rw [h2o 2 (by decide)]; exact sj_f2
  obtain ⟨M3, s3, h3f, h3s, h3o⟩ := schreib_schritt M2 2 _ _ _ hz2
  let K3 : FadenMaschine rufDF := ⟨M3, K2.lebt, K2.wartet, K2.rang, K2.uhr⟩
  have t3 : FadenSchritt rufPF rufOF 0 K2 K3 := FadenSchritt.lauf K2 2 M3 rfl rfl s3
  have hf31 : M3.faeden 1 = geschriebenFaden [] (spF.welt [])
      [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] sjK1.m.speicher := by
    rw [h3o 1 (by decide)]; exact h2f
  -- the join
  have hF : ∀ u ∈ K3.wartet 0, FertigG K3.m u := by
    intro u hu
    have hu' : u = 1 ∨ u = 2 := by simpa [K3, K2, sjK1] using hu
    rcases hu' with rfl | rfl
    · exact geschrieben_fertig hf31
    · exact geschrieben_fertig h3f
  let K4 : FadenMaschine rufDF :=
    ⟨K3.m, K3.lebt, fun t => if t = 0 then [] else K3.wartet t, K3.rang, K3.uhr⟩
  have t4 : FadenSchritt rufPF rufOF 0 K3 K4 :=
    FadenSchritt.join K3 0 rfl (by simp [K3, K2, sjK1]) hF
  -- the starter calls
  have hz0 : M3.faeden 0 = rufenderFaden [] (spF.welt [])
      [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := by
    rw [h3o 0 (by decide), h2o 0 (by decide)]; exact sj_f0
  obtain ⟨M5, s5, ⟨r, h5f⟩, h5s, h5o⟩ := ruf_schritt M3 0 _ _ _ hz0
  let K5 : FadenMaschine rufDF := ⟨M5, K4.lebt, K4.wartet, K4.rang, K4.uhr⟩
  have t5 : FadenSchritt rufPF rufOF 0 K4 K5 := FadenSchritt.lauf K4 0 M5 rfl rfl s5
  -- the starter writes
  obtain ⟨M6, s6, h6f, h6s, h6o⟩ := schreib_schritt M5 0 _ _ _ h5f
  let K6 : FadenMaschine rufDF := ⟨M6, K5.lebt, K5.wartet, K5.rang, K5.uhr⟩
  have t6 : FadenSchritt rufPF rufOF 0 K5 K6 := FadenSchritt.lauf K5 0 M6 rfl rfl s6
  have hr : FadenErreichbar rufPF rufOF 0 sjK0 K6 :=
    .schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ .start
      sj_schritt1) t2) t3) t4) t5) t6
  refine ⟨K2, K3, K4, K5, K6, hr, rfl, rfl, rfl, rfl, rfl, rfl,
    geschrieben_fertig h2f, schreiber_nicht_fertig hz2, ⟨2, by simp [K2, sjK1],
      schreiber_nicht_fertig hz2⟩, rfl,
    geschrieben_fertig hf31, geschrieben_fertig h3f, ?_, ?_, t4, by simp [K4], rfl, ?_, ?_, ?_,
    rfl, ?_⟩
  · show (M3.faeden 1).spur ≠ []
    rw [hf31]; exact outW_spur_ne _
  · show (M3.faeden 2).spur ≠ []
    rw [h3f]; exact outW_spur_ne _
  · show (M6.faeden 0).stapel.length = 1
    rw [h6f]; rfl
  · show (M6.faeden 0).spur ≠ []
    rw [h6f]; exact outW_spur_ne _
  · show M5 ≠ M6
    intro e
    have h1 : (M5.faeden 0).spur = [] := by rw [h5f]; rfl
    have h2 := outW_spur_ne M5.speicher
    rw [e, h6f] at h1
    exact h2 h1
  · show M2.speicher.slots () 0 () = _
    rw [h2s]; exact outW_slot _

/-! ## 3. `child`: spawned by a live parent, concurrent with it -/

/-- Thread 1 sits at the writing root `true` (the child entry); every other thread is the caller. -/
def kwInit2 : Faden → Σ f : rufDF.Fn, Env rufDF (rufDF.params f) :=
  fun t => if t = 1 then ⟨rufIncF, rufRhoF⟩ else ⟨rufCallerF, rhoCallerF⟩

/-- Only thread 1 is dormant. -/
def kwLebt2 : Faden → Bool := fun t => !(decide (t = 1))

def kw2K0 : FadenMaschine rufDF := FadenStart rufPF spF kwInit2 kwLebt2

/-- Right after thread 0 spawns the child on thread 1. -/
def kw2K1 : FadenMaschine rufDF :=
  ⟨kw2K0.m, fun t => if t = 1 then true else kw2K0.lebt t, kw2K0.wartet,
   fun t => if t = 1 then kw2K0.rang 0 + 1 else kw2K0.rang t, kw2K0.uhr + 1⟩

theorem kw2_schritt1 : FadenSchritt rufPF rufOF 0 kw2K0 kw2K1 :=
  FadenSchritt.kind kw2K0 0 1 rfl rfl rfl

/-- **THE CHILD RUN.** Thread 0 spawns the child on thread 1 and does NOT wait; the parent
    calls, the child writes (memory slot 0: 0 -> 2), the parent writes -- interleaved; the
    parent never joins. -/
theorem kw2_lauf : ∃ K2 K3 K4 : FadenMaschine rufDF,
    FadenErreichbar rufPF rufOF 0 kw2K0 K4 ∧
    kw2K0.lebt 1 = false ∧ kw2K1.lebt 1 = true ∧
    -- the parent never waits
    kw2K1.wartet 0 = [] ∧ K2.wartet 0 = [] ∧ K3.wartet 0 = [] ∧ K4.wartet 0 = [] ∧
    -- parent step, child step, parent step
    RufSchrittG rufPF rufOF 0 kw2K1.m 0 K2.m ∧ RufSchrittG rufPF rufOF 0 K2.m 1 K3.m ∧
    RufSchrittG rufPF rufOF 0 K3.m 0 K4.m ∧
    -- the child wrote (its own trace) and finished; the parent is one frame deep and wrote
    (K4.m.faeden 1).spur ≠ [] ∧ FertigG K4.m 1 ∧ (K4.m.faeden 0).stapel.length = 1 ∧
    (K4.m.faeden 0).spur ≠ [] ∧
    kw2K0.m.speicher.slots () 0 () = (⟨0, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
    K3.m.speicher.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) := by
  have hz0 : kw2K1.m.faeden 0 = rufenderFaden [] (spF.welt [])
      [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl
  obtain ⟨M2, s2, ⟨r, h2f⟩, h2s, h2o⟩ := ruf_schritt kw2K1.m 0 _ _ _ hz0
  let K2 : FadenMaschine rufDF := ⟨M2, kw2K1.lebt, kw2K1.wartet, kw2K1.rang, kw2K1.uhr⟩
  have t2 : FadenSchritt rufPF rufOF 0 kw2K1 K2 := FadenSchritt.lauf kw2K1 0 M2 rfl rfl s2
  have hz1 : M2.faeden 1 = schreiberFaden [] (spF.welt [])
      [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := by
    rw [h2o 1 (by decide)]; rfl
  obtain ⟨M3, s3, h3f, h3s, h3o⟩ := schreib_schritt M2 1 _ _ _ hz1
  let K3 : FadenMaschine rufDF := ⟨M3, K2.lebt, K2.wartet, K2.rang, K2.uhr⟩
  have t3 : FadenSchritt rufPF rufOF 0 K2 K3 := FadenSchritt.lauf K2 1 M3 rfl rfl s3
  have hz0' := (h3o 0 (by decide)).trans h2f
  obtain ⟨M4, s4, h4f, h4s, h4o⟩ := schreib_schritt M3 0 _ _ _ hz0'
  let K4 : FadenMaschine rufDF := ⟨M4, K3.lebt, K3.wartet, K3.rang, K3.uhr⟩
  have t4 : FadenSchritt rufPF rufOF 0 K3 K4 := FadenSchritt.lauf K3 0 M4 rfl rfl s4
  have hr : FadenErreichbar rufPF rufOF 0 kw2K0 K4 :=
    .schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ .start kw2_schritt1) t2) t3) t4
  have hf41 := (h4o 1 (by decide)).trans h3f
  refine ⟨K2, K3, K4, hr, rfl, rfl, rfl, rfl, rfl, rfl, s2, s3, s4, ?_,
    geschrieben_fertig hf41, ?_, ?_, rfl, ?_⟩
  · show (M4.faeden 1).spur ≠ []
    rw [hf41]; exact outW_spur_ne _
  · show (M4.faeden 0).stapel.length = 1
    rw [h4f]; rfl
  · show (M4.faeden 0).spur ≠ []
    rw [h4f]; exact outW_spur_ne _
  · show M3.speicher.slots () 0 () = _
    rw [h3s]; exact outW_slot _

#print axioms Gabbro.Grammatik.Zielsatz.schreib_schritt
#print axioms Gabbro.Grammatik.Zielsatz.ruf_schritt
#print axioms Gabbro.Grammatik.Zielsatz.sj_lauf
#print axioms Gabbro.Grammatik.Zielsatz.kw2_lauf

/-! ## 4. The goal on spawn runs of an accepted unit -/

/-- No thread of a start machine holds a lock when no root holds one by signature. -/
theorem start_offen_leer {D : Deklaration} (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (h : ∀ t, D.haelt (init t).1 = [])
    (g : Faden) : offen ((RufStartG P sp init).faeden g).spur = [] := by
  rw [start_faden]
  refine List.eq_nil_iff_forall_not_mem.mpr fun L hL => ?_
  rw [offen_startSpur, h g] at hL
  exact List.not_mem_nil hL

/-- **Probe B's pool routine `haupt` as a RUN-TIME root**: no declared start, `haupt` in
    `gestartet` (a `start { haupt, … }` of the idle root). `ws = [haupt, haupt]`. -/
def zStart : Einheit zD := ⟨zPB, zS, axWahr zD, [], zSp, [⟨zHaupt, .nil⟩]⟩

theorem zStart_ws : zStart.ws = [zHaupt, zHaupt] := rfl

/-- The concrete checker accepts it (the doubled root is pool-safe). -/
theorem zStart_akzeptiert :
    akzeptiert_pruefer.akzeptiert zStart zFs [()] [.inl ()] = true :=
  (by show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true; exact zPool_akzeptiert)

/-- (b): probe B's bodies, and the root's `requires true` at the declared memory. -/
theorem zStart_nutzerPflicht : NutzerPflicht zStart :=
  ⟨⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPB_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [zStart, List.nil_append, List.mem_singleton] at ha
      subst ha; rfl⟩⟩

/-- Threads 1 and 2 are slots at `haupt`, every other thread the idle root. -/
def zsInit : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f) :=
  fun t => if t = 1 ∨ t = 2 then ⟨some zHaupt, envR .nil⟩ else ⟨none, .nil⟩

theorem zsInit_leer (t : Faden) : zD.mitRuhe.haelt (zsInit t).1 = [] := by
  unfold zsInit; split <;> rfl

/-- (d): the runtime places `haupt` (a run-time root, run by any number of threads) on the
    slots and the idle root elsewhere. -/
theorem zStart_laufzeit : Laufzeit zStart (speicherR zSp) zsInit where
  lader := rfl
  start t := by
    unfold zsInit
    split
    · exact Or.inr ⟨⟨zHaupt, .nil⟩, by simp [zStart], rfl⟩
    · exact Or.inl rfl
  einmal t u _ he := by
    revert he
    unfold zsInit
    split
    · intro _; exact Or.inr ⟨zHaupt, rfl, List.Sublist.refl _⟩
    · intro _; exact Or.inl rfl

/-- The slots 1 and 2 are dormant. -/
def zsLebt0 : Faden → Bool := fun t => !(decide (t = 1) || decide (t = 2))

abbrev zsK0 : FadenMaschine zD.mitRuhe := FadenStart zPB.mitRuhe (speicherR zSp) zsInit zsLebt0

/-- Right after the idle root on thread 0 starts `haupt` on 1 and 2 and waits. -/
def zsK1 : FadenMaschine zD.mitRuhe :=
  ⟨zsK0.m, fun t => if t ∈ [1, 2] then true else zsK0.lebt t,
   fun t => if t = 0 then [1, 2] else zsK0.wartet t,
   fun t => if t ∈ [1, 2] then zsK0.rang 0 + 1 else zsK0.rang t, zsK0.uhr + 1⟩

theorem zs_schritt1 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zsK0 zsK1 :=
  FadenSchritt.start zsK0 0 [1, 2] rfl rfl (start_offen_leer _ _ _ zsInit_leer 0) (by decide)

/-- **THE GOAL ON A `start` RUN.** On the accepted unit `zStart`, the idle root starts two
    `haupt` threads (dormant before), both step, thread 1 takes the lock; the starter waits
    for its unfinished roots holding nothing -- and `gabbro_ziel` gives every leg of `ZielF`
    there: `Ziel` over the two spawned threads (race freedom between them included), and the
    join legs. -/
theorem spawn_start_ziel : ∃ K2 K3 K4 : FadenMaschine zD.mitRuhe,
    FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zsK0 K4 ∧
    zsK0.lebt 1 = false ∧ zsK0.lebt 2 = false ∧ K4.lebt 1 = true ∧ K4.lebt 2 = true ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 zsK1.m 1 K2.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K2.m 2 K3.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K3.m 1 K4.m ∧
    (() : zD.mitRuhe.Lock) ∈ offen (K4.m.faeden 1).spur ∧
    K4.wartet 0 = [1, 2] ∧ JoinWartet K4 0 ∧
    ZielF zStart.P.mitRuhe zStart.S.mitRuhe zO.mitRuhe 0
      (RufStartG zStart.P.mitRuhe (speicherR zSp) zsInit) K4 := by
  have hoff : ∀ g, offen (zsK1.m.faeden g).spur = [] :=
    start_offen_leer zPB.mitRuhe (speicherR zSp) zsInit zsInit_leer
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := zsK1.m) (f := 1) rfl zPoolLocks zPoolRet .nil rfl rfl
  let K2 : FadenMaschine zD.mitRuhe := ⟨M2, zsK1.lebt, zsK1.wartet, zsK1.rang, zsK1.uhr⟩
  have t2 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zsK1 K2 := FadenSchritt.lauf zsK1 1 M2 rfl rfl s2
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M2) (f := 2) (rufSchrittG_fremd s2 2 (by decide)) zPoolLocks zPoolRet .nil rfl rfl
  let K3 : FadenMaschine zD.mitRuhe := ⟨M3, K2.lebt, K2.wartet, K2.rang, K2.uhr⟩
  have t3 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K2 K3 := FadenSchritt.lauf K2 2 M3 rfl rfl s3
  have hfrei : RufFreiG M3 1 () := by
    intro g hg
    by_cases h2 : g = 2
    · subst h2
      rw [hZ3.1]
      show () ∉ offen (M2.weltVon 2).spur
      show () ∉ offen (M2.faeden 2).spur
      rw [rufSchrittG_fremd s2 2 (by decide), hoff]
      exact List.not_mem_nil
    · rw [rufSchrittG_fremd s3 g h2, rufSchrittG_fremd s2 g hg, hoff]
      exact List.not_mem_nil
  obtain ⟨M4, s4, hZ4⟩ := w_locks (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M3) (f := 1) ((rufSchrittG_fremd s3 1 (by decide)).trans hZ2.1) ()
    (fun _ h => absurd h List.not_mem_nil) (ruB zLocksBody) .nil (.ende zPoolRet) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res zD.mitRuhe)) ↔ L ∈ offen (zsK1.m.faeden 1).spur
      rw [hoff]
      simp) hfrei
  let K4 : FadenMaschine zD.mitRuhe := ⟨M4, K3.lebt, K3.wartet, K3.rang, K3.uhr⟩
  have t4 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K3 K4 := FadenSchritt.lauf K3 1 M4 rfl rfl s4
  have hr : FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zsK0 K4 :=
    .schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ .start zs_schritt1) t2) t3) t4
  have hL1 : (() : zD.mitRuhe.Lock) ∈ offen (M4.faeden 1).spur := by
    rw [hZ4.1]
    show () ∈ () :: offen (M3.weltVon 1).spur
    exact List.mem_cons_self
  refine ⟨K2, K3, K4, hr, rfl, rfl, rfl, rfl, s2, s3, s4, hL1, rfl, ⟨2, by simp [K4, K3, K2, zsK1],
    fun hF => ?_⟩, ?_⟩
  · -- root 2 stands at its `locks`, not at a return
    have h := hF.2
    rw [rufSchrittG_fremd s4 2 (by decide), hZ3.1] at h
    exact Bool.false_ne_true h
  · exact gabbro_ziel akzeptiert_pruefer zD zStart ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
      ⟨[.inl ()], zCs_voll⟩ zStart_akzeptiert zStart_nutzerPflicht zO
      ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ 0 _ _ zStart_laufzeit zsLebt0 K4 hr

/-- **Probe B with a `child`**: `haupt` is a declared start AND the root of a run-time child
    (`gestartet`). `ws = [haupt, haupt, haupt]`. -/
def zKind : Einheit zD := ⟨zPB, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp, [⟨zHaupt, .nil⟩]⟩

theorem zKind_ws : zKind.ws = [zHaupt, zHaupt, zHaupt] := rfl

theorem zKind_akzeptiert :
    akzeptiert_pruefer.akzeptiert zKind zFs [()] [.inl ()] = true :=
  (by show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt, zHaupt] = true; decide)

theorem zKind_nutzerPflicht : NutzerPflicht zKind :=
  ⟨⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPB_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [zKind, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, or_self] at ha
      subst ha; rfl⟩⟩

/-- Threads 0 (the parent) and 1 (the child slot) at `haupt`, the idle root elsewhere. -/
def zkInit : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f) :=
  fun t => if t = 0 ∨ t = 1 then ⟨some zHaupt, envR .nil⟩ else ⟨none, .nil⟩

theorem zkInit_leer (t : Faden) : zD.mitRuhe.haelt (zkInit t).1 = [] := by
  unfold zkInit; split <;> rfl

theorem zKind_laufzeit : Laufzeit zKind (speicherR zSp) zkInit where
  lader := rfl
  start t := by
    unfold zkInit
    split
    · exact Or.inr ⟨⟨zHaupt, .nil⟩, by simp [zKind], rfl⟩
    · exact Or.inl rfl
  einmal t u _ he := by
    revert he
    unfold zkInit
    split
    · intro _; exact Or.inr ⟨zHaupt, rfl, List.Sublist.cons _ (List.Sublist.refl _)⟩
    · intro _; exact Or.inl rfl

/-- Only the child slot 1 is dormant. -/
def zkLebt0 : Faden → Bool := fun t => !(decide (t = 1))

abbrev zkK0 : FadenMaschine zD.mitRuhe := FadenStart zPB.mitRuhe (speicherR zSp) zkInit zkLebt0

/-- Right after the parent (thread 0) spawns the child on thread 1. -/
def zkK1 : FadenMaschine zD.mitRuhe :=
  ⟨zkK0.m, fun t => if t = 1 then true else zkK0.lebt t, zkK0.wartet,
   fun t => if t = 1 then zkK0.rang 0 + 1 else zkK0.rang t, zkK0.uhr + 1⟩

theorem zk_schritt1 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zkK0 zkK1 :=
  FadenSchritt.kind zkK0 0 1 rfl rfl rfl

/-- **THE GOAL ON A `child` RUN.** On the accepted unit `zKind`, the live `haupt` on thread 0
    spawns a `haupt` child on thread 1 (dormant before) and goes on: parent step, child step,
    parent takes the lock -- and `gabbro_ziel` gives every leg of `ZielF` there; the child
    entered holding nothing (`schlafendFrei` before the spawn, its empty trace after). -/
theorem spawn_kind_ziel : ∃ K2 K3 K4 : FadenMaschine zD.mitRuhe,
    FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zkK0 K4 ∧
    zkK0.lebt 1 = false ∧ K4.lebt 1 = true ∧ K4.wartet 0 = [] ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 zkK1.m 0 K2.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K2.m 1 K3.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K3.m 0 K4.m ∧
    (() : zD.mitRuhe.Lock) ∈ offen (K4.m.faeden 0).spur ∧
    offen (K3.m.faeden 1).spur = [] ∧
    ZielF zKind.P.mitRuhe zKind.S.mitRuhe zO.mitRuhe 0
      (RufStartG zKind.P.mitRuhe (speicherR zSp) zkInit) K4 := by
  have hoff : ∀ g, offen (zkK1.m.faeden g).spur = [] :=
    start_offen_leer zPB.mitRuhe (speicherR zSp) zkInit zkInit_leer
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := zkK1.m) (f := 0) rfl zPoolLocks zPoolRet .nil rfl rfl
  let K2 : FadenMaschine zD.mitRuhe := ⟨M2, zkK1.lebt, zkK1.wartet, zkK1.rang, zkK1.uhr⟩
  have t2 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zkK1 K2 := FadenSchritt.lauf zkK1 0 M2 rfl rfl s2
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M2) (f := 1) (rufSchrittG_fremd s2 1 (by decide)) zPoolLocks zPoolRet .nil rfl rfl
  let K3 : FadenMaschine zD.mitRuhe := ⟨M3, K2.lebt, K2.wartet, K2.rang, K2.uhr⟩
  have t3 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K2 K3 := FadenSchritt.lauf K2 1 M3 rfl rfl s3
  have h3sp : offen (M3.faeden 1).spur = [] := by
    rw [hZ3.1]
    show offen (M2.faeden 1).spur = []
    rw [rufSchrittG_fremd s2 1 (by decide), hoff]
  have hfrei : RufFreiG M3 0 () := by
    intro g hg
    by_cases h1 : g = 1
    · subst h1
      rw [h3sp]
      exact List.not_mem_nil
    · rw [rufSchrittG_fremd s3 g h1, rufSchrittG_fremd s2 g hg, hoff]
      exact List.not_mem_nil
  obtain ⟨M4, s4, hZ4⟩ := w_locks (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M3) (f := 0) ((rufSchrittG_fremd s3 0 (by decide)).trans hZ2.1) ()
    (fun _ h => absurd h List.not_mem_nil) (ruB zLocksBody) .nil (.ende zPoolRet) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res zD.mitRuhe)) ↔ L ∈ offen (zkK1.m.faeden 0).spur
      rw [hoff]
      simp) hfrei
  let K4 : FadenMaschine zD.mitRuhe := ⟨M4, K3.lebt, K3.wartet, K3.rang, K3.uhr⟩
  have t4 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K3 K4 := FadenSchritt.lauf K3 0 M4 rfl rfl s4
  have hr : FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zkK0 K4 :=
    .schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ .start zk_schritt1) t2) t3) t4
  have hL0 : (() : zD.mitRuhe.Lock) ∈ offen (M4.faeden 0).spur := by
    rw [hZ4.1]
    show () ∈ () :: offen (M3.weltVon 0).spur
    exact List.mem_cons_self
  exact ⟨K2, K3, K4, hr, rfl, rfl, rfl, s2, s3, s4, hL0, h3sp,
    gabbro_ziel akzeptiert_pruefer zD zKind ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
      ⟨[.inl ()], zCs_voll⟩ zKind_akzeptiert zKind_nutzerPflicht zO
      ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ 0 _ _ zKind_laufzeit zkLebt0 K4 hr⟩

/-! ## 5. The refusals -/

/-- **`start` of a root that is not pool-safe is refused** (the model side of `N462`). `hauptB`
    of the two-thread fixture writes `privB` unguarded. As a run-time root (`gestartet`) it stands
    twice in `ws`, and the checker Bool refuses -- at the pool component alone. The same routine
    as an ordinary declared start beside `hauptA` is accepted: the refusal is the spawn's. -/
def mStartB : Einheit mD := ⟨mP, mSI, axWahr mD, [⟨mHauptA, .nil⟩], mSp, [⟨mHauptB, .nil⟩]⟩

theorem start_nicht_poolsicher_abgelehnt :
    akzeptiert_pruefer.akzeptiert mStartB mFs [()] mCs = false ∧
    (programmImFragmentG mP mFs && abgAlleB mP mFs &&
      fussWB mP mSI mFs [mHauptA, mHauptB, mHauptB] && stufenB mP mFs && sperrOrteB mSI [()] &&
      wurzelnB [mHauptA, mHauptB, mHauptB] && rennB mP mFs mCs [mHauptA, mHauptB, mHauptB] &&
      antwortenB mP mFs) = true ∧
    einzelnPoolB mP mFs mCs [mHauptA, mHauptB, mHauptB] = false ∧
    Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB] = true := by
  refine ⟨?_, by decide, by decide, mP_akzeptiert⟩
  show Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB, mHauptB] = false
  decide

/-- The same refusal at the specification: no `AkzeptiertSpec` for `mStartB`, because a
    run-time root must be pool-safe (`akzeptiertSpec_gestartet`). -/
theorem start_nicht_poolsicher_spec : ¬ AkzeptiertSpec mP mSI mFs mStartB.ws := fun h =>
  pool_abgelehnt.2.2.2 (akzeptiertSpec_gestartet mStartB mFs h ⟨mHauptB, .nil⟩
    (List.mem_singleton_self _)).2.2

/-- **A `child` inside `locks` is refused** (the model side of `N456`). A region inside
    `locks L` lifts to a root that needs `L` at entry -- `wrap` of probe B, which holds the lock
    by signature (it is called only inside `haupt`'s `locks`). As a run-time root it is refused
    by the checker Bool at the root component (`wurzelnB`: a thread root holds nothing). -/
def zKindUnterSperre : Einheit zD :=
  ⟨zPB, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp, [⟨zWrap, .nil⟩]⟩

theorem kind_unter_sperre_abgelehnt :
    zD.haelt zWrap = [()] ∧
    akzeptiert_pruefer.akzeptiert zKindUnterSperre zFs [()] [.inl ()] = false ∧
    wurzelnB [zHaupt, zWrap, zWrap] = false ∧
    Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt] = true := by
  refine ⟨rfl, ?_, by decide, zPB_akzeptiert⟩
  show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zWrap, zWrap] = false
  decide

theorem kind_unter_sperre_spec : ¬ AkzeptiertSpec zPB zS zFs zKindUnterSperre.ws := fun h => by
  have := (akzeptiertSpec_gestartet zKindUnterSperre zFs h ⟨zWrap, .nil⟩
    (List.mem_singleton_self _)).1
  exact absurd this (by decide)

/-- **No `start` under a held lock** (the model side of `N461`): a step that makes a thread a
    joining starter needs that thread to hold nothing. -/
theorem start_unter_sperre_kein_schritt {D : Deklaration} {P : Programm D} {O : Orakel D}
    {passes : Nat} {K K' : FadenMaschine D} (hs : FadenSchritt P O passes K K') (p : Faden)
    (h0 : K.wartet p = []) (h1 : K'.wartet p ≠ []) : offen (K.m.faeden p).spur = [] := by
  cases hs with
  | lauf => exact absurd h0 h1
  | start q cs _ _ hfrei _ =>
      by_cases hpq : p = q
      · subst hpq; exact hfrei
      · exact absurd (by show (if p = q then cs else K.wartet p) = []; simp [hpq, h0]) h1
  | kind => exact absurd h0 h1
  | join q _ _ _ =>
      exact absurd (by show (if p = q then [] else K.wartet p) = []; split <;> simp_all) h1

/-- Instantiated: on the `child` run of §4, thread 0 holds the lock -- no step makes it a
    starter there. -/
theorem start_unter_sperre_zeuge : ∃ K : FadenMaschine zD.mitRuhe,
    FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zkK0 K ∧
    (() : zD.mitRuhe.Lock) ∈ offen (K.m.faeden 0).spur ∧
    ∀ K', FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K K' → K'.wartet 0 = [] := by
  obtain ⟨_, _, K, hr, _, _, hw, _, _, _, hL, _⟩ := spawn_kind_ziel
  refine ⟨K, hr, hL, fun K' hs => Classical.byContradiction fun hne => ?_⟩
  rw [start_unter_sperre_kein_schritt hs 0 hw hne] at hL
  exact List.not_mem_nil hL

#print axioms Gabbro.Grammatik.Zielsatz.zStart_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.zStart_nutzerPflicht
#print axioms Gabbro.Grammatik.Zielsatz.zStart_laufzeit
#print axioms Gabbro.Grammatik.Zielsatz.spawn_start_ziel
#print axioms Gabbro.Grammatik.Zielsatz.zKind_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.spawn_kind_ziel
#print axioms Gabbro.Grammatik.Zielsatz.start_nicht_poolsicher_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.start_nicht_poolsicher_spec
#print axioms Gabbro.Grammatik.Zielsatz.kind_unter_sperre_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.kind_unter_sperre_spec
#print axioms Gabbro.Grammatik.Zielsatz.start_unter_sperre_kein_schritt
#print axioms Gabbro.Grammatik.Zielsatz.start_unter_sperre_zeuge

/-! ## 6. Fix lane F9's clone machine is a special case -/

/-- **Every run of the standalone clone machine (CloneHandoff.lean) is a thread-machine run**
    with the same G state and the same live set: a clone `spawn` is a `kind` step, a live step
    is a `lauf` step, and nobody ever joins. So `klon_ziel` is now a corollary of `gabbro_ziel`
    as well (`klon_ziel_faden`), with the thread-machine legs on top. -/
theorem klon_als_faden {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)} {lebt0 : Faden → Bool}
    {K : KlonMaschine D} (h : KlonErreichbar P O passes (KlonStart P sp init lebt0) K) :
    ∃ F : FadenMaschine D, FadenErreichbar P O passes (FadenStart P sp init lebt0) F ∧
      F.m = K.m ∧ F.lebt = K.lebt ∧ ∀ t, F.wartet t = [] := by
  induction h with
  | start => exact ⟨_, .start, rfl, rfl, fun _ => rfl⟩
  | schritt K K' _ hs ih =>
      obtain ⟨F, hF, hm, hl, hw⟩ := ih
      cases hs with
      | lauf f M' hf hs' =>
          refine ⟨⟨M', F.lebt, F.wartet, F.rang, F.uhr⟩,
            .schritt _ _ hF (FadenSchritt.lauf F f M' (by rw [hl]; exact hf) (hw f)
              (by rw [hm]; exact hs')), rfl, hl, hw⟩
      | spawn p c hp hc =>
          refine ⟨_, .schritt _ _ hF (FadenSchritt.kind F p c (by rw [hl]; exact hp) (hw p)
              (by rw [hl]; exact hc)), hm, ?_, hw⟩
          show (fun t => if t = c then true else F.lebt t) = _
          rw [hl]

/-- `klon_ziel` through the thread machine: every leg of `ZielF` on every clone run. -/
theorem klon_ziel_faden (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn]
    (E : Einheit D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true)
    (hN : NutzerPflicht E) (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat)
    (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (lebt0 : Faden → Bool) (K : KlonMaschine D.mitRuhe)
    (hK : KlonErreichbar E.P.mitRuhe O.mitRuhe passes (KlonStart E.P.mitRuhe sp init lebt0) K) :
    ∃ F : FadenMaschine D.mitRuhe, F.m = K.m ∧
      ZielF E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) F := by
  obtain ⟨F, hF, hm, -, -⟩ := klon_als_faden hK
  exact ⟨F, hm, gabbro_ziel C D E fs ls cs hC hN O hH passes sp init hL lebt0 F hF⟩

#print axioms Gabbro.Grammatik.Zielsatz.klon_als_faden
#print axioms Gabbro.Grammatik.Zielsatz.klon_ziel_faden

end Gabbro.Grammatik.Zielsatz
