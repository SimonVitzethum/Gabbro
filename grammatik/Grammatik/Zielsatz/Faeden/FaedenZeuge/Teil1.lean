module

public import Grammatik.Zielsatz.Faeden.FaedenVor
public import Grammatik.Zielsatz.Faeden.PoolZeuge
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



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
      simp only [outW, World.schreibSlot, World.merke, World.lese, List.map_nil, List.nil_append, List.cons_append,
  List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · simp only [World.storeSlot, Speicher.welt, dite_eq_ite, List.not_mem_nil] at he
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
           (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
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
  simp only [outW, World.schreibSlot, World.merke, World.lese, List.map_nil, List.nil_append, List.cons_append,
  ne_eq, reduceCtorEq, not_false_eq_true]

/-- Slot 0 holds 2 after the write, from any memory. -/
theorem outW_slot (sp : Speicher rufDF) :
    (outW sp).speicher.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) :=
  by rfl

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
  by rfl

theorem sj_f1 : sjK0.m.faeden 1 =
    schreiberFaden [] (spF.welt []) [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := by rfl

theorem sj_f2 : sjK0.m.faeden 2 =
    schreiberFaden [] (spF.welt []) [RufEreignisF.eintritt rufIncF rufRhoF (spF.welt [])] := by rfl

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
    FadenSchritt.join K3 0 rfl (by simp only [sjK1, List.mem_cons, List.not_mem_nil, or_false, Bool.ite_true_left, Bool.decide_or, ↓reduceIte,
  ne_eq, reduceCtorEq, not_false_eq_true, K3, K2]) hF
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
    geschrieben_fertig h2f, schreiber_nicht_fertig hz2, ⟨2, by simp only [sjK1, List.mem_cons, List.not_mem_nil, or_false, Bool.ite_true_left, Bool.decide_or, ↓reduceIte,
  Nat.succ_ne_self, or_true, K2],
      schreiber_nicht_fertig hz2⟩, rfl,
    geschrieben_fertig hf31, geschrieben_fertig h3f, ?_, ?_, t4, by simp only [↓reduceIte, K4], rfl, ?_, ?_, ?_,
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
def zStart : Einheit zD := ⟨zPB, zS, axWahr zD, [], zSp, [⟨zHaupt, .nil⟩], []⟩

theorem zStart_ws : zStart.ws = [zHaupt, zHaupt] := by rfl

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
  lader := by rfl
  start t := by
    unfold zsInit
    split
    · exact Or.inr ⟨⟨zHaupt, .nil⟩, by simp only [zStart, List.nil_append, List.mem_cons, List.not_mem_nil, or_false], rfl⟩
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

end Gabbro.Grammatik.Zielsatz
