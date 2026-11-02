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


end Gabbro.Grammatik.Zielsatz
