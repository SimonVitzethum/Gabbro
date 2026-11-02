/- Part 6 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Step 7 fires `rueck`: the callee frame pops to the waiting caller.
    Every premise feeds the constructor: `hpop`/`hfg`/`hrho`/`hs0`
    select the head frame, `hΛ` the lock state, `hs1`/`hv`/`hneu` the
    return data. -/
theorem schritt7G : RufSchrittG gP rufOF 0 M6G 0 M7G := by
  have hpop : (M6G.faeden 0).stapel = [callerFrameG] := rfl
  have hhead : (M6G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF),
       rufRhoF, .ende (.ret eF (by decide))⟩ := M6G_kopf
  have hfg : (M6G.faeden 0).kopf.f = rufIncF := rfl
  have hrho : (M6G.faeden 0).kopf.rho = hfg ▸ rufRhoF := rfl
  have hs0 : (M6G.faeden 0).kopf.s0 = M0G.weltVon 0 := rfl
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M6G.faeden 0).spur) := by
    have e : offen (M6G.faeden 0).spur = [] := rfl
    rw [e]
    exact (heldLeerF []).heldIn
  have hs1 : s1G =
      (M6G.weltVon 0).lese (Signatur.anfang rufDF (rufDF.signatur rufIncF))
        (ErgExpr.orte eF) := rfl
  have hv : vF = hfg ▸ evalErg s1G eF s1G rufRhoF := rfl
  have hneu : s1G.spur = [] ++ (M6G.faeden 0).spur := rfl
  exact RufSchrittG.rueck M6G 0 callerFrameG [] hpop _ _ _ _ _
    hhead _ hfg rufRhoF hrho _ hs0 hΛ _ hs1 _ hv _ hneu rfl

/-- Step 7 as reachability: seven steps FROM THE START STATE. -/
theorem reach7G : RufErreichbarG gP rufOF 0 M0G M7G := by
  exact RufErreichbarG.schritt _ _ 0 reach6G schritt7G

/-- The witness run reaches `M7G` from the start state. -/
theorem reach7G_start :
    RufErreichbarG gP rufOF 0 (RufStartG gP spF initF) M7G := by
  rw [← M0G_start]
  exact reach7G

/-- The witness log of thread 0: return, callee entry, caller entry. -/
theorem M7G_log : (M7G.faeden 0).log =
    [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G,
     RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0),
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := by rfl

/-- The final memory carries the written value at slot 0 (via `outWF`). -/
theorem M7G_slot : M7G.speicher.slots () 0 () =
    (⟨2, by decide, by decide⟩ : Wert rufDF (rufDF.typ () ())) := by
  have hhit := outWF_moves.1
  have hmem : M7G.speicher.slots () 0 () = outWF.slots () 0 () := rfl
  rw [hmem]
  exact hhit

/-- Memory really moved: slot 0 reads `2`, the start reads `0`. Both
    conjuncts feed the inequality below. -/
theorem M7G_moves : M7G.speicher.slots () 0 () ≠
    spF.slots () 0 () := by
  have h2 := M7G_slot
  have h0 : spF.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert rufDF (rufDF.typ () ())) := rfl
  rw [h2, h0]
  intro hcon
  have hn : ((⟨2, by decide, by decide⟩ :
      Wert rufDF (rufDF.typ () ())).n) = ((⟨0, by decide, by decide⟩ :
      Wert rufDF (rufDF.typ () ())).n) := congrArg Zahl.n hcon
  simp only [Int.reduceEq] at hn

/-- **Witness for `rufG_treu`.** The premises of `rufG_treu` are
    instantiated JOINTLY with concrete values: the program `gP` (callee
    with an `if` whose taken branch writes), the oracle `rufOF`, zero
    passes, start memory `spF`, every thread at the caller entry with
    `initF`, the reached machine `M7G` (reached FROM THE START STATE by
    `reach7G_start`: `ruf` pushes the callee, `endeEntf` unfolds the
    `if`, `dannIteWahr` takes the writing branch, `dannBlatt` runs the
    writing leaf -- slot 0 moves 0 -> 2 by `M7G_moves`, a step that
    changes memory -- two `dannLeer` steps drain the scaffolding,
    `rueck` pops it), and thread `0`. The log contains the `rueck`
    event, and the matching `eintritt` sits below it in the same log.
    The fourth conjunct is the non-degeneracy: the run moves memory.
    Every premise is used: `h` is the reachability, `hmem` the log
    membership, the move the memory change. -/
theorem rufG_treu_zeuge :
    ∃ (M : RufMaschineG rufDF) (f : Faden)
      (g : rufDF.Fn) (rho : Env rufDF (rufDF.params g))
      (v : ErgVal rufDF (rufDF.erg g)) (s0 s1 : World rufDF),
      RufErreichbarG gP rufOF 0 (RufStartG gP spF initF) M ∧
        RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log ∧
        RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log ∧
        M.speicher.slots () 0 () ≠ spF.slots () 0 () := by
  exact ⟨M7G, 0, rufIncF, rufRhoF, vF, M0G.weltVon 0, s1G,
    reach7G_start, by rw [M7G_log]; exact List.mem_cons_self,
    by rw [M7G_log]; exact List.mem_cons_of_mem _ (List.mem_cons_self),
    M7G_moves⟩

/-! ## 9. Second witness: a loop that exits with `leave`, plus a bind-call

    Roles reuse the F declaration `rufDF`: `true` is the writer (its body
    `rufRumpfF` is the writing leaf plus `ret`, so `eF`/`vF`/`leafSF_ok`
    transfer unchanged); `false` drives a `retry` loop whose body binds a
    call to `true` and then leaves. The `rueckBind` step logs the return
    (the joint `rueck` event) and the leaf moves memory. -/

/-- The loop condition: literal `false`, so the body runs once. -/
def bisH : Expr rufDF (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) .bool :=
  .fls

theorem bisH_orte : bisH.orte = [] := by rfl

/-- The abrupt exit at the end of the bound body. -/
def leaveH : Stmt rufDF (vertragVon rufDF rufCallerF) true
    (.int 0 6 :: rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF))) :=
  .leave rfl

/-- The bound continuation: exit, then nothing. -/
def restLeaveH : Block rufDF (vertragVon rufDF rufCallerF) true
    (.int 0 6 :: rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF))) :=
  .cons leaveH .nil

/-- The same exit after the bound value is dropped (driver context). -/
def leaveHd : Stmt rufDF (vertragVon rufDF rufCallerF) true
    (rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF))) :=
  .leave rfl

/-- The loop body: bind a call to the writer, then leave. -/
def bodyH : Block rufDF (vertragVon rufDF rufCallerF) true
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF))) :=
  .bindCall rufIncF rufArgsF (rufDF_erg rufIncF) rufHpF rfl restLeaveH

/-- The loop: one try, body runs (condition false), overflow never fires. -/
def retryStmtH : Stmt rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) :=
  .retry 1 bisH bodyH .nil

/-- The loop unfolds. -/
theorem retryH_entf : GEntfaltbar retryStmtH = true := by rfl

/-- The driver return: the parameter, like `restF` (contracts coincide by
    computation, so the F term is reused directly). -/
def driverRet : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) :=
  restF

/-- The driver body: the loop, then return. -/
def driverBodyH : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) :=
  .cons retryStmtH driverRet

/-- The program: the writer writes, the driver loops. -/
def hP : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => rufRumpfF
    | false => driverBodyH

/-- The driver body is what `hP` runs at `false`. -/
theorem hP_rumpf_false : hP.rumpf rufCallerF = driverBodyH := by rfl

/-- The writer body is what `hP` runs at `true`. -/
theorem hP_rumpf_true : hP.rumpf rufIncF = rufRumpfF := by rfl

def M0H : RufMaschineG rufDF := RufStartG hP spF initF

/-- The start head is the driver body with the entry environment. -/
theorem M0H_kopf :
    (M0H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, .ende driverBodyH⟩ := by
  have hstart : (RufStartG (D := rufDF) hP spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', .ende (hP.rumpf g')⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenG rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0H.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, .ende (hP.rumpf rufCallerF)⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenG rufDF) := by
    simp only [M0H]
    rw [hstart, hif]
  have hrumpf : hP.rumpf rufCallerF = driverBodyH := rfl
  rw [hM, hrumpf]

/-- Reachability from `RufStartG`: `M0H` IS the start machine. -/
theorem M0H_start : M0H = RufStartG hP spF initF := by rfl

/-! ## 10. The witness run: unfold, loop, bind-call, leave -/

/-- After the unfold: the loop moved into `dann` position. -/
def H1H : RufMaschineG rufDF :=
  ⟨M0H.speicher,
   rufUpdateG M0H.faeden 0
     ⟨(M0H.faeden 0).stapel,
      ⟨(M0H.faeden 0).kopf.f, (M0H.faeden 0).kopf.rho, (M0H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufCallerF,
        Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
        .dann (.cons retryStmtH .nil) (.ende driverRet)⟩⟩,
      (M0H.faeden 0).spur, (M0H.faeden 0).log⟩,
   M0H.lauf, M0H.start⟩

/-- Step 1 fires `endeEntf`: the loop head moves into `dann`. -/
theorem schritt1H : RufSchrittG hP rufOF 0 M0H 0 H1H :=
  RufSchrittG.endeEntf M0H 0 false (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    retryStmtH driverRet rhoCallerF retryH_entf M0H_kopf

/-- Step 1 as reachability. -/
theorem reach1H : RufErreichbarG hP rufOF 0 M0H H1H := by
  exact RufErreichbarG.schritt _ _ 0 RufErreichbarG.start schritt1H

/-- The unfolded head. -/
theorem H1H_kopf :
    (H1H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
     .dann (.cons retryStmtH .nil) (.ende driverRet)⟩ := by rfl

/-- The thread world is unchanged by the unfold. -/
theorem H1H_welt : H1H.weltVon 0 = spF.welt [] := by rfl

end Gabbro.Grammatik
