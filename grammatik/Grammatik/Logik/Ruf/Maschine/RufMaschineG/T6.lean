/- Part 6 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5

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
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl

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
  simp at hn

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

theorem bisH_orte : bisH.orte = [] := rfl

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
theorem retryH_entf : GEntfaltbar retryStmtH = true := rfl

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
theorem hP_rumpf_false : hP.rumpf rufCallerF = driverBodyH := rfl

/-- The writer body is what `hP` runs at `true`. -/
theorem hP_rumpf_true : hP.rumpf rufIncF = rufRumpfF := rfl

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
theorem M0H_start : M0H = RufStartG hP spF initF := rfl

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
     .dann (.cons retryStmtH .nil) (.ende driverRet)⟩ := rfl

/-- The thread world is unchanged by the unfold. -/
theorem H1H_welt : H1H.weltVon 0 = spF.welt [] := rfl

/-- After `dannRetry`: one try with the overflow arm behind. -/
def H2H : RufMaschineG rufDF :=
  ⟨H1H.speicher,
   rufUpdateG H1H.faeden 0
     ⟨(H1H.faeden 0).stapel,
      ⟨(H1H.faeden 0).kopf.f, (H1H.faeden 0).kopf.rho, (H1H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufCallerF,
        Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
        .wieder 1 bisH bodyH .nil (.dann .nil (.ende driverRet))⟩⟩,
      (H1H.faeden 0).spur, (H1H.faeden 0).log⟩,
   H1H.lauf, H1H.start⟩

/-- Step 2 fires `dannRetry`. -/
theorem schritt2H : RufSchrittG hP rufOF 0 H1H 0 H2H :=
  RufSchrittG.dannRetry H1H 0 false (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    1 bisH bodyH .nil .nil (.ende driverRet) rhoCallerF H1H_kopf

/-- Step 2 as reachability. -/
theorem reach2H : RufErreichbarG hP rufOF 0 M0H H2H := by
  exact RufErreichbarG.schritt _ _ 0 reach1H schritt2H

/-- The loop node, installed. -/
theorem H2H_kopf :
    (H2H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
     .wieder 1 bisH bodyH .nil (.dann .nil (.ende driverRet))⟩ := rfl

/-- The thread world is unchanged by installing the loop. -/
theorem H2H_welt : H2H.weltVon 0 = spF.welt [] := rfl

/-- After the condition check: the body runs under the loop shim. -/
def H3H : RufMaschineG rufDF :=
  ⟨H2H.speicher,
   rufUpdateG H2H.faeden 0
     ⟨(H2H.faeden 0).stapel,
      ⟨(H2H.faeden 0).kopf.f, (H2H.faeden 0).kopf.rho, (H2H.faeden 0).kopf.s0,
       ⟨true, rufDF.params rufCallerF,
        Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
        .dann bodyH
          (.wiederRest 0 bisH bodyH .nil
            (.dann .nil (.ende driverRet)))⟩⟩,
      (H2H.weltVon 0).spur, (H2H.faeden 0).log⟩,
   H2H.lauf ++ rufEigenG 0 [],
   H2H.start⟩

/-- Step 3 fires `wiederSchritt`: the condition is literal `false`. -/
theorem schritt3H : RufSchrittG hP rufOF 0 H2H 0 H3H := by
  have hs₁ : H2H.weltVon 0 =
      (H2H.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) bisH.orte := by
    rw [bisH_orte]
    rfl
  have hw : wahr? (eval (H2H.weltVon 0) bisH (H2H.weltVon 0) rhoCallerF) =
      false :=
    rfl
  have hneu : (H2H.weltVon 0).spur = [] ++ (H2H.faeden 0).spur := rfl
  exact RufSchrittG.wiederSchritt H2H 0 false (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    0 bisH bodyH .nil (.dann .nil (.ende driverRet)) rhoCallerF H2H_kopf _
    hs₁ hw _ hneu (heldGenau_rufDF _ _)

/-- Step 3 as reachability. -/
theorem reach3H : RufErreichbarG hP rufOF 0 M0H H3H := by
  exact RufErreichbarG.schritt _ _ 0 reach2H schritt3H

/-- The body under the shim. -/
theorem H3H_kopf :
    (H3H.faeden 0).kopf.rest =
    ⟨true, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
     .dann bodyH
       (.wiederRest 0 bisH bodyH .nil
         (.dann .nil (.ende driverRet)))⟩ := rfl

/-- The thread world is unchanged by the check (nothing read). -/
theorem H3H_welt : H3H.weltVon 0 = spF.welt [] := rfl

/-- After the bind-call: caller suspended with `wartet`, writer installed. -/
def H4H : RufMaschineG rufDF :=
  ⟨H3H.speicher,
   rufUpdateG H3H.faeden 0
     ⟨⟨(H3H.faeden 0).kopf.f, (H3H.faeden 0).kopf.rho, (H3H.faeden 0).kopf.s0,
        ⟨true, rufDF.params rufCallerF,
         nach rufDF rufIncF
           (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
         rhoCallerF,
         .wartet restLeaveH
           (.wiederRest 0 bisH bodyH .nil
             (.dann .nil (.ende driverRet)))⟩⟩ ::
       (H3H.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, H3H.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, .ende (hP.rumpf rufIncF)⟩⟩,
      (H3H.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (H3H.weltVon 0)) ::
        (H3H.faeden 0).log⟩,
   H3H.lauf ++ rufEigenG 0 [],
   H3H.start⟩

/-- Step 4 fires `dannBindCall`: the writer frame is pushed, the caller
    waits with `wartet`. Every premise feeds the constructor. -/
theorem schritt4H : RufSchrittG hP rufOF 0 H3H 0 H4H := by
  have hhead : (H3H.faeden 0).kopf.rest =
      ⟨true, rufDF.params rufCallerF,
       Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
       .dann (.bindCall rufIncF rufArgsF (rufDF_erg rufIncF) rufHpF rfl
         restLeaveH)
         (.wiederRest 0 bisH bodyH .nil
           (.dann .nil (.ende driverRet)))⟩ := H3H_kopf
  have hΛ : HeldIn ([] : List (Res rufDF)) (offen (H3H.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hs0 : H3H.weltVon 0 =
      (H3H.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
        (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (H3H.weltVon 0) rufArgsF
      (H3H.weltVon 0) rhoCallerF := by
    rw [H3H_welt]
    rfl
  have hneu : (H3H.weltVon 0).spur = [] ++ (H3H.faeden 0).spur := rfl
  exact RufSchrittG.dannBindCall H3H 0 true (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (.int 0 6) rufIncF rufArgsF (rufDF_erg rufIncF) rufHpF rfl restLeaveH
    (.wiederRest 0 bisH bodyH .nil (.dann .nil (.ende driverRet)))
    rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 4 as reachability. -/
theorem reach4H : RufErreichbarG hP rufOF 0 M0H H4H := by
  exact RufErreichbarG.schritt _ _ 0 reach3H schritt4H

/-- The writer head after the push: leaf plus return. -/
theorem H4H_kopf :
    (H4H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.cons leafSF restF)⟩ := rfl

/-- The writer runs in the entry world (arguments read nothing). -/
theorem H4H_welt : H4H.weltVon 0 = spF.welt [] := rfl

/-- After the writing leaf: memory moved to `outWF`. -/
def H5H : RufMaschineG rufDF :=
  ⟨outWF.speicher,
   rufUpdateG H4H.faeden 0
     ⟨(H4H.faeden 0).stapel,
      ⟨(H4H.faeden 0).kopf.f, (H4H.faeden 0).kopf.rho, (H4H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .ende restF⟩⟩,
      outWF.spur, (H4H.faeden 0).log⟩,
   H4H.lauf ++ rufEigenG 0 outWF.spur,
   H4H.start⟩

/-- Step 5 fires `blatt` on the writing leaf -- the memory move. -/
theorem schritt5H : RufSchrittG hP rufOF 0 H4H 0 H5H := by
  have hhead : (H4H.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .ende (.cons leafSF restF)⟩ := H4H_kopf
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (H4H.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (H4H.faeden 0).kopf.f)
      leafSF (H4H.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (H4H.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [H4H_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (H4H.faeden 0).spur := by
    have hspur : (H4H.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittG.blatt H4H 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF restF rufRhoF leafSF_blatt hhead hΛ
    outWF rufRhoF outWF.spur hstep hneu hkein

/-- Step 5 as reachability. -/
theorem reach5H : RufErreichbarG hP rufOF 0 M0H H5H := by
  exact RufErreichbarG.schritt _ _ 0 reach4H schritt5H

/-- The writer residue after the leaf: the parameter return. -/
theorem H5H_kopf :
    (H5H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.ret eF (by decide))⟩ := rfl

/-- The suspended caller frame, named for the pop. -/
def callerH : RufRahmenG rufDF :=
  ⟨rufCallerF, rhoCallerF, H3H.weltVon 0,
   ⟨true, rufDF.params rufCallerF,
    nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
    rhoCallerF,
    .wartet restLeaveH
      (.wiederRest 0 bisH bodyH .nil
        (.dann .nil (.ende driverRet)))⟩⟩

/-- The return world: the writer thread world read at the result places. -/
def s1H : World rufDF :=
  (H5H.weltVon 0).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF)

/-- After `rueckBind`: caller restored, value bound, return logged. The
    head frame is written with projections, exactly as the rule builds it. -/
def H6H : RufMaschineG rufDF :=
  ⟨s1H.speicher,
   rufUpdateG H5H.faeden 0
     ⟨[], ⟨callerH.f, callerH.rho, callerH.s0,
        ⟨true, .int 0 6 :: rufDF.params rufCallerF,
         nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
         .cons (ergWert (rufDF_erg rufIncF) vF) rhoCallerF,
         .dann restLeaveH
           (.schrumpf (.wiederRest 0 bisH bodyH .nil
             (.dann .nil (.ende driverRet))))⟩⟩,
      s1H.spur,
      (RufEreignisF.rueck rufIncF rufRhoF vF (H3H.weltVon 0) s1H) ::
        (H5H.faeden 0).log⟩,
   H5H.lauf ++ rufEigenG 0 [],
   H5H.start⟩


end Gabbro.Grammatik
