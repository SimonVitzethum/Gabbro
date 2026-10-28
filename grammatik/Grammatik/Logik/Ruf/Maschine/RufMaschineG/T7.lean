/- Part 7 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T6

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Step 6 fires `rueckBind`: the frame pops to the waiting caller and the
    value is bound. Every premise feeds the constructor. -/
theorem schritt6H : RufSchrittG hP rufOF 0 H5H 0 H6H := by
  have hpop : (H5H.faeden 0).stapel = [callerH] := rfl
  have hcaller : callerH.rest =
      ⟨true, rufDF.params rufCallerF,
       nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
       rhoCallerF,
       .wartet restLeaveH
         (.wiederRest 0 bisH bodyH .nil
           (.dann .nil (.ende driverRet)))⟩ := rfl
  have hhead : (H5H.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF),
       rufRhoF, .ende (.ret eF (by decide))⟩ := H5H_kopf
  have hfg : (H5H.faeden 0).kopf.f = rufIncF := rfl
  have hrho : (H5H.faeden 0).kopf.rho = hfg ▸ rufRhoF := rfl
  have hs0 : (H5H.faeden 0).kopf.s0 = H3H.weltVon 0 := rfl
  have hsp : offen (H5H.faeden 0).spur = [] := rfl
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (H5H.faeden 0).spur) := by
    rw [hsp]
    exact (heldLeerF []).heldIn
  have hs1 : s1H =
      (H5H.weltVon 0).lese (Signatur.anfang rufDF (rufDF.signatur rufIncF))
        (ErgExpr.orte eF) := rfl
  have hv : vF = hfg ▸ evalErg s1H eF s1H rufRhoF := rfl
  have hneu : s1H.spur = [] ++ (H5H.faeden 0).spur := rfl
  exact RufSchrittG.rueckBind H5H 0 callerH [] hpop true
    (rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (.int 0 6) restLeaveH
    (.wiederRest 0 bisH bodyH .nil (.dann .nil (.ende driverRet)))
    rhoCallerF (Or.inl hcaller) _ _ _ _ _ H5H_kopf _ hfg rufRhoF hrho _ hs0 hΛ _ hs1 _
    hv (rufDF_erg rufIncF) _ hneu

/-- Step 6 as reachability. -/
theorem reach6H : RufErreichbarG hP rufOF 0 M0H H6H := by
  exact RufErreichbarG.schritt _ _ 0 reach5H schritt6H

/-- The bound head: the exit under the loop shim. -/
theorem H6H_kopf :
    (H6H.faeden 0).kopf.rest =
    ⟨true, .int 0 6 :: rufDF.params rufCallerF,
     nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
     .cons (ergWert (rufDF_erg rufIncF) vF) rhoCallerF,
     .dann restLeaveH
       (.schrumpf (.wiederRest 0 bisH bodyH .nil
         (.dann .nil (.ende driverRet))))⟩ := rfl

/-- The witness log of thread 0: return, writer entry, driver entry. -/
theorem H6H_log : (H6H.faeden 0).log =
    [RufEreignisF.rueck rufIncF rufRhoF vF (H3H.weltVon 0) s1H,
     RufEreignisF.eintritt rufIncF rufRhoF (H3H.weltVon 0),
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl

/-- After the peel: the exit faces the loop shim at driver context. -/
def H7H : RufMaschineG rufDF :=
  ⟨H6H.speicher,
   rufUpdateG H6H.faeden 0
     ⟨(H6H.faeden 0).stapel,
      ⟨(H6H.faeden 0).kopf.f, (H6H.faeden 0).kopf.rho, (H6H.faeden 0).kopf.s0,
       ⟨true, rufDF.params rufCallerF,
        nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
        rhoCallerF,
        .dann (.cons leaveHd .nil)
          (.wiederRest 0 bisH bodyH .nil
            (.dann .nil (.ende driverRet)))⟩⟩,
      (H6H.faeden 0).spur, (H6H.faeden 0).log⟩,
   H6H.lauf, H6H.start⟩

/-- Step 7 fires `peelSchrumpfLeave`: the bound value is dropped. -/
theorem schritt7H : RufSchrittG hP rufOF 0 H6H 0 H7H :=
  RufSchrittG.peelSchrumpfLeave H6H 0 true (rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (.int 0 6) .nil
    (.wiederRest 0 bisH bodyH .nil (.dann .nil (.ende driverRet)))
    (.cons (ergWert (rufDF_erg rufIncF) vF) rhoCallerF) rfl H6H_kopf

/-- Step 7 as reachability. -/
theorem reach7H : RufErreichbarG hP rufOF 0 M0H H7H := by
  exact RufErreichbarG.schritt _ _ 0 reach6H schritt7H

/-- The exit under the shim, peeled. -/
theorem H7H_kopf :
    (H7H.faeden 0).kopf.rest =
    ⟨true, rufDF.params rufCallerF,
     nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
     rhoCallerF,
     .dann (.cons leaveHd .nil)
       (.wiederRest 0 bisH bodyH .nil
         (.dann .nil (.ende driverRet)))⟩ := rfl

/-- After the loop exit: the overflow arm is skipped, driver continues. -/
def H8H : RufMaschineG rufDF :=
  ⟨H7H.speicher,
   rufUpdateG H7H.faeden 0
     ⟨(H7H.faeden 0).stapel,
      ⟨(H7H.faeden 0).kopf.f, (H7H.faeden 0).kopf.rho, (H7H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufCallerF,
        nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
        rhoCallerF,
        .dann .nil (.ende driverRet)⟩⟩,
      (H7H.weltVon 0).spur, (H7H.faeden 0).log⟩,
   H7H.lauf ++ rufEigenG 0 [],
   H7H.start⟩

/-- Step 8 fires `dannLeaveWieder`: the loop is exited. -/
theorem schritt8H : RufSchrittG hP rufOF 0 H7H 0 H8H := by
  have hhead : (H7H.faeden 0).kopf.rest =
      ⟨true, rufDF.params rufCallerF,
       nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
       rhoCallerF,
       .dann (.cons leaveHd .nil)
         (.wiederRest 0 bisH bodyH .nil
           (.dann .nil (.ende driverRet)))⟩ := H7H_kopf
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (H7H.faeden 0).kopf.f)
      leaveHd
      (H7H.weltVon 0) rhoCallerF) =
      Ausgang.leave (D := rufDF) (V := vertragVon rufDF (H7H.faeden 0).kopf.f)
        rfl (H7H.weltVon 0) rhoCallerF := rfl
  have hneu : (H7H.weltVon 0).spur = [] ++ (H7H.faeden 0).spur := rfl
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ ([] : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittG.dannLeaveWieder H7H 0 false (rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    0 bisH bodyH .nil (.dann .nil (.ende driverRet)) .nil rhoCallerF rfl
    hhead _ _ [] hstep hneu hkein (heldGenau_rufDF _ _)

/-- Step 8 as reachability. -/
theorem reach8H : RufErreichbarG hP rufOF 0 M0H H8H := by
  exact RufErreichbarG.schritt _ _ 0 reach7H schritt8H

/-- The driver continuation after the loop. -/
theorem H8H_kopf :
    (H8H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
     rhoCallerF,
     .dann .nil (.ende driverRet)⟩ := rfl

/-- After the drain: the driver return. -/
def H9H : RufMaschineG rufDF :=
  ⟨H8H.speicher,
   rufUpdateG H8H.faeden 0
     ⟨(H8H.faeden 0).stapel,
      ⟨(H8H.faeden 0).kopf.f, (H8H.faeden 0).kopf.rho, (H8H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufCallerF,
        nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
        rhoCallerF, .ende driverRet⟩⟩,
      (H8H.faeden 0).spur, (H8H.faeden 0).log⟩,
   H8H.lauf, H8H.start⟩

/-- Step 9 fires `dannLeer`: the loop scaffolding is gone. -/
theorem schritt9H : RufSchrittG hP rufOF 0 H8H 0 H9H :=
  RufSchrittG.dannLeer H8H 0 false (rufDF.params rufCallerF)
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (.ende driverRet) rhoCallerF H8H_kopf

/-- Step 9 as reachability: nine steps FROM THE START STATE. -/
theorem reach9H : RufErreichbarG hP rufOF 0 M0H H9H := by
  exact RufErreichbarG.schritt _ _ 0 reach8H schritt9H

/-- The witness run reaches `H9H` from the start state. -/
theorem reach9H_start :
    RufErreichbarG hP rufOF 0 (RufStartG hP spF initF) H9H := by
  rw [← M0H_start]
  exact reach9H

/-- The final log: return, writer entry, driver entry (later steps keep it). -/
theorem H9H_log : (H9H.faeden 0).log =
    [RufEreignisF.rueck rufIncF rufRhoF vF (H3H.weltVon 0) s1H,
     RufEreignisF.eintritt rufIncF rufRhoF (H3H.weltVon 0),
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl

/-- The final memory carries the written value at slot 0 (via `outWF`). -/
theorem H9H_slot : H9H.speicher.slots () 0 () =
    (⟨2, by decide, by decide⟩ : Wert rufDF (rufDF.typ () ())) := by
  have hhit := outWF_moves.1
  have hmem : H9H.speicher.slots () 0 () = outWF.slots () 0 () := rfl
  rw [hmem]
  exact hhit

/-- Memory really moved: slot 0 reads `2`, the start reads `0`. -/
theorem H9H_moves : H9H.speicher.slots () 0 () ≠
    spF.slots () 0 () := by
  have h2 := H9H_slot
  have h0 : spF.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert rufDF (rufDF.typ () ())) := rfl
  rw [h2, h0]
  intro hcon
  have hn : ((⟨2, by decide, by decide⟩ :
      Wert rufDF (rufDF.typ () ())).n) = ((⟨0, by decide, by decide⟩ :
      Wert rufDF (rufDF.typ () ())).n) := congrArg Zahl.n hcon
  simp only [Int.reduceEq] at hn

/-- **Witness for `rufG_treu` over a loop with `leave` and a bind-call.**
    The premises of `rufG_treu` are instantiated JOINTLY: the program `hP`
    (driver with a `retry` loop whose body binds a call to the writer and
    then leaves), the oracle `rufOF`, zero passes, start memory `spF`,
    every thread at the driver entry with `initF`, the reached machine
    `H9H` (reached FROM THE START STATE by `reach9H_start`: `endeEntf`
    unfolds the loop, `dannRetry` installs one try, `wiederSchritt` runs
    the body on the false condition, `dannBindCall` pushes the writer,
    `blatt` runs the writing leaf -- slot 0 moves 0 -> 2 by `H9H_moves`,
    a step that changes memory -- `rueckBind` binds the value and logs
    the return, `peelSchrumpfLeave` drops the bound value,
    `dannLeaveWieder` exits the loop, `dannLeer` drains the scaffolding),
    and thread `0`. The log contains the `rueck` event, and the matching
    `eintritt` sits below it in the same log. The fourth conjunct is the
    non-degeneracy: the run moves memory. -/
theorem rufG_treu_zeuge_bind_leave :
    ∃ (M : RufMaschineG rufDF) (f : Faden)
      (g : rufDF.Fn) (rho : Env rufDF (rufDF.params g))
      (v : ErgVal rufDF (rufDF.erg g)) (s0 s1 : World rufDF),
      RufErreichbarG hP rufOF 0 (RufStartG hP spF initF) M ∧
        RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log ∧
        RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log ∧
        M.speicher.slots () 0 () ≠ spF.slots () 0 () := by
  exact ⟨H9H, 0, rufIncF, rufRhoF, vF, H3H.weltVon 0, s1H,
    reach9H_start, by rw [H9H_log]; exact List.mem_cons_self,
    by rw [H9H_log]; exact List.mem_cons_of_mem _ (List.mem_cons_self),
    H9H_moves⟩

/-- **Witness for `rufG_nie_wartend`.** Its premises instantiated on the
    bind/leave program `hP` from the start state: after `dannBindCall`
    (`H4H`) the caller frame WAITS on the stack (`wartet`) below the
    writer, and the head does not wait; after the writer's leaf moved
    memory, the binding pop, the peel and the loop exit (`H9H`) the head
    does not wait either -- the theorem at two reachable machines, one with
    a waiting frame on the stack. -/
theorem rufG_nie_wartend_zeuge :
    RufErreichbarG hP rufOF 0 (RufStartG hP spF initF) H4H ∧
    (∃ (c : RufRahmenG rufDF) (rst : List (RufRahmenG rufDF)),
      (H4H.faeden 0).stapel = c :: rst ∧ c.wartend = true) ∧
    (H4H.faeden 0).kopf.wartend = false ∧
    RufErreichbarG hP rufOF 0 (RufStartG hP spF initF) H9H ∧
    (H9H.faeden 0).kopf.wartend = false ∧
    H9H.speicher.slots () 0 () ≠ spF.slots () 0 () := by
  have h4 : RufErreichbarG hP rufOF 0 (RufStartG hP spF initF) H4H := by
    rw [← M0H_start]
    exact reach4H
  exact ⟨h4, ⟨callerH, [], rfl, rfl⟩, rufG_nie_wartend hP rufOF 0 spF initF H4H h4 0,
    reach9H_start, rufG_nie_wartend hP rufOF 0 spF initF H9H reach9H_start 0, H9H_moves⟩

/-! ## CUTS:
  - Stepwise coverage. Every `Stmt`/`Block`/`Endblock` constructor either
    has a step rule or is listed below with its reason.
    - Leaves run atomically through `execStmt` (`blatt`/`dannBlatt`, `.ok`
      outcome): `assignSlot`, `assignDurch`, `assignGlob`, `schreibBytes`,
      `assignVar`, `uebergang`, `axiomCall`, `regSchreib`, `transition`,
      `publish`, `advances`, `retires`.
    - `ite` (both directions), `onOption` (some/none), `onTag`
      (payload/payload-free via `armWahlG`), `onGrund` (via `grundWahlG`),
      `locks` (take into `dann`, release at `frei`), `breaking`,
      `traverse`/`retry`/`forever` (one iteration at a time via
      `trav`/`travRest`, `wieder`/`wiederRest`, `ewig`/`ewigRest` with the
      `passes` budget), `let` (`endeBind`/`dannBind` with `schrumpf`),
      `narrow` and `pruefung` (both outcomes, else-arms jump to `ende`).
    - `traverse` reads its invariant exactly where `traverseLauf` does
      (repaired 2026-09-13): `dannTrav` unfolds WITHOUT a read, `travNext`
      reads before every iteration, `travDone` after the last one,
      `dannLeaveTrav` after a `leave`; each fires only on `true`. On a
      false read no rule for the frame fires -- it is stuck where
      `traverseLauf` ends in `logik .schleife` (`trav_falsch_steht`,
      `RufAdaequatG.lean`). Before the repair a false START invariant made
      `dannTravFertig` skip the loop and continue, `travNext` re-read the
      invariant before the first iteration, and `travDone` never read it.
    - Direct calls: `ruf` (ende position) and `rufDann` (block position)
      push the caller frame ADVANCED past the call (`.ende rest` resp.
      `.dann rest k`, holdings `nach D g Λ`), so `rueck` resumes the caller
      after the call. (Repaired 2026-09-13: `ruf` pushed the caller
      unchanged, so the caller repeated the call after every `rueck` and
      never reached `rest`.)
    - Indirect calls: `rufCallInd` (ende position) and `dannCallInd`
      (block position) resolve the pointer value and push the callee frame
      like `ruf`/`rufDann`, logging `eintritt` (`rufCallInd` repaired like
      `ruf`).
    - Bind-calls push the callee with a waiting caller residue: `wartet`
      (`dannBindCall`, `dannBindCallInd`) or `wartetSonst`, which keeps the
      else block (`dannBindCallElse`); a return binds the value in the
      caller environment -- from `ende ret` (`rueckBind`), from an early
      `ret` at an `ende` cons head (`rueckConsBind`) or in a block
      (`dannRetBind`), each logging `rueck`, into either waiting form. The
      verbatim pops (`rueck`, `rueckCons`, `dannRet`) demand a caller that
      does NOT wait (`hnw`, repaired 2026-09-13: before, they could restore
      a waiting caller, whose head `wartet …` has no rule -- the thread
      deadlocked); no reachable head waits (`rufG_nie_wartend`).
    - The error channel (added 2026-09-13): a callee's `retGrund r` (from
      `ende`, an `ende` cons head, or a block) pops into a caller waiting
      in `wartetSonst` (`rueckGrund`, `rueckConsGrund`, `dannRetGrund`),
      which runs its else block with `r` bound, logging the new event
      `RufEreignisF.why` (`RufLogPasstG.why` keeps `rufG_treu`). A
      `retGrund` into any other caller (only an entry frame could have one:
      `call`/`bindCall` demand `gruende = 0`) or with an empty stack has no
      step.
    - Register/atomic/float binders run one layer deep, mirroring their
      `execBlock` equation (value pushed, body stepwise under `schrumpf`):
      `dannRegLies`, `dannRegLiesElseWahr`/`Falsch`, `dannAwaits`,
      `dannExchange` (total), `dannGleit`, `dannGleitLit`, `dannGleitVon`,
      `dannGleitNarrowOk`/`Else`, `dannBindAxiom`. Each fires only on its
      success outcome; the hardware outcomes (unfittable register,
      broken `zusage`, invisible global, out-of-range float, failing
      axiom) have no step -- the machine stalls where `execBlock`
      reports `hardware`.
    - Abrupt exits: `dannLeaveTrav`/`dannNextTrav`, `dannLeaveWieder`/
      `dannNextWieder`, `dannLeaveEwig`/`dannNextEwig` consume a head
      `leave`/`next` at a loop shim (`trav` leave checks the invariant
      like `traverseLauf`; `retry`/`forever` exits are direct like
      `retryLauf`/`foreverLauf`); `peelDann`/`peelSchrumpf`/`peelFrei` (x
      `leave`/`next`) abandon the scaffolding the loop body built (`frei`
      emits `gibt`, like `locks`) -- at ANY static holdings (generalised
      2026-09-13: the peels and shims demanded the exit's holdings to equal
      the scaffolding's, so an exit behind a holdings-changing statement,
      e.g. a call that consumes or produces marks, had no step, while
      `execBlock` propagates the exit; the holdings index is static
      bookkeeping the step never reads); early `ret` pops with a `rueck` event
      (`dannRet` in blocks, `rueckCons` at `ende` cons heads). `rueck`,
      `rueckCons`, `rueckBind` accept a returning residue at ANY loop level,
      so a `ret` that ends an else branch (`sonst`) inside a loop body pops
      (it stalled before: the rules demanded level `false`).
    - NOT covered: `retGrund` outside the error channel (see above);
      `leave`/`next` at `ende`
      position (else-branch exits via `dannNarrowElse`/`dannPruefFalsch`/
      `dannRegLiesElseFalsch`/`dannGleitNarrowElse` discard the loop shim
      with the continuation -- recovering it needs the shim threaded
      through else-branches, a redesign); peels through
      `wartet`/`wartetSonst` (unreachable: a waiting residue never stands as
      a live continuation, `GRest.sauber`); `forever` with exhausted budget
      and false
      invariants (the reference machine reports `hardware .fortschritt`
      / `logik .schleife` there).
    - Top-level `ret` with an empty call stack has no step (as in F): both
      witnesses return through a call, like every `rueck`.
  - No contract discharge: the machine never gates on contracts, and no
    theorem connects `rueck` events to `ReqAmEintritt`/`EnsAmRueck`. The
    events carry the actual values such a theorem would need. So the
    machine realises calls through the bare body run (`rufRumpf`), not
    through `rufAt`, which checks and reads the contracts (`befund_vertrag`,
    `RufAdaequatRufG.lean`).
-/

#print axioms Gabbro.Grammatik.rufG_treu
#print axioms Gabbro.Grammatik.rufG_treu_zeuge
#print axioms Gabbro.Grammatik.rufG_treu_zeuge_bind_leave
#print axioms Gabbro.Grammatik.rufSchrittG_passt
#print axioms Gabbro.Grammatik.rufErreichbarG_passt
#print axioms Gabbro.Grammatik.schritt4G
#print axioms Gabbro.Grammatik.reach7G_start
#print axioms Gabbro.Grammatik.M7G_moves
#print axioms Gabbro.Grammatik.schritt5H
#print axioms Gabbro.Grammatik.schritt6H
#print axioms Gabbro.Grammatik.schritt8H
#print axioms Gabbro.Grammatik.reach9H_start
#print axioms Gabbro.Grammatik.H9H_moves
#print axioms Gabbro.Grammatik.rufG_nie_wartend
#print axioms Gabbro.Grammatik.rufG_nie_wartend_zeuge
#print axioms Gabbro.Grammatik.rufSchrittG_sauber


end Gabbro.Grammatik
