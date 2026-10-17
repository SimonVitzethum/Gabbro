/- Part 3 of 3 of `RufMaschineF` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineF.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The outcome world of the `blatt` step: read (nothing to read) then write
    slot 0 := 2. NOTE: this is the CALLEE leaf outcome at the callee thread
    world, restated below as `leafSF_ok_at` for the actual machine. -/
def outWF : World rufDF :=
  (((spF.welt []).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) []).schreibSlot ()
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) 0 ()
    ⟨2, by decide, by decide⟩)

theorem leafSF_ok : (execStmt rufOF 0 (R := keinRuf)
    (V := vertragVon rufDF rufIncF)
    (Λ := Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Λ' := Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF (spF.welt []) rufRhoF) =
    Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) outWF rufRhoF := by
  unfold leafSF outWF
  rfl

/-- The outcome world differs from the entry world in memory: slot 0 moves
    from 0 to 2. This is the non-degeneracy the witness needs -- a step that
    changes memory. -/
theorem outWF_moves : outWF.slots () 0 () =
    (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
    (spF.welt []).slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert rufDF (.int 0 5)) := by
  refine ⟨rfl, rfl⟩

/-- `Anfang` of the witness signature is empty: no locks, no marks. -/
theorem anfangF_leer :
    Signatur.anfang rufDF (rufDF.signatur rufIncF) = [] := rfl

/-- Held-exactly at the empty trace: no locks exist. -/
theorem heldLeerF (spur : List (Ereignis rufDF)) :
    HeldGenau ([] : List (Res rufDF)) (offen spur) := by
  intro L
  exact nomatch L

/-- The start head is the writing body with the entry environment.
    STALE shape from before the caller/callee split; kept as documentation
    of the one-function attempt. States the callee residue, which the start
    machine no longer holds (it holds the caller). -/
theorem M0F_kopf_alt :
    rufRumpfF = Endblock.cons leafSF restF :=
  rufRumpfF_eq

/-- The machine after the `ruf` step: the caller frame suspended, the
    callee frame installed with evaluated arguments (`rufRhoF`: the caller
    rho holds 2, so the callee gets 2), entry world the caller thread world
    (no arg reads), log extended with the entry event. -/
def M1F : RufMaschineF rufDF :=
  ⟨M0F.speicher,
   rufUpdateF M0F.faeden 0
     ⟨(M0F.faeden 0).kopf :: (M0F.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, M0F.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, rufPF.rumpf rufIncF⟩⟩,
      (M0F.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (M0F.weltVon 0)) ::
        (M0F.faeden 0).log⟩,
   M0F.lauf ++ rufEigenF 0 [],
   M0F.start⟩

/-- The callee entry world is the caller thread world: the arguments read
    nothing (`var.hier` has no Orte). -/
theorem argsOrteF : rufArgsF.orte = [] := rfl

/-- Step 1 fires the `ruf` rule: head matches (caller body is the call),
    locks vacuous, entry world is the thread world (no arg reads),
    evaluated args are `rufRhoF`, no new trace events. Every premise is
    used: `hhead`/`hΛ`/`hs0`/`hrho`/`hneu` feed the constructor. -/
theorem schritt1F : RufSchrittF rufPF rufOF 0 M0F 0 M1F := by
  have hhead : (M0F.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .cons (.call rufIncF rufArgsF rufHpF rfl)
        ((rufDF_params rufCallerF).symm ▸
          (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
            Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
          Endblock rufDF (vertragVon rufDF rufCallerF) false
            (rufDF.params rufIncF) (nach rufDF rufIncF []))⟩ := by
    rw [M0F_kopf]
    rfl
  have hΛ : HeldGenau ([] : List (Res rufDF)) (offen (M0F.faeden 0).spur) :=
    heldLeerF _
  have hs0 : M0F.weltVon 0 =
      (M0F.weltVon 0).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (M0F.weltVon 0) rufArgsF
      (M0F.weltVon 0) rhoCallerF := by
    have hw : M0F.weltVon 0 = spF.welt [] := rfl
    rw [hw]
    rfl
  have hneu : (M0F.weltVon 0).spur = [] ++ (M0F.faeden 0).spur := rfl
  exact RufSchrittF.ruf M0F 0 false (rufDF.params rufCallerF) [] rufIncF
    rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 1 as reachability: start, then one step. -/
theorem reach1F : RufErreichbarF rufPF rufOF 0 M0F M1F := by
  exact RufErreichbarF.schritt _ _ 0 RufErreichbarF.start schritt1F

/-- The return expression of the witness body: the parameter widened to
    `.int 0 6`. -/
def eF : ErgExpr rufDF (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (vertragVon rufDF rufIncF).erg :=
  (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6))))

theorem restF_eq : restF = Endblock.ret eF (by decide) := rfl

theorem eF_orte : ErgExpr.orte eF = [] := rfl

/-- The return value: the parameter 2 widened to `.int 0 6`. -/
def vF : ErgVal rufDF (rufDF.erg rufIncF) :=
  (rufDF_erg rufIncF).symm ▸ (⟨2, by decide, by decide⟩ : ErgVal rufDF (some (.int 0 6)))

theorem vF_wert : vF = evalErg (M1F.weltVon 0) eF (M1F.weltVon 0) rufRhoF := rfl

/-- The machine after the `blatt` step: the callee residue advanced to
    `restF`, the stored callee environment unchanged (the leaf does not
    bind), memory moved to `outWF`. The new events are the whole outcome
    trace, since the entry trace was empty. -/
def M2F : RufMaschineF rufDF :=
  ⟨outWF.speicher,
   rufUpdateF M1F.faeden 0
     ⟨(M1F.faeden 0).stapel,
      ⟨(M1F.faeden 0).kopf.f, (M1F.faeden 0).kopf.rho, (M1F.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF, restF⟩⟩,
      outWF.spur, (M1F.faeden 0).log⟩,
   M1F.lauf ++ rufEigenF 0 outWF.spur,
   M1F.start⟩

/-- The callee head after the call is the writing body with `rufRhoF`. -/
theorem M1F_kopf :
    (M1F.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .cons leafSF restF⟩ := rfl

/-- The thread world is unchanged by the call (no new events). -/
theorem M1F_welt : M1F.weltVon 0 = spF.welt [] := rfl

/-- Step 2 fires the `blatt` rule on the callee frame: the leaf runs under
    the STORED `rufRhoF` (no free binder) and stores the resulting `rufRhoF`
    (the leaf does not bind). Memory moves to `outWF` -- the write. Every
    premise is used: `hhead`/`hΛ`/`hstep`/`hneu` feed the constructor. -/
theorem schritt2F : RufSchrittF rufPF rufOF 0 M1F 0 M2F := by
  have hhead : (M1F.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .cons leafSF restF⟩ := M1F_kopf
  have hΛ : HeldGenau (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M1F.faeden 0).spur) := by
    rw [anfangF_leer]
    exact heldLeerF _
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (M1F.faeden 0).kopf.f)
      leafSF (M1F.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (M1F.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [M1F_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (M1F.faeden 0).spur := by
    have hspur : (M1F.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittF.blatt M1F 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF restF rufRhoF leafSF_blatt hhead hΛ outWF rufRhoF
    outWF.spur hstep hneu hkein

/-- Step 2 as reachability. -/
theorem reach2F : RufErreichbarF rufPF rufOF 0 M0F M2F := by
  exact RufErreichbarF.schritt _ _ 0 reach1F schritt2F

/-- The machine after the `rueck` step: the caller restored, the return
    logged after the entry. The return world is the callee thread world
    (no reads), the value is the widened parameter 2. Every premise is
    used: `hpop`/`hfg`/`hrho`/`hs0` select the head frame, `hΛ` the lock
    state, `hs1`/`hv`/`hneu` feed the constructor. -/
def M3F : RufMaschineF rufDF :=
  ⟨(M2F.weltVon 0).speicher,
   rufUpdateF M2F.faeden 0
     ⟨[], (M0F.faeden 0).kopf, (M2F.weltVon 0).spur,
      [RufEreignisF.rueck rufIncF rufRhoF vF (M0F.weltVon 0) (M2F.weltVon 0)] ++
        (M2F.faeden 0).log⟩,
   M2F.lauf ++ rufEigenF 0 [],
   M2F.start⟩

theorem schritt3F : RufSchrittF rufPF rufOF 0 M2F 0 M3F := by
  have hpop : (M2F.faeden 0).stapel = [(M0F.faeden 0).kopf] := rfl
  have hhead : (M2F.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF),
       rufRhoF, .ret eF (by decide)⟩ := rfl
  have hfg : (M2F.faeden 0).kopf.f = rufIncF := rfl
  have hrho : (M2F.faeden 0).kopf.rho = hfg ▸ rufRhoF := rfl
  have hs0 : (M2F.faeden 0).kopf.s0 = M0F.weltVon 0 := rfl
  have hΛ : HeldGenau (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M2F.faeden 0).spur) := by
    rw [anfangF_leer]
    exact heldLeerF _
  have hs1 : M2F.weltVon 0 =
      (M2F.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF) := by
    rw [eF_orte]
    rfl
  have hv : vF = hfg ▸ evalErg (M2F.weltVon 0) eF (M2F.weltVon 0) rufRhoF := rfl
  have hneu : (M2F.weltVon 0).spur = [] ++ (M2F.faeden 0).spur := rfl
  exact RufSchrittF.rueck M2F 0 (M0F.faeden 0).kopf [] hpop _ _ _ _ _
    hhead _ hfg rufRhoF hrho _ hs0 hΛ _ hs1 _ hv _ hneu

/-- Step 3 as reachability: three steps FROM THE START STATE. -/
theorem reach3F : RufErreichbarF rufPF rufOF 0 M0F M3F := by
  exact RufErreichbarF.schritt _ _ 0 reach2F schritt3F

/-- Reachability from `RufStartF`: `M0F` IS the start machine. -/
theorem M0F_start : M0F = RufStartF rufPF spF initF := rfl

/-- The witness run reaches `M3F` from the start state. -/
theorem reach3F_start :
    RufErreichbarF rufPF rufOF 0 (RufStartF rufPF spF initF) M3F := by
  rw [← M0F_start]
  exact reach3F

/-- The witness log of thread 0 after all three steps: return, callee
    entry, caller entry. -/
theorem M3F_log : (M3F.faeden 0).log =
    [RufEreignisF.rueck rufIncF rufRhoF vF (M0F.weltVon 0) (M2F.weltVon 0),
     RufEreignisF.eintritt rufIncF rufRhoF (M0F.weltVon 0),
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl

/-- **Witness for `rufF_treu`.** The premises of `rufF_treu` are instantiated
    JOINTLY with concrete values: the program `rufPF`, the oracle `rufOF`,
    one pass, start memory `spF`, every thread at the caller entry with
    `rhoCallerF`, the reached machine `M3F` (reached FROM THE START STATE by
    `reach3F_start`: `ruf` pushes the callee, `blatt` runs the writing leaf
    -- slot 0 moves 0 -> 2 by `outWF_moves`, a step that changes memory --
    `rueck` pops it), and thread `0`. The log contains the `rueck` event,
    and the matching `eintritt` sits below it in the same log. The program
    is NON-DEGENERATE: one table that the callee writes (`leafSF` via
    `execStmt`), and a three-step run with a memory-changing step. Every
    premise is used: `h` is the reachability, `hmem` the log membership. -/
theorem rufF_treu_zeuge :
    ∃ (M : RufMaschineF rufDF) (f : Faden)
      (g : rufDF.Fn) (rho : Env rufDF (rufDF.params g))
      (v : ErgVal rufDF (rufDF.erg g)) (s0 s1 : World rufDF),
      RufErreichbarF rufPF rufOF 0 (RufStartF rufPF spF initF) M ∧
        RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log ∧
        RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  exact ⟨M3F, 0, rufIncF, rufRhoF, vF, M0F.weltVon 0, M2F.weltVon 0,
    reach3F_start, by rw [M3F_log]; exact List.mem_cons_self,
    by rw [M3F_log]; exact List.mem_cons_of_mem _ (List.mem_cons_self)⟩

-- APPEND-POINT

/-! ## CUTS:
  - Compound statements (`ite`, `locks` bodies, `bind`, loops, indirect and
    reason-channel calls) have no unfold step: the machine is partial there,
    and only straight-line `ret` bodies plus one writing leaf reduce. Full
    continuation threading stays open, as in the D attempt.
  - No contract discharge: the machine never gates on contracts, and no
    theorem connects `rueck` events to `ReqAmEintritt`/`EnsAmRueck`. The
    events carry the actual values such a theorem would need.
  - `rufVF` (result 3) and `rufWeltF`/`rufStartF_passt`-era one-function
    leftovers: `rufVF` is unused (the witness returns the parameter 2 as
    `vF`); `rufWeltF` only serves `leafSF_mem`; `M0F_kopf_alt` restates
    `rufRumpfF_eq`.
-/

#print axioms Gabbro.Grammatik.RufEreignisF.eintritt
#print axioms Gabbro.Grammatik.rufF_treu
#print axioms Gabbro.Grammatik.rufF_treu_zeuge
#print axioms Gabbro.Grammatik.rufSchrittF_passt
#print axioms Gabbro.Grammatik.rufErreichbarF_passt
#print axioms Gabbro.Grammatik.rufLogPasstF_gedeckt
#print axioms Gabbro.Grammatik.schritt1F
#print axioms Gabbro.Grammatik.schritt2F
#print axioms Gabbro.Grammatik.schritt3F
#print axioms Gabbro.Grammatik.reach3F_start
#print axioms Gabbro.Grammatik.outWF_moves


end Gabbro.Grammatik
