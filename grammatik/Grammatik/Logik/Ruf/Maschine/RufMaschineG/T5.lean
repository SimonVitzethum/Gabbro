/- Part 5 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Every rule keeps the invariant of the acting thread. The pops are the
    point: a verbatim pop resumes a caller that does not wait (`hnw`), so
    the resumed head is clean; a binding pop resumes the waiting caller's
    continuation as a clean `dann` residue. -/
theorem rufSchrittG_sauber_acting {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : RufFadenSauberG (M.faeden f)) : RufFadenSauberG (M'.faeden f) := by
  obtain ⟨hk, hst⟩ := h
  have hpopS : ∀ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst →
      caller.rest.2.2.2.2.stapelSauber = true ∧
        ∀ r ∈ rst, r.rest.2.2.2.2.stapelSauber = true := by
    intro caller rst hpop
    rw [hpop] at hst
    exact ⟨hst caller List.mem_cons_self, fun r hr => hst r (List.mem_cons_of_mem _ hr)⟩
  cases hs with
  | rueck caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    exact ⟨GRest.stapelSauber_sauber hnw hc, hr⟩
  | rueckCons caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    exact ⟨GRest.stapelSauber_sauber hnw hc, hr⟩
  | dannRet _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    exact ⟨GRest.stapelSauber_sauber hnw hc, hr⟩
  | rueckBind caller rst hpop _ _ _ _ _ restb k _ hcaller =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, hr⟩
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc <;>
      simpa [GRest.sauber, GRest.stapelSauber] using hc
  | dannRetBind _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ restb k _ hcaller =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, hr⟩
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc <;>
      simpa [GRest.sauber, GRest.stapelSauber] using hc
  | rueckConsBind _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ restb k _ hcaller =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, hr⟩
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc <;>
      simpa [GRest.sauber, GRest.stapelSauber] using hc
  | rueckGrund _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ hcaller =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    rw [hcaller] at hc
    exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
  | rueckConsGrund _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ hcaller =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    rw [hcaller] at hc
    exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
  | dannRetGrund _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ hcaller =>
    obtain ⟨hc, hr⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    rw [hcaller] at hc
    exact ⟨by simpa [GRest.sauber, GRest.stapelSauber] using hc, hr⟩
  | _ =>
    simp only [rufUpdateG_self]
    rw [‹(M.faeden f).kopf.rest = _›] at hk
    simp only [GRest.sauber] at hk
    refine ⟨?_, ?_⟩
    · simp only [GRest.sauber]
      try exact hk
    · first
      | exact hst
      | (intro r hr
         rcases List.mem_cons.1 hr with hr | hr
         · subst hr
           simp only [GRest.sauber, GRest.stapelSauber]
           try exact hk
         · exact hst r hr)

/-- Every step keeps the invariant at every thread. -/
theorem rufSchrittG_sauber {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : ∀ g, RufFadenSauberG (M.faeden g)) : ∀ g, RufFadenSauberG (M'.faeden g) := by
  intro g
  by_cases hg : g = f
  · subst hg
    exact rufSchrittG_sauber_acting hs (h g)
  · rw [rufSchrittG_passt_anders P O passes M M' f g hg hs]
    exact h g

/-- The start machine satisfies the invariant: empty stacks, `ende` heads. -/
theorem rufStartG_sauber (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    ∀ g, RufFadenSauberG ((RufStartG P sp init).faeden g) := by
  intro g
  refine ⟨rfl, ?_⟩
  intro r hr
  exact absurd hr List.not_mem_nil

/-- **No reachable head waits.** In every machine reachable from the start,
    no thread's head residue is a waiting node -- the deadlock the verbatim
    pops caused (a caller restored at `wartet …`, where no rule fires) can
    no longer arise. -/
theorem rufG_nie_wartend (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (f : Faden) :
    (M.faeden f).kopf.wartend = false := by
  have hinv : ∀ g, RufFadenSauberG (M.faeden g) := by
    induction h with
    | start => exact rufStartG_sauber P sp init
    | schritt M M' g _ hs ih => exact rufSchrittG_sauber hs ih
  exact (hinv f).kopf_wartend

/-! ## 7. Witness: an `if` whose taken branch writes a table

    The witness reuses the F declaration `rufDF` (one table, `Bool`
    functions, no locks): the callee `true` runs an `if` whose taken
    branch is the writing leaf, the caller `false` reuses the F caller
    body (a call to `true`). -/

/-- The condition: the literal `true`, so the taken branch fires. -/
def cG : Expr rufDF (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) .bool :=
  .tru

/-- The taken branch: the writing leaf, then nothing. -/
def thenG : Block rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons leafSF .nil

/-- The else branch: nothing. -/
def elseG : Block rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .nil

/-- The `if` statement. -/
def iteG : Stmt rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .ite cG thenG elseG

/-- The `if` unfolds. -/
theorem iteG_entf : GEntfaltbar iteG = true := rfl

/-- The callee body: the `if`, then the parameter return `restF`. -/
def calleeG : Endblock rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons iteG restF

/-- The program: trivial contracts, callee with the `if`, caller reused. -/
def gP : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => calleeG
    | false => rufCallerRumpfF

/-- The callee body is what `gP` runs at `true`. -/
theorem gP_rumpf_true : gP.rumpf rufIncF = calleeG := rfl

def M0G : RufMaschineG rufDF := RufStartG gP spF initF

/-- The start head is the caller body with the entry environment. -/
theorem M0G_kopf :
    (M0G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, .ende rufCallerRumpfF⟩ := by
  have hstart : (RufStartG (D := rufDF) gP spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', .ende (gP.rumpf g')⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenG rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0G.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, .ende (gP.rumpf rufCallerF)⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenG rufDF) := by
    simp only [M0G]
    rw [hstart, hif]
  have hrumpf : gP.rumpf rufCallerF = rufCallerRumpfF := rfl
  rw [hM, hrumpf]

/-- Reachability from `RufStartG`: `M0G` IS the start machine. -/
theorem M0G_start : M0G = RufStartG gP spF initF := rfl

/-! ## 8. The witness run: call, unfold, branch, write, return -/

/-- The caller's residue AFTER the call: the parameter return. -/
def callerRestG : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF) (nach rufDF rufIncF []) :=
  (rufDF_params rufCallerF).symm ▸
    ((.ret (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
      Endblock rufDF (vertragVon rufDF rufCallerF) false
        (rufDF.params rufIncF) (nach rufDF rufIncF []))

/-- The suspended caller frame: residue ADVANCED past the call. -/
def callerFrameG : RufRahmenG rufDF :=
  ⟨rufCallerF, rhoCallerF, spF.welt [],
   ⟨false, rufDF.params rufCallerF, nach rufDF rufIncF [], rhoCallerF,
    .ende callerRestG⟩⟩

/-- The machine after the `ruf` step: caller suspended past the call,
    callee installed with the `if` body. -/
def M1G : RufMaschineG rufDF :=
  ⟨M0G.speicher,
   rufUpdateG M0G.faeden 0
     ⟨callerFrameG :: (M0G.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, M0G.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, .ende (gP.rumpf rufIncF)⟩⟩,
      (M0G.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0)) ::
        (M0G.faeden 0).log⟩,
   M0G.lauf ++ rufEigenG 0 [],
   M0G.start⟩

/-- Step 1 fires the `ruf` rule on the caller frame. Every premise feeds
    the constructor: `hhead`/`hΛ` fix the frame, `hs0`/`hrho`/`hneu` the
    entry data. -/
theorem schritt1G : RufSchrittG gP rufOF 0 M0G 0 M1G := by
  have hhead : (M0G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .ende (.cons (.call rufIncF rufArgsF rufHpF rfl)
         ((rufDF_params rufCallerF).symm ▸
           (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
             Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
           Endblock rufDF (vertragVon rufDF rufCallerF) false
             (rufDF.params rufIncF) (nach rufDF rufIncF [])))⟩ := by
    rw [M0G_kopf]
    rfl
  have hΛ : HeldIn ([] : List (Res rufDF)) (offen (M0G.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hs0 : M0G.weltVon 0 =
      (M0G.weltVon 0).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (M0G.weltVon 0) rufArgsF
      (M0G.weltVon 0) rhoCallerF := by
    have hw : M0G.weltVon 0 = spF.welt [] := rfl
    rw [hw]
    rfl
  have hneu : (M0G.weltVon 0).spur = [] ++ (M0G.faeden 0).spur := rfl
  exact RufSchrittG.ruf M0G 0 false (rufDF.params rufCallerF) [] rufIncF
    rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 1 as reachability. -/
theorem reach1G : RufErreichbarG gP rufOF 0 M0G M1G := by
  exact RufErreichbarG.schritt _ _ 0 RufErreichbarG.start schritt1G

/-- The callee head after the call is the `if` body with `rufRhoF`. -/
theorem M1G_kopf :
    (M1G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.cons iteG restF)⟩ := rfl

/-- The thread world is unchanged by the call (no new events). -/
theorem M1G_welt : M1G.weltVon 0 = spF.welt [] := rfl

/-- The machine after the unfold: the `if` moved into `dann` position. -/
def M2G : RufMaschineG rufDF :=
  ⟨M1G.speicher,
   rufUpdateG M1G.faeden 0
     ⟨(M1G.faeden 0).stapel,
      ⟨(M1G.faeden 0).kopf.f, (M1G.faeden 0).kopf.rho, (M1G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons iteG .nil) (.ende restF)⟩⟩,
      (M1G.faeden 0).spur, (M1G.faeden 0).log⟩,
   M1G.lauf, M1G.start⟩

/-- Step 2 fires `endeEntf`: the compound head moves into `dann`. -/
theorem schritt2G : RufSchrittG gP rufOF 0 M1G 0 M2G :=
  RufSchrittG.endeEntf M1G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    iteG restF rufRhoF iteG_entf M1G_kopf

/-- Step 2 as reachability. -/
theorem reach2G : RufErreichbarG gP rufOF 0 M0G M2G := by
  exact RufErreichbarG.schritt _ _ 0 reach1G schritt2G

/-- The unfolded head. -/
theorem M2G_kopf :
    (M2G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann (.cons iteG .nil) (.ende restF)⟩ := rfl

/-- The thread world is unchanged by the unfold. -/
theorem M2G_welt : M2G.weltVon 0 = spF.welt [] := rfl

theorem cG_orte : cG.orte = [] := rfl

/-- The machine after the branch: the taken writing branch runs first,
    then the empty rest, then the return. The condition reads nothing,
    so the world is unchanged. -/
def M3G : RufMaschineG rufDF :=
  ⟨M2G.speicher,
   rufUpdateG M2G.faeden 0
     ⟨(M2G.faeden 0).stapel,
      ⟨(M2G.faeden 0).kopf.f, (M2G.faeden 0).kopf.rho, (M2G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩⟩,
      (M2G.weltVon 0).spur, (M2G.faeden 0).log⟩,
   M2G.lauf ++ rufEigenG 0 [],
   M2G.start⟩

/-- Held-exactly for `rufDF`: the declaration has no lock. -/
theorem heldGenau_rufDF (Λ : List (Res rufDF)) (spur : List (Ereignis rufDF)) :
    HeldIn Λ (offen spur) := fun L => nomatch L

/-- Step 3 fires `dannIteWahr`: the condition is the literal `true`. -/
theorem schritt3G : RufSchrittG gP rufOF 0 M2G 0 M3G := by
  have hhead : (M2G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons (.ite cG thenG elseG) .nil) (.ende restF)⟩ := M2G_kopf
  have hs₁ : M2G.weltVon 0 =
      (M2G.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) cG.orte := by
    rw [cG_orte]
    rfl
  have hw : wahr? (eval (M2G.weltVon 0) cG (M2G.weltVon 0) rufRhoF) = true :=
    rfl
  have hneu : (M2G.weltVon 0).spur = [] ++ (M2G.faeden 0).spur := rfl
  exact RufSchrittG.dannIteWahr M2G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    cG thenG elseG .nil (.ende restF) rufRhoF hhead _ hs₁ hw _ hneu (heldGenau_rufDF _ _)

/-- Step 3 as reachability. -/
theorem reach3G : RufErreichbarG gP rufOF 0 M0G M3G := by
  exact RufErreichbarG.schritt _ _ 0 reach2G schritt3G

/-- The taken branch, unfolded. -/
theorem M3G_kopf :
    (M3G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := rfl

/-- The thread world is unchanged by the branch choice. -/
theorem M3G_welt : M3G.weltVon 0 = spF.welt [] := rfl

/-- The machine after the writing leaf: memory moved to `outWF`, the
    branch block is done. -/
def M4G : RufMaschineG rufDF :=
  ⟨outWF.speicher,
   rufUpdateG M3G.faeden 0
     ⟨(M3G.faeden 0).stapel,
      ⟨(M3G.faeden 0).kopf.f, (M3G.faeden 0).kopf.rho, (M3G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.dann .nil (.ende restF))⟩⟩,
      outWF.spur, (M3G.faeden 0).log⟩,
   M3G.lauf ++ rufEigenG 0 outWF.spur,
   M3G.start⟩

/-- Step 4 fires `dannBlatt` on the writing leaf -- the memory move. -/
theorem schritt4G : RufSchrittG gP rufOF 0 M3G 0 M4G := by
  have hhead : (M3G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := M3G_kopf
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M3G.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (M3G.faeden 0).kopf.f)
      leafSF (M3G.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (M3G.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [M3G_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (M3G.faeden 0).spur := by
    have hspur : (M3G.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittG.dannBlatt M3G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF .nil (.dann .nil (.ende restF)) rufRhoF leafSF_blatt hhead hΛ
    outWF rufRhoF outWF.spur hstep hneu hkein

/-- Step 4 as reachability. -/
theorem reach4G : RufErreichbarG gP rufOF 0 M0G M4G := by
  exact RufErreichbarG.schritt _ _ 0 reach3G schritt4G

/-- The finished branch, behind two empty blocks. -/
theorem M4G_kopf :
    (M4G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann .nil (.dann .nil (.ende restF))⟩ := rfl

/-- The machine after the first empty block completes. -/
def M5G : RufMaschineG rufDF :=
  ⟨M4G.speicher,
   rufUpdateG M4G.faeden 0
     ⟨(M4G.faeden 0).stapel,
      ⟨(M4G.faeden 0).kopf.f, (M4G.faeden 0).kopf.rho, (M4G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.ende restF)⟩⟩,
      (M4G.faeden 0).spur, (M4G.faeden 0).log⟩,
   M4G.lauf, M4G.start⟩

/-- Step 5 fires `dannLeer`: the branch block is done. -/
theorem schritt5G : RufSchrittG gP rufOF 0 M4G 0 M5G :=
  RufSchrittG.dannLeer M4G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (.dann .nil (.ende restF)) rufRhoF M4G_kopf

/-- Step 5 as reachability. -/
theorem reach5G : RufErreichbarG gP rufOF 0 M0G M5G := by
  exact RufErreichbarG.schritt _ _ 0 reach4G schritt5G

/-- The second empty block, done. -/
theorem M5G_kopf :
    (M5G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann .nil (.ende restF)⟩ := rfl

/-- The machine after the second empty block completes: the return. -/
def M6G : RufMaschineG rufDF :=
  ⟨M5G.speicher,
   rufUpdateG M5G.faeden 0
     ⟨(M5G.faeden 0).stapel,
      ⟨(M5G.faeden 0).kopf.f, (M5G.faeden 0).kopf.rho, (M5G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .ende restF⟩⟩,
      (M5G.faeden 0).spur, (M5G.faeden 0).log⟩,
   M5G.lauf, M5G.start⟩

/-- Step 6 fires `dannLeer` again: the `if` scaffolding is gone. -/
theorem schritt6G : RufSchrittG gP rufOF 0 M5G 0 M6G :=
  RufSchrittG.dannLeer M5G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (.ende restF) rufRhoF M5G_kopf

/-- Step 6 as reachability. -/
theorem reach6G : RufErreichbarG gP rufOF 0 M0G M6G := by
  exact RufErreichbarG.schritt _ _ 0 reach5G schritt6G

/-- The return residue: the parameter return. -/
theorem M6G_kopf :
    (M6G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.ret eF (by decide))⟩ := rfl

/-- The return world: the callee thread world read at the (empty) result
    places. -/
def s1G : World rufDF :=
  (M6G.weltVon 0).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF)

/-- The machine after the `rueck` step: caller restored, return logged. -/
def M7G : RufMaschineG rufDF :=
  ⟨(M6G.weltVon 0).speicher,
   rufUpdateG M6G.faeden 0
     ⟨[], callerFrameG, s1G.spur,
      [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G] ++
        (M6G.faeden 0).log⟩,
   M6G.lauf ++ rufEigenG 0 [],
   M6G.start⟩


end Gabbro.Grammatik
