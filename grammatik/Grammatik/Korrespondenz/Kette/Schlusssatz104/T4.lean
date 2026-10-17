/- Part 4 of 4 of `Schlusssatz104` (split by instrumente/teile/lean-teilen.py; the umbrella `Schlusssatz104.lean` imports all parts). -/
import Grammatik.Korrespondenz.Kette.Schlusssatz104.T3

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze
open G104_referenz (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies)
set_option maxRecDepth 100000

/-- **`schlusssatz_104` -- the closing theorem, stage (a), for
    `beispiele/104-referenz.gab`.** About ONE program, the `gP` the Lean
    parser produces. PREMISES: the correspondence certificate checks
    (`certOkG c = true`, by `decide` on the printed one), and the named
    assumptions that ARE Lean propositions (CUTS names the rest):

    * `hA1ein`/`hA1lies` -- A1 with A2 and A3, as a hypothesis: every run of
      the compiled `einzahlen`/`lies` (`binEin`/`binLies`, the behaviour of
      the binary, a parameter) is a run of the C semantics of the emitted
      unit `refCProg` at the emitter's layout `gEL104.lay`, at the depth the
      call tree needs;
    * `hA4` -- A4: the runtime's start (`LaufzeitStart init`: every thread
      but `0` idles in the runtime's root).

    CONCLUSIONS:
    1. PARSE FIDELITY: the source text translates to `(gP, gFs)`;
    2. MODEL CERTIFICATES: the printed statement certificates ARE the print
       of `gP`'s two bodies, and the Lean checker accepts them;
    3. MODEL JUDGEMENT: `gP` passes the fragment and footprint checks, every
       function meets the per-function obligations at EVERY `forever`
       budget, and its call semantics does not depend on the budget;
    4. EVERY C RUN: the certificate elaborates to the emitted C unit; for
       each function, from a C state related to ANY Gabbro world and C
       arguments related to ANY Gabbro arguments, the Gabbro call ends `ok`
       (every contract on the way checked), the C call has a run, and EVERY
       run of it ends related to the Gabbro result;
    5. THE MACHINE: the program the machine runs, `gPB`, is `gP` renamed
       plus the runtime's idle root, and on every reachable machine -- from
       every start memory, at every budget, from the start `init` -- the
       conclusion of the goal theorem holds, including the root function's
       `ensures` at its completion (`StartEndeG`, `KeinStartGrundG`);
    6. EVERY RUN OF THE BINARY (under `hA1ein`/`hA1lies`): from related
       starts it ends related to the Gabbro result, which is the same at
       every budget. -/
theorem schlusssatz_104 (c : Cert104) (hc : certOkG c = true)
    (binEin : CSt → List CVal → CSt → Option CVal → Prop)
    (hA1ein : ∀ st vs st' rv, binEin st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv)
    (binLies : CSt → List CVal → CSt → Option CVal → Prop)
    (hA1lies : ∀ st vs st' rv, binLies st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv)
    (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) (hA4 : LaufzeitStart init) :
    -- 1. parse fidelity
    uebersetze104 src104 = .ok (G104_referenz.gP, G104_referenz.gFs) ∧
    -- 2. model certificates
    (printEnd104 (G104_referenz.gP.rumpf g_einzahlen) = some cert104_einzahlen ∧
      certEnd104Ok G104_referenz.gD (vertragVon G104_referenz.gD g_einzahlen) false
        gCtx_einzahlen gL_einzahlen cert104_einzahlen = true ∧
      printEnd104 (G104_referenz.gP.rumpf g_lies) = some cert104_lies ∧
      certEnd104Ok G104_referenz.gD (vertragVon G104_referenz.gD g_lies) false
        gCtx_lies gL_lies cert104_lies = true) ∧
    -- 3. model judgement, at every budget
    (programmImFragmentG G104_referenz.gP G104_referenz.gFs = true ∧
      fussOrtGB G104_referenz.gP G104_referenz.gFs = true ∧
      (∀ (passes : Nat) (f : G104_referenz.gD.Fn), KoerperGutS G104_referenz.gP passes
        (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f) ∧
      (∀ (passes : Nat) (f : G104_referenz.gD.Fn), InvGutS G104_referenz.gP passes
        (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f) ∧
      (∀ (passes k : Nat) (f : G104_referenz.gD.Fn) (σ : World G104_referenz.gD)
        (ρ : Env G104_referenz.gD (G104_referenz.gD.params f)),
        rufAt G104_referenz.gP gO104 passes k f σ ρ = rufAt G104_referenz.gP gO104 0 k f σ ρ)) ∧
    -- 4. every C run
    (progOf c = refCProg ∧
      (∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cEin.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmEin c.ppEin c.ksEin) ρG ρ0 →
        ∃ σ', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
          (∃ st', CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' none) ∧
          ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' rv →
            corrW gEL104 σ' st' ∧ rv = none) ∧
      (∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cLies.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmLies c.ppLies c.ksLies) ρG ρ0 →
        ∃ σ' v, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
          (∃ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv) ∧
          ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv →
            corrW gEL104 σ' st' ∧ RetCorr gEL104 (G104_referenz.gD.erg g_lies) v rv)) ∧
    -- 5. the machine
    ((renEnd (G104_referenz.gP.rumpf g_einzahlen) = some (gPB.rumpf (some GFn.einzahlen)) ∧
      renEnd (G104_referenz.gP.rumpf g_lies) = some (gPB.rumpf (some GFn.lies)) ∧
      renE (G104_referenz.gP.ensures g_einzahlen) = some (gPB.ensures (some GFn.einzahlen)) ∧
      renE (G104_referenz.gP.ensures g_lies) = some (gPB.ensures (some GFn.lies)) ∧
      renE (G104_referenz.gP.requires g_einzahlen) = some (gPB.requires (some GFn.einzahlen)) ∧
      renE (G104_referenz.gP.requires g_lies) = some (gPB.requires (some GFn.lies)) ∧
      ruhig gPB none = true) ∧
      -- `gPB`'s source functions behave as `gP`'s, through the same emitted C
      (∀ (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen))
        (ρB : Env gDB (gDB.params (some GFn.einzahlen))) (vs : List CVal) (ρ0 : CLok),
        corrW gEL104 σ st → corrW gEBL σB st → bindParams cEin.params vs = some ρ0 →
        EnvRel gEL104 kEinG ρG ρ0 → EnvRel gEBL kEinB ρB ρ0 →
        ∃ σ' σB', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
          rufAt gPB gOB 0 2 (some GFn.einzahlen) σB ρB = .ok σB' () ∧
          ∀ k : Int, 0 ≤ k → k < 2 → (σ'.slots GTab.Konto k GKontoFeld.stand).n =
            (σB'.slots GTab.Konto k GKontoFeld.stand).n) ∧
      (∀ (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies))
        (ρB : Env gDB (gDB.params (some GFn.lies))) (vs : List CVal) (ρ0 : CLok),
        corrW gEL104 σ st → corrW gEBL σB st → bindParams cLies.params vs = some ρ0 →
        EnvRel gEL104 kLiesG ρG ρ0 → EnvRel gEBL kLiesB ρB ρ0 →
        ∃ σ' v σB' vB, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
          rufAt gPB gOB 0 1 (some GFn.lies) σB ρB = .ok σB' vB ∧
          (show Zahl 0 100 from v).n = (show Zahl 0 100 from vB).n ∧
          ∀ k : Int, 0 ≤ k → k < 2 → (σ'.slots GTab.Konto k GKontoFeld.stand).n =
            (σB'.slots GTab.Konto k GKontoFeld.stand).n) ∧
      (∀ (passes k : Nat) (f : gDB.Fn) (σ : World gDB) (ρ : Env gDB (gDB.params f)),
        rufAt gPB gOB passes k f σ ρ = rufAt gPB gOB 0 k f σ ρ) ∧
      ∀ (sp : Speicher gDB) (passes : Nat) (M : RufMaschineG gDB),
        RufErreichbarG gPB gOB passes (RufStartG gPB sp init) M →
          ((VertragAmOrtG gPB M ∧ SperrInvG (SperrInv.leer gDB) M ∧ KeinLogikHaltG gOB passes M ∧
            ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
              AnPruefungG M t → ∃ M', RufSchrittG gPB gOB passes M t M') ∧
          InvAmOrtG gPB M) ∧ StartEndeG gPB M ∧ KeinStartGrundG M) ∧
    -- 6. every run of the binary
    ((∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cEin.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmEin c.ppEin c.ksEin) ρG ρ0 →
        ∃ σ', (∀ passes : Nat, rufAt G104_referenz.gP gO104 passes 2 g_einzahlen σ ρG = .ok σ' ()) ∧
          ∀ st' rv, binEin st vs st' rv → corrW gEL104 σ' st' ∧ rv = none) ∧
      (∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cLies.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmLies c.ppLies c.ksLies) ρG ρ0 →
        ∃ σ' v, (∀ passes : Nat, rufAt G104_referenz.gP gO104 passes 1 g_lies σ ρG = .ok σ' v) ∧
          ∀ st' rv, binLies st vs st' rv →
            corrW gEL104 σ' st' ∧ RetCorr gEL104 (G104_referenz.gD.erg g_lies) v rv)) := by
  refine ⟨uebersetze104_ok,
    ⟨print104_einzahlen, cert104_einzahlen_ok, print104_lies, cert104_lies_ok⟩,
    ⟨export104_fragment, export104_fuss, gP_koerperS_alle, gP_invGutS_alle, gP_rufAt_passes⟩,
    ⟨progOf_ok c hc, fun σ st ρG vs ρ0 hw hb hr => c104_einzahlen c hc σ st ρG vs ρ0 hw hb hr,
      fun σ st ρG vs ρ0 hw hb hr => c104_lies c hc σ st ρG vs ρ0 hw hb hr⟩,
    ⟨gPB_ist_gP_umbenannt, gPB_wie_gP_einzahlen, gPB_wie_gP_lies, gPB_rufAt_passes,
      gPB_ziel init hA4⟩, ?_, ?_⟩
  · intro σ st ρG vs ρ0 hw hb hr
    obtain ⟨σ', hR, _, hall⟩ := c104_einzahlen c hc σ st ρG vs ρ0 hw hb hr
    refine ⟨σ', fun passes => (gP_rufAt_passes passes 2 _ σ ρG).trans hR, fun st' rv hbin => ?_⟩
    exact hall st' rv (by rw [progOf_ok c hc]; exact hA1ein _ _ _ _ hbin)
  · intro σ st ρG vs ρ0 hw hb hr
    obtain ⟨σ', v, hR, _, hall⟩ := c104_lies c hc σ st ρG vs ρ0 hw hb hr
    refine ⟨σ', v, fun passes => (gP_rufAt_passes passes 1 _ σ ρG).trans hR, fun st' rv hbin => ?_⟩
    exact hall st' rv (by rw [progOf_ok c hc]; exact hA1lies _ _ _ _ hbin)

/-- The premise holds for the certificate as printed (rows and layout from
    `printed104`, `certG104_rows`), by `decide`; it elaborates to the emitted
    unit. `schlusssatz_104 certG104 certG104_ok` is the closed chain. -/
theorem schlusssatz_104_praemisse :
    certOkG certG104 = true ∧ certG104.einRows = printed104.einRows ∧
      certG104.liesRows = printed104.liesRows ∧ certG104.lay = printed104.lay ∧
      progOf certG104 = refCProg :=
  ⟨certG104_ok, certG104_rows.1, certG104_rows.2.1, certG104_rows.2.2, progOf_ok _ certG104_ok⟩


/-! ### 6.1 Witnesses (rule 13): the premises are jointly satisfiable, on runs that move memory -/

/-- The zero world of `gD`: both slots `0`, empty trace. -/
def gWelt0 : World G104_referenz.gD :=
  ⟨fun t _ f => (match t, f with | .Konto, .stand => ⟨0, by decide, by decide⟩),
    (fun g => nomatch g), []⟩

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def gRho7 : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

theorem gW0_corr : corrW gEL104 gWelt0 refSt0 := by
  refine ⟨?_, And.intro (fun g => nomatch g) (fun _ h => Bool.noConfusion h)⟩
  intro t _
  cases t
  refine ⟨rfl, ?_⟩
  intro k f hk0 hk
  cases f
  have hk2 : k < 2 := hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with e | e <;> subst e <;> rfl

theorem gRho7_env : EnvRel gEL104 (kOfG certG104.vmEin certG104.ppEin certG104.ksEin) gRho7
    (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩)) := by
  refine ⟨?_, fun q hq => absurd hq (by simp [certG104, kOfG]),
    fun q hq => absurd hq (by simp [certG104, kOfG])⟩
  intro τ x
  cases x with
  | here => exact ⟨GTab.Konto, rfl, rfl⟩
  | there y =>
      cases y with
      | here => rfl
      | there z =>
          cases z with
          | here => rfl
          | there w => exact nomatch w

/-- **WITNESS, part 4**: `einzahlen(k, 0, 7)` from the zero state -- the
    premises of part 4 hold jointly; by the theorem the Gabbro call ends
    `ok` and EVERY C run ends related to it; the slot moved `0 -> 100` in
    the Gabbro world and in the C cell. -/
theorem schlusssatz_104_zeuge :
    ∃ σ' : World G104_referenz.gD,
      rufAt G104_referenz.gP gO104 0 2 g_einzahlen gWelt0 gRho7 = .ok σ' () ∧
      (gWelt0.slots GTab.Konto 0 GKontoFeld.stand).n = 0 ∧
      (σ'.slots GTab.Konto 0 GKontoFeld.stand).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧
      (∃ st', CallAt gEL104.lay tvOrc tvXR (progOf certG104) 2 0 refSt0 einArgs st' none) ∧
      ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf certG104) 2 0 refSt0 einArgs st' rv →
        st'.mem (.tab 0) 0 = .int 100 ∧ rv = none := by
  obtain ⟨σ', hR, hex, hall⟩ := (schlusssatz_104 certG104 certG104_ok _ (fun _ _ _ _ h => h) _ (fun _ _ _ _ h => h)
    (fun _ => ⟨none, .nil⟩) (fun _ _ => rfl)).2.2.2.1.2.1 gWelt0 refSt0 gRho7
    einArgs _ gW0_corr rfl gRho7_env
  have hR' : rufAt G104_referenz.gP gO104 0 2 g_einzahlen gWelt0 gRho7 = .ok _ () := rfl
  rw [hR'] at hR
  cases hR
  refine ⟨_, hR', rfl, rfl, rfl, hex, fun st' rv hC => ?_⟩
  obtain ⟨hc, hrv⟩ := hall st' rv hC
  exact ⟨(hc.1 GTab.Konto rfl).2 0 GKontoFeld.stand (by decide) (by decide), hrv⟩


/-! ### 6.2 A reached machine of `gPB` -/

/-- The zero start memory of `gDB`. -/
def gbSp0 : Speicher gDB :=
  ⟨fun t _ f => (match t, f with | .Konto, .stand => ⟨0, by decide, by decide⟩), (fun g => nomatch g)⟩

/-- `einzahlen(k, 0, 7)` on the machine. -/
def gbRho7 : Env gDB (gDB.params (some GFn.einzahlen)) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

theorem gbHoff {M : RufMaschineG gDB} {f : Faden} {z : RufFadenG gDB} {x : List GLock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

theorem gbHg {s : List (Ereignis gDB)} (h : offen s = [GLock.M]) : HeldGenau gbL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

/-- **WITNESS, part 5**: a reached machine of `gPB` (thread 0 runs
    `einzahlen(k, 0, 7)`, three steps: the write, the call of `lies`, its
    return): memory `0 -> 100`, the return of `lies` is logged, and its
    `ensures result == k.slots[i].stand` holds there BY THE THEOREM. -/
theorem schlusssatz_104_maschine_zeuge :
    ∃ M : RufMaschineG gDB,
      RufErreichbarG gPB gOB 0 (RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)) M ∧
      (gbSp0.slots GTab.Konto 0 GKontoFeld.stand).n = 0 ∧
      (M.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100 ∧
      ∃ (rho : Env gDB (gDB.params (some GFn.lies))) (v : ErgVal gDB (gDB.erg (some GFn.lies)))
        (s0 s1 : World gDB),
        RufEreignisF.rueck (some GFn.lies) rho v s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck gPB (some GFn.lies) s0 s1 rho v ∧
        -- the root `einzahlen` has finished (empty stack, head at its `return`):
        -- its `ensures` holds at its completion, BY THE THEOREM (`StartEndeG`)
        (M.faeden 0).stapel = [] ∧
        ∃ w : World gDB, EnsAmRueck gPB (some GFn.einzahlen) (gbSp0.welt []) w gbRho7 () := by
  have h00 : (RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)).faeden 0 =
      ⟨[], ⟨some GFn.einzahlen, gbRho7, gbSp0.welt [],
        ⟨false, gDB.params (some GFn.einzahlen), gbL, gbRho7, .ende gbBody_einzahlen⟩⟩,
        startSpur (some GFn.einzahlen),
        [RufEreignisF.eintritt (some GFn.einzahlen) gbRho7 (gbSp0.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)).faeden 0).spur =
      [GLock.M] := rfl
  -- 1: the write through the pointer
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := gPB) (O := gOB) (passes := 0) h00 _ _ _
    rfl rfl (gbHg hoff0).heldIn _ _ rfl ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff1 : offen (M1.faeden 0).spur = [GLock.M] := by
    rw [hZ1.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff0)
  have e1 := hZ1.1
  try dsimp only at e1
  -- 2: call `lies`
  obtain ⟨M2, s2, hZ2⟩ := w_rufEnde (P := gPB) (O := gOB) (passes := 0) e1 (some GFn.lies) _ gbHp rfl
    _ _ rfl (gbHg (gbHoff e1 hoff1)).heldIn
  have hoff2 : offen (M2.faeden 0).spur = [GLock.M] := by
    rw [hZ2.spur, (Erw.lese _ _ _).offen]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  -- 3: `lies` returns
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := gPB) (O := gOB) (passes := 0) e2 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (gbHg (gbHoff e2 hoff2)).heldIn
  have hr3 : RufErreichbarG gPB gOB 0 (RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)) M3 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3
  have hsp : (M3.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100 := by
    rw [hG3.2]
    show (M2.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100
    rw [hZ2.2]
    show (M1.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100
    rw [hZ1.2]
    rfl
  have hlog := congrArg RufFadenG.log hG3.1
  have hex : ∃ (rho : Env gDB (gDB.params (some GFn.lies)))
      (v : ErgVal gDB (gDB.erg (some GFn.lies))) (w0 w1 : World gDB),
      RufEreignisF.rueck (D := gDB) (some GFn.lies) rho v w0 w1 ∈ (M3.faeden 0).log := by
    rw [hlog]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  obtain ⟨rho, v, w0, w1, hm⟩ := hex
  have hens := ((gPB_ziel (bootInit GFn.einzahlen gbRho7) (bootInit_laufzeit _ _) gbSp0 0 M3
    hr3).1.1.1 0 _ hm).2 (some GFn.lies) rho v w0 w1 rfl
  have hSE := (gPB_ziel (bootInit GFn.einzahlen gbRho7) (bootInit_laufzeit _ _) gbSp0 0 M3 hr3).2.1 0
  have h3 := hG3.1
  rw [h3] at hSE
  have hroot := (hSE rfl _ _ _ _ _ .empty rfl ⟨_, Or.inl rfl⟩).1
  exact ⟨M3, hr3, rfl, hsp, rho, v, w0, w1, hm, hens, by rw [h3], _, hroot⟩

/-- **The premises of `schlusssatz_104` are jointly satisfiable** (rule
    13): the printed certificate, the C semantics itself as the binary's
    behaviour (the hypotheses A1 hold with equality), and the runtime's
    start `bootInit` (A4) -- the start of the reached machine above. -/
theorem schlusssatz_104_praemissen :
    certOkG certG104 = true ∧
    (∀ st vs st' rv, CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv) ∧
    (∀ st vs st' rv, CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv) ∧
    LaufzeitStart (bootInit GFn.einzahlen gbRho7) :=
  ⟨certG104_ok, fun _ _ _ _ h => h, fun _ _ _ _ h => h, bootInit_laufzeit _ _⟩

example := schlusssatz_104 certG104 certG104_ok _ (fun _ _ _ _ h => h) _ (fun _ _ _ _ h => h)
  (bootInit GFn.einzahlen gbRho7) (bootInit_laufzeit _ _)


/-! ## CUTS

  THE PREMISES of `schlusssatz_104` (since 2026-09-14 the named
  assumptions that ARE Lean propositions are hypotheses of the theorem):

  * `hc : certOkG c = true` -- the correspondence certificate checks.
    Discharged for the printed rows by `decide` (`schlusssatz_104_praemisse`).
  * `hA1ein`/`hA1lies` -- A1 with A2 and A3 as ONE Lean hypothesis per
    function: every run of the binary's `einzahlen`/`lies` (`binEin`,
    `binLies`: the behaviour of the compiled code, parameters of the
    theorem) is a run of `CallAt gEL104.lay tvOrc tvXR refCProg` -- the C
    semantics of `CSemantik`/`CSpeicher`/`CFormen*`, applied to the emitted
    unit as the CS term `refCProg`, at the emitter's layout, at the call
    depth the call tree needs (2 for `einzahlen`, 1 for `lies`). Part 6
    then states EVERY run of the binary; part 4 stays a statement about the
    C semantics.
  * `hA4 : LaufzeitStart init` -- A4, fully a Lean proposition: every
    thread but `0` idles in the runtime's root `none`. Part 5 holds for
    EVERY such start (`bootInit` is one: `bootInit_laufzeit`).
  * No hardware or oracle premise: `gD` declares no axiom, register,
    device, global or `awaits` (`gO104`/`gOB` are forced by empty types,
    `GutO`/`RegLokal` proved), and the emitted unit makes no device access
    and no foreign call (`tvOrc`, `tvXR`; `tvXR_funktional`).
  * Jointly satisfiable: `schlusssatz_104_praemissen` (the C semantics
    itself as the binary's behaviour, `bootInit`), and the `example`.

  WHAT STAYS OUTSIDE LEAN -- the parts of A1-A5 that are no Lean
  proposition, precisely:

  A1. That `binEin`/`binLies` ARE the behaviour of the binary a C compiler
      produced from the emitted file -- i.e. that the compiler implements
      the C semantics of the model. A statement about a program outside
      Lean (the compiler); the theorem is conditional on it through the
      hypotheses, not by construction. Also outside: that the depth-2/1
      runs are all runs (no monotonicity lemma for `CallAt` in its fuel).
  A2. That the emitted TEXT means `refCProg`. `refCProg`/`cEinBody`/
      `cLiesBody` are a hand transcription of the quoted emitter output
      (`CFormenZeuge.lean`, `Korrespondenz104.lean`; byte identity of the
      quote with `gabbro emit` measured 2026-09-13, not proved); the
      certificate rows elaborate to them (`progOf_ok`) and are the Rust
      printer's rows (`certG104_rows`). WHAT WOULD REPLACE IT: a C parser
      in Lean for the emitter's subset, `parseC : String → Option CProg`,
      the emitted text pinned as a `String`, and `parseC text = some
      refCProg` by `decide`. A2 would then shrink to "the compiler's front
      end reads the subset as `parseC` does" -- a part of A1.
  A3. That the compiler lays out `Konto` as `kontoLay` (2 records of 4
      bytes, `stand` at offset 0, `uint32_t`; `kontoLay_werte`). It is in
      the A1 hypothesis (`gEL104.lay`); the emitted `_Static_assert` pins
      (`CFormenM` M11) are checked BY THE COMPILER, so A3 reduces to A1 +
      A2 plus one missing Lean lemma: the C semantics depends on a
      `RecLay` only through the pinned numbers (fields `< nf`).
  A4. That the real runtime starts the program in a `LaufzeitStart` shape
      (the C driver that makes the call is not emitted). The shape itself
      is the hypothesis `hA4`.
  A5. The Lean kernel, and the DEFINITIONS a human must read (plan §3):
      machine G, `rufAt`/`execEnd`, `KoerperGutS`, `VertragAmOrtG`, the C
      semantics, `corrW`/`EnvRel`. Not a proposition.

  THE `forever` BUDGET: `gP` and `gPB` contain no `forever` loop; the
  obligations (part 3) are stated at EVERY budget (`koerperGutS_alle`),
  the call semantics is budget-independent (`gP_rufAt_passes`,
  `gPB_rufAt_passes`: every `rufAt … 0 …` of parts 4-6 holds at every
  budget), and part 5 holds on the machines of every budget.

  JOINTS -- what is closed and how:

  J1. P identity. CLOSED for the parser's `gP`: parse (1), model
      certificates (2), model judgement (3) and the C correspondence (4)
      are all about `gP` itself; `r4P`/`refP` are no longer in the chain.
      The machine (5) needs `gPB` = `gP` plus the idle root, related to `gP`
      by a proved translation: syntactically (`gPB_ist_gP_umbenannt`, the
      renaming `renEnd`/`renE` applied to `gP`'s bodies and contracts gives
      `gPB`'s, by `rfl`) and semantically for both source functions
      (`gPB_wie_gP_*`: same memory effect and answer, through the emitted C).
  J2. Model certificates are FOR `gP`: `print104_*` (the Lean print of
      `gP`'s bodies is the pasted printer output), accepted by `decide`.
  J3. The C correspondence is about `gP`'s bodies (`liesG_end`, `einG_end`)
      and the emitted text (A2); the certificate is load-bearing
      (`progOf_ok`, `kOf_ok`, `corrCertG_sound`).
  J4. Single-threaded completeness: `ziel_ort_einfaden` (no footprint or
      exclusivity premise) for the machine; every C run by
      `callAt_funktional` (`exec_det`).

  NOT PROVED (named):

  - The source text is the comment-free one-line form `u104lex` pins; the
    real file with comments is lane 162's.
  - The certificate's MAP (`vm`/`pp`/`ks`) is `gP`'s and is NOT what
    `corrlean.rs` prints today: the printer prints `refD`'s map (`vm = [2]`,
    the `MODEL DATUM` index `ks = [(1, 0)]`). Its rows and layout are the
    printer's. Moving the printer to the exporter's map is Rust work (no
    `cargo` in this lane).
  - `renE`/`renEnd` are PARTIAL (the 104 fragment and some more; `none`
    elsewhere) and their semantic preservation is not proved in general;
    the semantic bridge is proved for 104's two functions only, and only
    for starts related to one C state.
  - Part 4 relates C runs to `rufAt` (the sequential semantics), part 5
    states the goal theorem on machine G of `gPB`; that G with one active
    thread agrees with `rufAt` is the adequacy chain (`rufG_adaequat_ruf`),
    not re-instantiated here. (Part 5 now carries the root's `ensures` at
    its completion -- `StartEndeG`, witnessed on a reached machine in
    `schlusssatz_104_maschine_zeuge` -- so the root's contract is no longer
    carried by part 4 alone.)
  - The C statements are at the depth the call tree needs (`einzahlen` at 2,
    `lies` at 1); deeper `CallAt` fuel is not stated (no monotonicity lemma).
  - `corrW` relates memory, not traces: Gabbro's lock trace and C's
    observation list are not related (CSpeicher CUTS).
  - Stage (b): concurrency (DRF-SC, lock primitives, thread creation) is
    not addressed; `gP_kein_exklusiv` shows a two-active-thread start of
    this program is refused by the model anyway (every function holds `M`).
  - Widening beyond 104: everything keyed to `gD`: the lowering
    (`lowerProg`), `certOkG` (fixed rows), `printEnd104` (the 104 shapes),
    the renaming target `gDB`, the per-program `rufAt` computations
    (`rufEin_ok`) that stand in for a general "obligations imply `rufAt` ok"
    theorem, and the copied C correspondence of 5.5.
-/

#print axioms Gabbro.Grammatik.uebersetze104_ok
#print axioms Gabbro.Grammatik.corrCertG_sound
#print axioms Gabbro.Grammatik.c104_einzahlen
#print axioms Gabbro.Grammatik.c104_lies
#print axioms Gabbro.Grammatik.print104_einzahlen
#print axioms Gabbro.Grammatik.print104_lies
#print axioms Gabbro.Grammatik.gP_koerperS
#print axioms Gabbro.Grammatik.gP_kein_ruhig
#print axioms Gabbro.Grammatik.gP_kein_exklusiv
#print axioms Gabbro.Grammatik.gPB_ist_gP_umbenannt
#print axioms Gabbro.Grammatik.gPB_ziel
#print axioms Gabbro.Grammatik.gPB_wie_gP_einzahlen
#print axioms Gabbro.Grammatik.gPB_wie_gP_lies
#print axioms Gabbro.Grammatik.schlusssatz_104
#print axioms Gabbro.Grammatik.schlusssatz_104_praemisse
#print axioms Gabbro.Grammatik.schlusssatz_104_zeuge
#print axioms Gabbro.Grammatik.schlusssatz_104_maschine_zeuge
#print axioms Gabbro.Grammatik.schlusssatz_104_praemissen
#print axioms Gabbro.Grammatik.gP_rufAt_passes


end Gabbro.Grammatik
