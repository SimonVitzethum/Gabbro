/- Part 3 of 4 of `Schlusssatz104` (split by instrumente/teile/lean-teilen.py; the umbrella `Schlusssatz104.lean` imports all parts). -/
import Grammatik.Korrespondenz.Kette.Schlusssatz104.T2

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze
open G104_referenz (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies)
set_option maxRecDepth 100000

theorem gPB_einzahlen_R : KoerperGutR gPB 0 (some GFn.einzahlen) := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : gPB.rumpf (some GFn.einzahlen) = gbBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 (some GFn.lies) _ _ σ2 w hRv).1.1 GTab.Konto rfl
      simp only [execStmt] at h1
      cases h1
      show decide ((σ.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n ≤
        (σ2.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n) = true
      have e3 := (hfr (ρ.get (.there .here)).n GKontoFeld.stand).trans
        (storeSlot_hit (D := gDB) _ GTab.Konto _ GKontoFeld.stand _)
      have h100 : (σ2.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).le_hi
        (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : gPB.rumpf (some GFn.einzahlen) = gbBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact gb_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem gPB_koerperS : ∀ f : gDB.Fn,
    KoerperGutS gPB 0 (axWahr gDB) (SperrInv.leer gDB) f :=
  fun f => koerperGutS_leer ⟨koerperGutRQ_of_R _ (match f with
    | some .einzahlen => gPB_einzahlen_R
    | some .lies => koerperGutR_of_V gPB_koerper_lies
    | none => koerperGutR_of_V gPB_koerper_ruhe),
    programmLogikFrei_ok gbFs_voll gPB_logikFrei 0 _ f⟩

/-- The oracle of `gDB`: no axiom, register or global exists. -/
def gOB : Orakel gDB where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem gOB_gut : GutO gOB := fun a => nomatch a

theorem gOB_lokal : RegLokal gOB := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- **The runtime's start**: thread 0 runs the source function `f` on the
    arguments `ρ` (whatever the driver calls), every other thread idles. -/
def bootInit (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    Faden → Σ g : gDB.Fn, Env gDB (gDB.params g) :=
  fun t => if t = 0 then ⟨some f, ρ⟩ else ⟨none, .nil⟩

theorem bootInit_ruhig (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    ∀ u, u ≠ 0 → ruhig gPB (bootInit f ρ u).1 = true := by
  intro u hu
  unfold bootInit
  rw [if_neg hu]
  exact gPB_ruhig

theorem bootInit_start (sp : Speicher gDB) (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    StartGut gPB sp (bootInit f ρ) := by
  intro t
  unfold bootInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]; rfl

theorem gPB_ohneEwig : ohneEwigB gPB gbFs = true := by decide

theorem gPB_koerperS_alle : ∀ (passes : Nat) (f : gDB.Fn),
    KoerperGutS gPB passes (axWahr gDB) (SperrInv.leer gDB) f :=
  koerperGutS_alle gbFs_voll gPB_ohneEwig gPB_koerperS

theorem gPB_rufAt_passes : ∀ (passes k : Nat) (f : gDB.Fn) (σ : World gDB)
    (ρ : Env gDB (gDB.params f)), rufAt gPB gOB passes k f σ ρ = rufAt gPB gOB 0 k f σ ρ :=
  fun passes => rufAt_passes gOB (ohneEwigB_ok gbFs_voll gPB_ohneEwig) passes 0

/-- No function of `gDB` declares a reason. -/
theorem gDB_ohneGrund (g : gDB.Fn) : gDB.gruende g = 0 := by
  rcases g with _ | f
  · rfl
  · cases f <;> rfl

/-- **A4 AS A LEAN PROPOSITION: the runtime's start.** Every thread but `0`
    idles in the runtime's root `none`; thread `0` runs whatever the driver
    calls (a source function on its arguments -- or nothing). -/
def LaufzeitStart (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) : Prop :=
  ∀ u, u ≠ 0 → init u = ⟨none, .nil⟩

theorem bootInit_laufzeit (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    LaufzeitStart (bootInit f ρ) := by
  intro u hu
  unfold bootInit
  rw [if_neg hu]

/-- **THE GOAL THEOREM ON THE MACHINE OF `gPB`** -- for EVERY start that
    has the runtime's shape (A4, `LaufzeitStart`), from EVERY start memory,
    at EVERY `forever` budget: on every reachable machine the contracts
    hold at every logged event, the (empty) lock invariants hold, no thread
    is stuck at a `logik` check, the progress conjunct holds, every owed
    invariant holds at every logged return, and -- new -- at a finished
    thread `0` the root function's `ensures` holds (`StartEndeG`), and it
    finished at a value return (`KeinStartGrundG`). `ziel_ort_einfaden_ende`. -/
theorem gPB_ziel (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) (hA4 : LaufzeitStart init) :
    ∀ (sp : Speicher gDB) (passes : Nat) (M : RufMaschineG gDB),
      RufErreichbarG gPB gOB passes (RufStartG gPB sp init) M →
      ((VertragAmOrtG gPB M ∧ SperrInvG (SperrInv.leer gDB) M ∧ KeinLogikHaltG gOB passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG gPB gOB passes M t M') ∧
      InvAmOrtG gPB M) ∧ StartEndeG gPB M ∧ KeinStartGrundG M :=
  fun sp => ziel_ort_einfaden_ende gPB gOB (axWahr gDB) (SperrInv.leer gDB) gbFs sp init
    gOB_gut gOB_lokal (axVertragO_wahr gOB) axEnsLokal_wahr sperrInvOk_leer gbFs_voll gPB_fragment
    (fun u hu => by rw [hA4 u hu]; exact gPB_ruhig) gPB_koerperS_alle (fun _ => rfl) (fun _ => rfl)
    (fun _ => invGutS_leer rfl) (fun _ => gDB_ohneGrund _)


/-! ### 5.5 `gPB` behaves as `gP`: both against the same emitted C

The renaming of 5.3 is syntactic. Its semantic content, for the two source
functions: the C correspondence of `gPB`'s bodies against the SAME emitted
unit (a copy of section 2 over `gDB`), and then, from worlds related to one
C state, both Gabbro calls end `ok` and agree -- every C run relates to both
(`gPB_wie_gP_einzahlen`, `gPB_wie_gP_lies`). -/

def kEinB : CEnvLay gDB (gDB.params (some GFn.einzahlen)) := ⟨[0, 1, 2], [], []⟩

def kLiesB : CEnvLay gDB (gDB.params (some GFn.lies)) := ⟨[0, 1], [], []⟩

/-- The emitter's layout over `gDB` -- the same layout as `gEL104`
    (the carriers are `gD`'s). -/
def gEBL : EmitLay gDB where
  lay := refLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => kontoLay
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun t => by cases t; rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun t f f' _ => by cases t; cases f; cases f'; rfl
  fnr_fits := fun t f => by cases t; cases f; rfl
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- `lies` runs in frame 1, calling nothing. -/
def xLiesB : TVCtx gDB :=
  ⟨gEBL, tvOrc, 1, CallAt gEBL.lay tvOrc tvXR refCProg 0, tvXR, gOB, 0, rufAt gPB gOB 0 0⟩

/-- `einzahlen` runs in frame 2, its callees at depth 1. -/
def xEinB : TVCtx gDB :=
  ⟨gEBL, tvOrc, 2, CallAt gEBL.lay tvOrc tvXR refCProg 1, tvXR, gOB, 0, rufAt gPB gOB 0 1⟩

/-! #### 5.5.1 `lies` of `gPB` against the emitted `lies` -/

/-- `return k->slots[i].stand;` corresponds to `gPB`'s `lies` body:
    `k` is C local 0 (Gabbro variable 0), `i` C local 1 (variable 1). -/
theorem liesB_end (m : Nat) : EndCorr xLiesB m true kLiesB (gPB.rumpf (some GFn.lies)) cLiesBody := by
  have hi : ExprCorr xLiesB kLiesB (.var 1)
      (Expr.var (D := gDB) (Γ := (gDB.params (some GFn.lies))) (Λ := gbL) (.there .here)) :=
    ecorr_var xLiesB kLiesB (.there .here)
  have hp : PtrTo xLiesB kLiesB (.var 0) GTab.Konto :=
    ptrTo_var xLiesB kLiesB (Γ := (gDB.params (some GFn.lies))) (.here) rfl
  have he := ecorr_durch xLiesB kLiesB (Λ := gbL) (rw := false) (p := Expr.var .here)
    rfl hp GKontoFeld.stand rfl gbDarf hi
  exact EndCorr.ret (by rfl) ⟨cU32, _, rfl, he, rfl⟩

/-- THE CALLEE RELATION of `lies` at depth 1. -/
theorem liesB_fn : FnCorr gEBL (rufAt gPB gOB 0 1) (CallAt gEBL.lay tvOrc tvXR refCProg 1)
    (some GFn.lies) 1 cLies.params kLiesB :=
  cCorr_ruf gEBL tvOrc tvXR gPB gOB 0 0 refCProg (some GFn.lies) 1 cLies rfl kLiesB 0
    (cCorr_end xLiesB 0 true (liesB_end 0))

/-! #### 5.5.2 `einzahlen` of `gPB` against the emitted `einzahlen` -/

/-- `(void)b;` evaluates Gabbro's `b` (variable 2, C local 2). -/
theorem einB_void :
    ExprCorr xEinB kEinB (.var 2)
      (Expr.var (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) (.there (.there .here))) :=
  ecorr_var xEinB kEinB (.there (.there .here))

/-- `k->slots[i].stand = 100;` against `k.slots[i].stand = 100` through the
    `rw` pointer `k`. -/
theorem einB_write (m : Nat) :
    StmtCorr xEinB m kEinB
      (Stmt.assignThru (V := vertragVon gDB (some GFn.einzahlen)) (l := false) (Γ := (gDB.params (some GFn.einzahlen)))
        (Λ := gbL) (.var .here) GTab.Konto rfl GKontoFeld.stand (.var (.there .here))
        (.widen (by decide) (by decide) (.lit 100)) (by decide) gbDarf)
      (.store cStand cU32 (.lit 100)) := by
  have hi : ExprCorr xEinB kEinB (.var 1)
      (Expr.var (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) (.there .here)) :=
    ecorr_var xEinB kEinB (.there .here)
  have he : ExprCorr xEinB kEinB (.lit 100)
      (Expr.widen (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) (lo' := 0) (hi' := 100)
        (by decide) (by decide) (.lit 100)) :=
    ecorr_weiter xEinB kEinB _ _ (ecorr_lit xEinB kEinB 100)
  have hp : PtrTo xEinB kEinB (.var 0) GTab.Konto :=
    ptrTo_var xEinB kEinB (Γ := (gDB.params (some GFn.einzahlen))) (.here) rfl
  exact scorr_assignDurch xEinB kEinB m rfl hp GKontoFeld.stand rfl _ _ hi he

/-- The arguments of `lies(k, i);`: C passes `k` (local 0) and `i`
    (local 1); Gabbro passes a read-only pointer to the same table and `i`.
    A pointer's C value is the table's address either way. -/
theorem einB_args : ArgsTo xEinB kEinB
    (Args.cons (Expr.ptrOf (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) GTab.Konto 0 rfl false)
      (Args.cons (Expr.var (.there .here)) .nil))
    [.var 0, .var 1] cLies.params kLiesB := by
  intro σ st ρG ρC _ hr
  have h0 := hr.1 _ (Var.here (Γ := [.index 2, .int 0 10]) (τ := .ptr 0 true))
  have h1 := hr.1 _ (Var.there (σ := .ptr 0 true) (Var.here (Γ := [.int 0 10]) (τ := .index 2)))
  obtain ⟨t0, ht0, e0⟩ := h0
  have et : t0 = GTab.Konto := by cases t0; rfl
  subst et
  have e0' : ρC 0 = .ptr ⟨.tab 0, 0⟩ := e0
  have e1' : ρC 1 = .int (encW (.index 2) (ρG.get (.there .here))) := h1
  have hc1 : convV cU32 (ρC 1) = some (ρC 1) := by
    rw [e1']
    exact convV_of_valCorr (EL := gEBL) (τ := .index 2) (v := ρG.get (.there .here)) rfl rfl
  refine ⟨[ρC 0, ρC 1], st, lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0), ?_,
    SameML.refl st, ?_, ?_⟩
  · simp only [evArgs, ev, e0', e1']
  · show (match convV .ptr (ρC 0), bindParams [(1, cU32)] [ρC 1] with
      | some v', some ρ => some (lokUpd ρ 0 v')
      | _, _ => none) = _
    have hb1 : bindParams [(1, cU32)] [ρC 1] = some (lokUpd (fun _ => .undef) 1 (ρC 1)) := by
      show (match convV cU32 (ρC 1), bindParams [] [] with
        | some v', some ρ => some (lokUpd ρ 1 v')
        | _, _ => none) = _
      rw [hc1]
      rfl
    rw [hb1, e0']
    rfl
  · refine ⟨?_, fun q hq => absurd hq (by simp [kLiesB]),
      fun q hq => absurd hq (by simp [kLiesB])⟩
    intro τ x
    cases x with
    | here =>
        refine ⟨GTab.Konto, rfl, ?_⟩
        show lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 0 = _
        simp only [lokUpd, if_pos]
        exact e0'
    | there y =>
        cases y with
        | here =>
            show ValCorr gEBL (.index 2) _ (lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 1)
            simp only [lokUpd]
            rw [e1']
            rfl
        | there z => exact nomatch z

/-- `lies(k, i);` against `gPB`'s call of `lies`. -/
theorem einB_call (m : Nat) :
    StmtCorr xEinB m kEinB
      (Stmt.call (V := vertragVon gDB (some GFn.einzahlen)) (l := false) (Γ := (gDB.params (some GFn.einzahlen))) (some GFn.lies)
        (Args.cons (Expr.ptrOf (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) GTab.Konto 0 rfl false)
          (Args.cons (Expr.var (.there .here)) .nil))
        gbHp rfl)
      (.call 1 [.var 0, .var 1] none) :=
  scorr_call xEinB kEinB m (some GFn.lies) _ gbHp rfl liesB_fn einB_args

/-- THE BODY of `einzahlen` against the emitted body. -/
theorem einB_end (m : Nat) : EndCorr xEinB m true kEinB (gPB.rumpf (some GFn.einzahlen)) cEinBody :=
  EndCorr.pre einB_void
    (EndCorr.cons (einB_write m) (EndCorr.cons (einB_call m) (EndCorr.retEnd (by rfl) rfl rfl)))

/-- THE CALLEE RELATION of `einzahlen` at depth 2. -/
theorem einB_fn : FnCorr gEBL (rufAt gPB gOB 0 2) (CallAt gEBL.lay tvOrc tvXR refCProg 2)
    (some GFn.einzahlen) 0 cEin.params kEinB :=
  cCorr_ruf gEBL tvOrc tvXR gPB gOB 0 1 refCProg (some GFn.einzahlen) 0 cEin rfl kEinB 0
    (cCorr_end xEinB 0 true (einB_end 0))

/-- `lies` on `gPB`, from ANY world and arguments, at any depth: the call
    ends `ok` (requires, ensures and invariants all checked by `rufAt`),
    and the answer world has the caller's slots. -/
theorem rufLiesB_ok (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    ∃ σ' v, rufAt gPB gOB 0 (n + 1) (some GFn.lies) σ ρ = .ok σ' v ∧ σ'.slots = σ.slots := by
  have h := rufAt_ok_of_gates gPB gOB 0 n (some GFn.lies) σ ρ _ rfl rfl _ _ rfl _ rfl
    (by show wahr? (decide (_ = _)) = true; exact decide_eq_true rfl) _ rfl rfl
  exact ⟨_, _, h, rfl⟩

/-- The answer world of `lies` (chosen; its slots are the caller's). -/
noncomputable def liesWB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) : World gDB :=
  Classical.choose (rufLiesB_ok n σ ρ)

theorem liesWB_spec (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    ∃ v, rufAt gPB gOB 0 (n + 1) (some GFn.lies) σ ρ = .ok (liesWB n σ ρ) v ∧
      (liesWB n σ ρ).slots = σ.slots :=
  Classical.choose_spec (rufLiesB_ok n σ ρ)

/-- The answer value of `lies` (chosen). -/
noncomputable def liesVB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    ErgVal gDB (gDB.erg (some GFn.lies)) :=
  Classical.choose (liesWB_spec n σ ρ)

theorem liesAtB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    rufAt gPB gOB 0 (n + 1) (some GFn.lies) σ ρ = .ok (liesWB n σ ρ) (liesVB n σ ρ) :=
  (Classical.choose_spec (liesWB_spec n σ ρ)).1

theorem liesWB_slots (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    (liesWB n σ ρ).slots = σ.slots :=
  (Classical.choose_spec (liesWB_spec n σ ρ)).2

/-- `einzahlen`'s body under `rufAt` handlers: it returns, with the slot
    `k.slots[i].stand` at `100`. -/
theorem einBodyB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.einzahlen))) :
    ∃ σ1, execEnd (V := vertragVon gDB (some GFn.einzahlen)) gOB 0
      (rufAt gPB gOB 0 (n + 1)) (gPB.rumpf (some GFn.einzahlen)) σ ρ =
      .zurueck σ1 () ∧ (σ1.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n = 100 := by
  show ∃ σ1, execEnd _ _ _ gbBody_einzahlen σ ρ = _ ∧ _
  simp only [gbBody_einzahlen, execEnd, execStmt, liesAtB]
  refine ⟨_, rfl, ?_⟩
  show ((liesWB n _ _).slots GTab.Konto _ GKontoFeld.stand).n = 100
  rw [liesWB_slots]
  exact (congrArg (fun z : Zahl 0 100 => z.n)
    (storeSlot_hit (D := gDB) _ GTab.Konto _ GKontoFeld.stand _)).trans rfl

/-- `einzahlen` on `gPB`, from ANY world and arguments, at depth `n + 2`:
    the call ends `ok` -- its `ensures old(stand) <= stand` and `lies`'s
    `ensures result == stand` both checked by `rufAt` on the way. -/
theorem rufEinB_ok (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.einzahlen))) :
    ∃ σ', rufAt gPB gOB 0 (n + 2) (some GFn.einzahlen) σ ρ = .ok σ' () := by
  obtain ⟨σ1, hb, h100⟩ := einBodyB n
    (σ.lese (Signatur.anfang gDB (gDB.signatur (some GFn.einzahlen)))
      (gPB.requires (some GFn.einzahlen)).orte) ρ
  refine ⟨_, rufAt_ok_of_gates gPB gOB 0 (n + 1) (some GFn.einzahlen) σ ρ _ rfl rfl _ ()
    hb _ rfl ?_ _ rfl rfl⟩
  show wahr? (decide (_ ≤ _)) = true
  apply decide_eq_true
  show _ ≤ (σ1.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n
  rw [h100]
  exact (Zahl.le_hi _)

/-- A cell of `Konto` under both layouts: the same C cell holds the
    encoded slot of both related worlds, so the slots agree. -/
theorem slots_gleich {σ : World G104_referenz.gD} {σB : World gDB} {st : CSt}
    (h : corrW gEL104 σ st) (hB : corrW gEBL σB st) (k : Int) (h0 : 0 ≤ k) (h1 : k < 2) :
    (σ.slots GTab.Konto k GKontoFeld.stand).n = (σB.slots GTab.Konto k GKontoFeld.stand).n := by
  have e := (h.1 GTab.Konto rfl).2 k GKontoFeld.stand h0 h1
  have eB := (hB.1 GTab.Konto rfl).2 k GKontoFeld.stand h0 h1
  have := e.symm.trans eB
  injection this

/-- **`gPB`'s `einzahlen` behaves as `gP`'s**: from worlds related to the
    same C state and arguments related to the same C locals, both Gabbro
    calls end `ok`, and their memories agree slot by slot -- through the
    emitted C, whose every run relates to both (`callAt_funktional`). -/
theorem gPB_wie_gP_einzahlen (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
    (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen))
    (ρB : Env gDB (gDB.params (some GFn.einzahlen))) (vs : List CVal) (ρ0 : CLok)
    (hw : corrW gEL104 σ st) (hwB : corrW gEBL σB st) (hb : bindParams cEin.params vs = some ρ0)
    (hr : EnvRel gEL104 kEinG ρG ρ0) (hrB : EnvRel gEBL kEinB ρB ρ0) :
    ∃ σ' σB', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
      rufAt gPB gOB 0 2 (some GFn.einzahlen) σB ρB = .ok σB' () ∧
      ∀ k : Int, 0 ≤ k → k < 2 →
        (σ'.slots GTab.Konto k GKontoFeld.stand).n = (σB'.slots GTab.Konto k GKontoFeld.stand).n := by
  obtain ⟨σ', hR⟩ := rufEin_ok 0 σ ρG
  obtain ⟨σB', hRB⟩ := rufEinB_ok 0 σB ρB
  obtain ⟨st1, rv1, hC1, hO1⟩ := einG_fn σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  obtain ⟨st2, rv2, hC2, hO2⟩ := einB_fn σB st ρB vs ρ0 hwB hb hrB (by rw [hRB]; rfl)
  rw [hR] at hO1
  rw [hRB] at hO2
  obtain ⟨e1, -⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional refCProg 2
    0 st vs st1 rv1 st2 rv2 hC1 hC2
  subst e1
  exact ⟨σ', σB', hR, hRB, fun k h0 h1 => slots_gleich hO1.1 hO2.1 k h0 h1⟩

/-- **`gPB`'s `lies` behaves as `gP`'s**: both calls end `ok` with the SAME
    answer and slot-equal memories. -/
theorem gPB_wie_gP_lies (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
    (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies))
    (ρB : Env gDB (gDB.params (some GFn.lies))) (vs : List CVal) (ρ0 : CLok)
    (hw : corrW gEL104 σ st) (hwB : corrW gEBL σB st) (hb : bindParams cLies.params vs = some ρ0)
    (hr : EnvRel gEL104 kLiesG ρG ρ0) (hrB : EnvRel gEBL kLiesB ρB ρ0) :
    ∃ σ' v σB' vB, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
      rufAt gPB gOB 0 1 (some GFn.lies) σB ρB = .ok σB' vB ∧
      (show Zahl 0 100 from v).n = (show Zahl 0 100 from vB).n ∧
      ∀ k : Int, 0 ≤ k → k < 2 →
        (σ'.slots GTab.Konto k GKontoFeld.stand).n = (σB'.slots GTab.Konto k GKontoFeld.stand).n := by
  obtain ⟨σ', v, hR, -⟩ := rufLies_ok 0 σ ρG
  obtain ⟨σB', vB, hRB, -⟩ := rufLiesB_ok 0 σB ρB
  obtain ⟨st1, rv1, hC1, hO1⟩ := liesG_fn σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  obtain ⟨st2, rv2, hC2, hO2⟩ := liesB_fn σB st ρB vs ρ0 hwB hb hrB (by rw [hRB]; rfl)
  rw [hR] at hO1
  rw [hRB] at hO2
  obtain ⟨e1, e2⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional refCProg 1
    1 st vs st1 rv1 st2 rv2 hC1 hC2
  subst e1
  subst e2
  obtain ⟨c1, hc1, hv1⟩ := hO1.2
  obtain ⟨c2, hc2, hv2⟩ := hO2.2
  rw [hc1] at hc2
  cases hc2
  have := hv1.symm.trans hv2
  injection this with hvv
  exact ⟨σ', v, σB', vB, hR, hRB, hvv, fun k h0 h1 => slots_gleich hO1.1 hO2.1 k h0 h1⟩

/-! ## 6. THE CLOSING THEOREM, stage (a) -/


end Gabbro.Grammatik
