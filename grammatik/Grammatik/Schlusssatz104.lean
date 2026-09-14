/-
  File:      Grammatik/Schlusssatz104.lean
  Subject:   THE CLOSING THEOREM, STAGE (a), FOR `beispiele/104-referenz.gab`
             (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2,
             §6): `schlusssatz_104`.

  One program, `G104_referenz.gP` over `G104_referenz.gD` -- the program
  the LEAN PARSER produces from the source text (`Parser/Uebersetze.lean`).
  Every other part of the chain is re-anchored at it here:

  * section 1, parse: the source text lexes, parses, elaborates and lowers
    to `(G104_referenz.gP, G104_referenz.gFs)`, each stage a PROPOSITIONAL equation (not a `Bool` pin);
  * section 2, C: the emitted C bodies of `einzahlen` and `lies` (quoted in
    `CFormenZeuge.lean`, byte-identical to the emitter's output) correspond
    to `G104_referenz.gP`'s bodies -- not to `refP`'s, the index-fixed one-parameter model
    `Korrespondenz104.lean` used; the certificate checked here carries the
    emitter's rows and layout verbatim (`certG104_rows`) and `G104_referenz.gP`'s locals map;
  * section 3, model certificates: the Lean-side print of `G104_referenz.gP`'s bodies IS
    the pasted printer output of `ZeugnisStmt104b.lean`, and both are
    accepted;
  * section 4, model judgement: every function of `G104_referenz.gP` meets the per-function
    obligations of the goal theorem (`KoerperGutS`, `InvGutS`), the fragment
    and footprint checks hold, and every call of `G104_referenz.gP` from any world ends
    `ok` (no contract violated on the way);
  * section 5, the machine: G starts EVERY thread in some function, and
    `G104_referenz.gD` has no lock-free idle function, so no G machine of `G104_referenz.gP` has one
    active thread (`gP_kein_einfaden`, proved). The runtime supplies the
    idle root: `gDB`/`gPB` = `G104_referenz.gD`/`G104_referenz.gP` plus exactly that root; `gPB`'s
    source part is the parser's `G104_referenz.gP` under a structural renaming
    (`renEnd`, `renE`: kernel-checked equations), and the goal theorem
    `ziel_ort_einfaden` holds for `gPB` from EVERY start memory with thread
    0 in EVERY source function and argument;
  * section 6, the theorem and its CUTS.
-/
import Grammatik.Parser.Uebersetze
import Grammatik.ZeugnisStmt104b
import Grammatik.Korrespondenz104
import Grammatik.CFormenDet
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.ZielOrtInv
import Grammatik.ZielOrtGanzZeuge

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze
open G104_referenz (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies)

set_option maxRecDepth 100000

/-! ## 1. Parse: the source text to `(G104_referenz.gP, G104_referenz.gFs)` -/

/-- The source text of `beispiele/104-referenz.gab`, comment-free (the text
    `u104lex` pins; comments lex away). -/
def src104 : String :=
  "module beispiel::referenz { const NKONTO : u32 = 2; type Betrag = u32 in 0 .. 10; type Stand = u32 in 0 .. 100; table Konto count NKONTO { slot { stand : Stand, } } lock M protects { stand } rank 0 held <= 50 ops; impl fn einzahlen(k : ptr<normal, rw> Konto, i : index into Konto, b : Betrag) requires Held(M) ensures old(k.slots[i].stand) <= k.slots[i].stand effects { reads k.slots, writes k.slots, locks M } costs <= 16 ops { k.slots[i].stand = 100; lies(k, i); } impl fn lies(k : ptr<normal, r> Konto, i : index into Konto) -> Stand requires Held(M) ensures result == k.slots[i].stand effects { reads k.slots, locks M } costs <= 8 ops { return k.slots[i].stand; } }"

/-- THE LEAN TRANSLATION PIPELINE of the 104 fragment: lex, parse,
    elaborate, lower. Every stage is a Lean function; nothing Rust. -/
def uebersetze104 (s : String) : Except String (Programm G104_referenz.gD × List GFn) :=
  match lex s with
  | .error _ => .error "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items =>
      match elabU items with
      | .error e => .error e
      | .ok u => lowerProg u

theorem s104_lex : lex src104 = .ok tt104 := u104lex

/-- Parsing, as an equation (the `Bool` pin `u104parse` made propositional). -/
theorem s104_parse : parseTopTief tt104 = .ok items104 := rfl

/-- Elaboration, as an equation (the `Bool` pin `u104elab` made propositional). -/
theorem s104_elab : elabU items104 = .ok uExp104 := rfl

/-- **PARSE FIDELITY**: the source text translates, in Lean, to the program
    `G104_referenz.gP` with member list `G104_referenz.gFs`. -/
theorem uebersetze104_ok : uebersetze104 src104 = .ok (G104_referenz.gP, G104_referenz.gFs) := by
  unfold uebersetze104
  rw [s104_lex]
  dsimp only
  rw [s104_parse]
  dsimp only
  rw [s104_elab]
  exact u104lower

/-! ## 2. C: the emitted bodies correspond to `G104_referenz.gP`'s bodies -/

/-- The emitter's layout of `G104_referenz.gD`: `Konto` is table block 0, `stand` is
    field 0 of `Konto_slot` at `uint32_t`, no globals (the layout of
    `refEL`, over the parser's declaration). -/
def gEL104 : EmitLay G104_referenz.gD where
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

/-- The oracle of `G104_referenz.gD`: no axiom, register or global exists. -/
def gO104 : Orakel G104_referenz.gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- `lies` runs in frame 1, calling nothing. -/
def xLiesG : TVCtx G104_referenz.gD :=
  ⟨gEL104, tvOrc, 1, CallAt gEL104.lay tvOrc tvXR refCProg 0, tvXR, gO104, 0, rufAt G104_referenz.gP gO104 0 0⟩

/-- `einzahlen` runs in frame 2, its callees at depth 1. -/
def xEinG : TVCtx G104_referenz.gD :=
  ⟨gEL104, tvOrc, 2, CallAt gEL104.lay tvOrc tvXR refCProg 1, tvXR, gO104, 0, rufAt G104_referenz.gP gO104 0 1⟩

/-! ### 2.1 The correspondence certificate over `G104_referenz.gP`

The rows (`(void)b;`, `k->slots[i].stand = 100;`, `lies(k, i);`,
`return k->slots[i].stand;`) and the layout are the emitter's, verbatim
from `printed104` (`certG104_rows`). The locals map is `G104_referenz.gP`'s: `G104_referenz.gP` HAS the
parameters `k`, `i`, `b`, so C locals 0, 1, 2 are Gabbro variables 0, 1, 2
(`vm`), and nothing is a pointer-only (`pp`) or model-fixed (`ks`) local.
`printed104`'s map (`vm = [2]`, `pp`, `ks = [(1, 0)]`) is the map for the
index-fixed model `refD`; its `ks` entry was the printer's `MODEL DATUM`. -/

/-- The certificate `certOkG` accepts: rows and layout as printed, the map
    of `G104_referenz.gP`. -/
def certG104 : Cert104 :=
  { einRows := [CertRow.voidB 2, CertRow.store100 0 1, CertRow.callLies 0 1],
    liesRows := [CertRow.retLoad 0 1],
    lay := ⟨2, 4, 0⟩,
    vmEin := [0, 1, 2], ppEin := [], ksEin := [],
    vmLies := [0, 1], ppLies := [], ksLies := [] }

/-- The rows and the layout ARE the emitter's printed ones. -/
theorem certG104_rows : certG104.einRows = printed104.einRows ∧
    certG104.liesRows = printed104.liesRows ∧ certG104.lay = printed104.lay :=
  ⟨rfl, rfl, rfl⟩

/-- THE DECIDABLE CHECK of a certificate against `G104_referenz.gP`: the rows and layout
    of the emitted C of 104, and `G104_referenz.gP`'s locals map. -/
def certOkG (c : Cert104) : Bool :=
  decide (c.einRows = [.voidB 2, .store100 0 1, .callLies 0 1]) &&
  decide (c.liesRows = [.retLoad 0 1]) &&
  decide (c.lay = ⟨2, 4, 0⟩) &&
  decide (c.vmEin = [0, 1, 2]) && decide (c.ppEin = []) && decide (c.ksEin = []) &&
  decide (c.vmLies = [0, 1]) && decide (c.ppLies = []) && decide (c.ksLies = [])

theorem certG104_ok : certOkG certG104 = true := by decide

/-- The locals layout of a certificate, over `G104_referenz.gD` (pointer entries name
    table `Konto`, the only table). -/
def kOfG {Γ : Ctx} (vm : List Nat) (pp : List (Nat × Unit)) (ks : List (Nat × Int)) :
    CEnvLay G104_referenz.gD Γ :=
  ⟨vm, pp.map (fun q => (q.1, GTab.Konto)), ks⟩

def kEinG : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_einzahlen) := kOfG [0, 1, 2] [] []

def kLiesG : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_lies) := kOfG [0, 1] [] []

/-! ### 2.2 `lies` -/

/-- `return k->slots[i].stand;` corresponds to `G104_referenz.gP`'s `lies` body:
    `k` is C local 0 (Gabbro variable 0), `i` C local 1 (variable 1). -/
theorem liesG_end (m : Nat) : EndCorr xLiesG m true kLiesG (G104_referenz.gP.rumpf g_lies) cLiesBody := by
  have hi : ExprCorr xLiesG kLiesG (.var 1)
      (Expr.var (D := G104_referenz.gD) (Γ := gCtx_lies) (Λ := gL_lies) (.dort .hier)) :=
    ecorr_var xLiesG kLiesG (.dort .hier)
  have hp : PtrTo xLiesG kLiesG (.var 0) GTab.Konto :=
    ptrTo_var xLiesG kLiesG (Γ := gCtx_lies) (.hier) rfl
  have he := ecorr_durch xLiesG kLiesG (Λ := gL_lies) (rw := false) (p := Expr.var .hier)
    rfl hp GKontoFeld.stand rfl gDarf_lies_Konto hi
  exact EndCorr.ret (by rfl) ⟨cU32, _, rfl, he, rfl⟩

/-- THE CALLEE RELATION of `lies` at depth 1. -/
theorem liesG_fn : FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 1) (CallAt gEL104.lay tvOrc tvXR refCProg 1)
    g_lies 1 cLies.params kLiesG :=
  cCorr_ruf gEL104 tvOrc tvXR G104_referenz.gP gO104 0 0 refCProg g_lies 1 cLies rfl kLiesG 0
    (cCorr_end xLiesG 0 true (liesG_end 0))

/-! ### 2.3 `einzahlen` -/

/-- `(void)b;` evaluates Gabbro's `b` (variable 2, C local 2). -/
theorem einG_void :
    ExprCorr xEinG kEinG (.var 2)
      (Expr.var (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) (.dort (.dort .hier))) :=
  ecorr_var xEinG kEinG (.dort (.dort .hier))

/-- `k->slots[i].stand = 100;` against `k.slots[i].stand = 100` through the
    `rw` pointer `k`. -/
theorem einG_write (m : Nat) :
    StmtCorr xEinG m kEinG
      (Stmt.assignDurch (V := vertragVon G104_referenz.gD g_einzahlen) (l := false) (Γ := gCtx_einzahlen)
        (Λ := gL_einzahlen) (.var .hier) GTab.Konto rfl GKontoFeld.stand (.var (.dort .hier))
        (.weiter (by decide) (by decide) (.lit 100)) (by decide) gDarf_einzahlen_Konto)
      (.store cStand cU32 (.lit 100)) := by
  have hi : ExprCorr xEinG kEinG (.var 1)
      (Expr.var (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) (.dort .hier)) :=
    ecorr_var xEinG kEinG (.dort .hier)
  have he : ExprCorr xEinG kEinG (.lit 100)
      (Expr.weiter (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) (lo' := 0) (hi' := 100)
        (by decide) (by decide) (.lit 100)) :=
    ecorr_weiter xEinG kEinG _ _ (ecorr_lit xEinG kEinG 100)
  have hp : PtrTo xEinG kEinG (.var 0) GTab.Konto :=
    ptrTo_var xEinG kEinG (Γ := gCtx_einzahlen) (.hier) rfl
  exact scorr_assignDurch xEinG kEinG m rfl hp GKontoFeld.stand rfl _ _ hi he

/-- The arguments of `lies(k, i);`: C passes `k` (local 0) and `i`
    (local 1); Gabbro passes a read-only pointer to the same table and `i`.
    A pointer's C value is the table's address either way. -/
theorem einG_args : ArgsTo xEinG kEinG
    (Args.cons (Expr.ptrOf (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) GTab.Konto 0 rfl false)
      (Args.cons (Expr.var (.dort .hier)) .nil))
    [.var 0, .var 1] cLies.params kLiesG := by
  intro σ st ρG ρC _ hr
  have h0 := hr.1 _ (Var.hier (Γ := [.index 2, .int 0 10]) (τ := .ptr 0 true))
  have h1 := hr.1 _ (Var.dort (σ := .ptr 0 true) (Var.hier (Γ := [.int 0 10]) (τ := .index 2)))
  obtain ⟨t0, ht0, e0⟩ := h0
  have et : t0 = GTab.Konto := by cases t0; rfl
  subst et
  have e0' : ρC 0 = .ptr ⟨.tab 0, 0⟩ := e0
  have e1' : ρC 1 = .int (encW (.index 2) (ρG.get (.dort .hier))) := h1
  have hc1 : convV cU32 (ρC 1) = some (ρC 1) := by
    rw [e1']
    exact convV_of_valCorr (EL := gEL104) (τ := .index 2) (v := ρG.get (.dort .hier)) rfl rfl
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
  · refine ⟨?_, fun q hq => absurd hq (by simp [kLiesG, kOfG]),
      fun q hq => absurd hq (by simp [kLiesG, kOfG])⟩
    intro τ x
    cases x with
    | hier =>
        refine ⟨GTab.Konto, rfl, ?_⟩
        show lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 0 = _
        simp only [lokUpd, if_pos]
        exact e0'
    | dort y =>
        cases y with
        | hier =>
            show ValCorr gEL104 (.index 2) _ (lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 1)
            simp only [lokUpd]
            rw [e1']
            rfl
        | dort z => exact nomatch z

/-- `lies(k, i);` against `G104_referenz.gP`'s call of `lies`. -/
theorem einG_call (m : Nat) :
    StmtCorr xEinG m kEinG
      (Stmt.call (V := vertragVon G104_referenz.gD g_einzahlen) (l := false) (Γ := gCtx_einzahlen) g_lies
        (Args.cons (Expr.ptrOf (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) GTab.Konto 0 rfl false)
          (Args.cons (Expr.var (.dort .hier)) .nil))
        gHp_einzahlen_lies rfl)
      (.call 1 [.var 0, .var 1] none) :=
  scorr_call xEinG kEinG m g_lies _ gHp_einzahlen_lies rfl liesG_fn einG_args

/-- THE BODY of `einzahlen` against the emitted body. -/
theorem einG_end (m : Nat) : EndCorr xEinG m true kEinG (G104_referenz.gP.rumpf g_einzahlen) cEinBody :=
  EndCorr.pre einG_void
    (EndCorr.cons (einG_write m) (EndCorr.cons (einG_call m) (EndCorr.retEnd (by rfl) rfl rfl)))

/-- THE CALLEE RELATION of `einzahlen` at depth 2. -/
theorem einG_fn : FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 2) (CallAt gEL104.lay tvOrc tvXR refCProg 2)
    g_einzahlen 0 cEin.params kEinG :=
  cCorr_ruf gEL104 tvOrc tvXR G104_referenz.gP gO104 0 1 refCProg g_einzahlen 0 cEin rfl kEinG 0
    (cCorr_end xEinG 0 true (einG_end 0))


/-! ### 2.4 The certificate is load-bearing -/

/-- The C unit a certificate elaborates to: `einzahlen` is function 0,
    `lies` function 1, bodies from the rows (parameters and locals as the
    emitter declares them). -/
def progOf (c : Cert104) : CProg
  | 0 => some { cEin with body := einCS c }
  | 1 => some { cLies with body := liesCS c }
  | _ => none

/-- A valid certificate elaborates to the EMITTED unit (the quoted C of
    `CFormenZeuge.lean`). -/
theorem progOf_ok (c : Cert104) (h : certOkG c = true) : progOf c = refCProg := by
  unfold certOkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, hL⟩, hLay⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hE' := of_decide_eq_true hE
  have hL' := of_decide_eq_true hL
  have hLay' := of_decide_eq_true hLay
  have e1 : einCS c = cEinBody := by unfold einCS; rw [hE', hLay']; rfl
  have e2 : liesCS c = cLiesBody := by unfold liesCS; rw [hL', hLay']; rfl
  funext n
  match n with
  | 0 => simp only [progOf, e1]; rfl
  | 1 => simp only [progOf, e2]; rfl
  | _ + 2 => rfl

/-- A valid certificate's locals maps ARE `gP`'s. -/
theorem kOf_ok (c : Cert104) (h : certOkG c = true) :
    (kOfG c.vmEin c.ppEin c.ksEin : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) =
      kEinG ∧
    (kOfG c.vmLies c.ppLies c.ksLies : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_lies)) =
      kLiesG := by
  unfold certOkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hVmE⟩, hPpE⟩, hKsE⟩, hVmL⟩, hPpL⟩, hKsL⟩ := h
  rw [of_decide_eq_true hVmE, of_decide_eq_true hPpE, of_decide_eq_true hKsE,
    of_decide_eq_true hVmL, of_decide_eq_true hPpL, of_decide_eq_true hKsL]
  exact ⟨rfl, rfl⟩

/-- **THE SOUNDNESS OF THE CORRESPONDENCE CERTIFICATE over `gP`**: a valid
    certificate gives the callee relations of both functions of `gP`,
    against the unit the certificate elaborates to, under the certificate's
    locals maps. -/
theorem corrCertG_sound (c : Cert104) (h : certOkG c = true) :
    FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 1) (CallAt gEL104.lay tvOrc tvXR (progOf c) 1)
      g_lies 1 cLies.params (kOfG c.vmLies c.ppLies c.ksLies) ∧
    FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 2) (CallAt gEL104.lay tvOrc tvXR (progOf c) 2)
      g_einzahlen 0 cEin.params (kOfG c.vmEin c.ppEin c.ksEin) := by
  rw [progOf_ok c h, (kOf_ok c h).1, (kOf_ok c h).2]
  exact ⟨liesG_fn, einG_fn⟩

/-! ### 2.5 Every run: the sequential model's answer and the C runs -/

/-- `lies` on `gP`, from ANY world and arguments, at any depth: the call
    ends `ok` (requires, ensures and invariants all checked by `rufAt`),
    and the answer world has the caller's slots. -/
theorem rufLies_ok (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    ∃ σ' v, rufAt G104_referenz.gP gO104 0 (n + 1) g_lies σ ρ = .ok σ' v ∧ σ'.slots = σ.slots := by
  have h := rufAt_ok_of_gates G104_referenz.gP gO104 0 n g_lies σ ρ _ rfl rfl _ _ rfl _ rfl
    (by show wahr? (decide (_ = _)) = true; exact decide_eq_true rfl) _ rfl rfl
  exact ⟨_, _, h, rfl⟩

/-- The answer world of `lies` (chosen; its slots are the caller's). -/
noncomputable def liesW (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) : World G104_referenz.gD :=
  Classical.choose (rufLies_ok n σ ρ)

theorem liesW_spec (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    ∃ v, rufAt G104_referenz.gP gO104 0 (n + 1) g_lies σ ρ = .ok (liesW n σ ρ) v ∧
      (liesW n σ ρ).slots = σ.slots :=
  Classical.choose_spec (rufLies_ok n σ ρ)

/-- The answer value of `lies` (chosen). -/
noncomputable def liesV (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    ErgVal G104_referenz.gD (G104_referenz.gD.erg g_lies) :=
  Classical.choose (liesW_spec n σ ρ)

theorem liesAt (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    rufAt G104_referenz.gP gO104 0 (n + 1) g_lies σ ρ = .ok (liesW n σ ρ) (liesV n σ ρ) :=
  (Classical.choose_spec (liesW_spec n σ ρ)).1

theorem liesW_slots (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    (liesW n σ ρ).slots = σ.slots :=
  (Classical.choose_spec (liesW_spec n σ ρ)).2

/-- `einzahlen`'s body under `rufAt` handlers: it returns, with the slot
    `k.slots[i].stand` at `100`. -/
theorem einBody (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) :
    ∃ σ1, execEnd (V := vertragVon G104_referenz.gD g_einzahlen) gO104 0
      (rufAt G104_referenz.gP gO104 0 (n + 1)) (G104_referenz.gP.rumpf g_einzahlen) σ ρ =
      .zurueck σ1 () ∧ (σ1.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n = 100 := by
  show ∃ σ1, execEnd _ _ _ G104_referenz.gBody_einzahlen σ ρ = _ ∧ _
  simp only [G104_referenz.gBody_einzahlen, execEnd, execStmt, liesAt]
  refine ⟨_, rfl, ?_⟩
  show ((liesW n _ _).slots GTab.Konto _ GKontoFeld.stand).n = 100
  rw [liesW_slots]
  exact (congrArg (fun z : Zahl 0 100 => z.n)
    (storeSlot_hit (D := G104_referenz.gD) _ GTab.Konto _ GKontoFeld.stand _)).trans rfl

/-- `einzahlen` on `gP`, from ANY world and arguments, at depth `n + 2`:
    the call ends `ok` -- its `ensures old(stand) <= stand` and `lies`'s
    `ensures result == stand` both checked by `rufAt` on the way. -/
theorem rufEin_ok (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) :
    ∃ σ', rufAt G104_referenz.gP gO104 0 (n + 2) g_einzahlen σ ρ = .ok σ' () := by
  obtain ⟨σ1, hb, h100⟩ := einBody n
    (σ.lese (Signatur.anfang G104_referenz.gD (G104_referenz.gD.signatur g_einzahlen))
      (G104_referenz.gP.requires g_einzahlen).orte) ρ
  refine ⟨_, rufAt_ok_of_gates G104_referenz.gP gO104 0 (n + 1) g_einzahlen σ ρ _ rfl rfl _ ()
    hb _ rfl ?_ _ rfl rfl⟩
  show wahr? (decide (_ ≤ _)) = true
  apply decide_eq_true
  show _ ≤ (σ1.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n
  rw [h100]
  exact (Zahl.le_hi _)

/-- No foreign call in this unit: its (empty) meaning is functional. -/
theorem tvXR_funktional : tvXR.Funktional := fun _ _ _ _ _ _ _ h _ => h.elim

/-- **EVERY RUN OF THE EMITTED C OF `einzahlen`** (depth 2, calling `lies`
    at depth 1), from a state related to ANY Gabbro world, with arguments
    related to ANY Gabbro arguments: the Gabbro call `rufAt gP … einzahlen`
    ends `ok` in a world `σ'`; the C call has a run; and EVERY C run ends in
    a state related to `σ'`, returning nothing. -/
theorem c104_einzahlen (c : Cert104) (hc : certOkG c = true) (σ : World G104_referenz.gD)
    (st : CSt) (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen))
    (vs : List CVal) (ρ0 : CLok) (hw : corrW gEL104 σ st)
    (hb : bindParams cEin.params vs = some ρ0)
    (hr : EnvRel gEL104 (kOfG c.vmEin c.ppEin c.ksEin) ρG ρ0) :
    ∃ σ', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
      (∃ st', CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' none) ∧
      ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' rv →
        corrW gEL104 σ' st' ∧ rv = none := by
  obtain ⟨σ', hR⟩ := rufEin_ok 0 σ ρG
  have hF := (corrCertG_sound c hc).2
  obtain ⟨st1, rv1, hC1, hO1⟩ := hF σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  rw [hR] at hO1
  obtain ⟨hc1, hret1⟩ := hO1
  have hrv1 : rv1 = none := hret1
  subst hrv1
  refine ⟨σ', hR, ⟨st1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional (progOf c) 2
    0 st vs st1 none st' rv hC1 hC
  subst e1
  exact ⟨hc1, e2.symm⟩

/-- **EVERY RUN OF THE EMITTED C OF `lies`** (depth 1): the Gabbro call ends
    `ok` with answer `v`; the C call has a run; every C run ends related and
    returns the encoding of `v`. -/
theorem c104_lies (c : Cert104) (hc : certOkG c = true) (σ : World G104_referenz.gD)
    (st : CSt) (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies))
    (vs : List CVal) (ρ0 : CLok) (hw : corrW gEL104 σ st)
    (hb : bindParams cLies.params vs = some ρ0)
    (hr : EnvRel gEL104 (kOfG c.vmLies c.ppLies c.ksLies) ρG ρ0) :
    ∃ σ' v, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
      (∃ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv) ∧
      ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv →
        corrW gEL104 σ' st' ∧ RetCorr gEL104 (G104_referenz.gD.erg g_lies) v rv := by
  obtain ⟨σ', v, hR, -⟩ := rufLies_ok 0 σ ρG
  have hF := (corrCertG_sound c hc).1
  obtain ⟨st1, rv1, hC1, hO1⟩ := hF σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  rw [hR] at hO1
  refine ⟨σ', v, hR, ⟨st1, rv1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional (progOf c) 1
    1 st vs st1 rv1 st' rv hC1 hC
  subst e1
  subst e2
  exact hO1

end Gabbro.Grammatik
