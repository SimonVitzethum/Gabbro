/-
  File:      Grammatik/CFormenZeuge.lean
  Subject:   The witnesses of T4 (rule 13): `refD`'s `einzahlen`, end to
             end, against the C that the emitter writes for
             `beispiele/104-referenz.gab`; one byte-view form and one
             atomic form instantiated (`CFormenH.lean` supplies those
             lemmas; this file's second half instantiates them).

  THE EMITTED C, as `target/debug/gabbro emit beispiele/104-referenz.gab`
  printed it on 2026-09-13 (binary of 2026-09-11 17:58), function bodies:

      static void einzahlen(Konto *restrict k, uint32_t i, uint32_t b) {
          (void)b;
          k->slots[i].stand = 100;
          lies(k, i);
      }

      static uint32_t lies(const Konto *restrict k, uint32_t i) {
          return k->slots[i].stand;
      }

  with `typedef struct { uint32_t stand; } Konto_slot;` and
  `typedef struct { Konto_slot slots[NKONTO]; } Konto;`, `NKONTO = 2`.

  THE MODEL SIDE. `refD` (ReferenzB.lean) is that program with the index
  fixed to `0` and the table named directly: `einzahlen` has the one
  parameter `b` (`.int 0 10`), writes `konto[0] := 100`, calls `lies`,
  returns; `lies` returns `konto[0]`. The C parameters the model does not
  carry are the certificate's data: `k` points to table `Konto` (`K.pp`),
  `i` holds `0` (`K.ks`). C numbering: function 0 is `einzahlen`,
  function 1 is `lies`; locals `k = 0`, `i = 1`, `b = 2`.
-/
import Grammatik.CFormenH

namespace Gabbro.Grammatik

/-! ## 1. The emitted C, as data -/

/-- `k->slots[i].stand` as an address: record `i` of 2, 4 bytes apart,
    field at offset 0 (`refEL_adressen`). -/
def cStand : CX := .slotA (.var 0) (.var 1) 2 4 0

/-- `uint32_t`. -/
def cU32 : CTy := .int false .w32

/-- `return k->slots[i].stand;` -/
def cLiesBody : CS := .ret (some (cU32, .ld cStand cU32))

/-- `(void)b; k->slots[i].stand = 100; lies(k, i);` -- and the end of the
    `void` body. -/
def cEinBody : CS :=
  .seq (.expr (.var 2)) (.seq (.store cStand cU32 (.lit 100)) (.seq (.call 1 [.var 0, .var 1] none) .skip))

def cLies : CFun := { params := [(0, .ptr), (1, cU32)], locals := [], body := cLiesBody }

def cEin : CFun := { params := [(0, .ptr), (1, cU32), (2, cU32)], locals := [], body := cEinBody }

/-- The unit: `einzahlen` is function 0, `lies` function 1. -/
def refCProg : CProg
  | 0 => some cEin
  | 1 => some cLies
  | _ => none

/-! ## 2. The locals layouts and the contexts -/

/-- `einzahlen`: Gabbro's `b` in C local 2; `k` (local 0) points to
    `Konto`; `i` (local 1) is `0`. -/
def kEin : CEnvLay refD (refD.params refEin) := ⟨[2], [(0, ())], [(1, 0)]⟩

/-- `lies`: no Gabbro parameter; `k` and `i` as above. -/
def kLies : CEnvLay refD (refD.params refLies) := ⟨[], [(0, ())], [(1, 0)]⟩

/-- No device, no foreign call in this unit. -/
def tvOrc : DevOrc := fun _ _ _ => 0
def tvXR : CCallR := fun _ _ _ _ _ => False

/-- The body of `lies` runs in frame 1, calling nothing. -/
def xLies : TVCtx refD :=
  ⟨refEL, tvOrc, 1, CallAt refEL.lay tvOrc tvXR refCProg 0, tvXR, refO, 0, rufAt refP refO 0 0⟩

/-- The body of `einzahlen` runs in frame 2, its callees at depth 1. -/
def xEin : TVCtx refD :=
  ⟨refEL, tvOrc, 2, CallAt refEL.lay tvOrc tvXR refCProg 1, tvXR, refO, 0, rufAt refP refO 0 1⟩

/-- A C local the certificate fixes corresponds to a Gabbro expression of
    that constant value (`i` against `refD`'s literal index `0`). -/
theorem ecorr_fest (X : TVCtx refD) {Γ : Ctx} {Λ : List (Res refD)} (K : CEnvLay refD Γ)
    {y : Nat} {v lo hi : Int} (hq : (y, v) ∈ K.ks) (e : Expr refD Γ Λ (.int lo hi))
    (hev : ∀ (σ : World refD) (ρG : Env refD Γ), (eval σ e σ ρG).n = v) :
    ExprCorr X K (.var y) e := by
  intro σ st ρG ρC _ hr
  have h := hr.2.2 _ hq
  refine ⟨.int v, st, ?_, ?_⟩
  · simp only [ev, h]
  · show CVal.int v = .int (eval σ e σ ρG).n
    rw [hev]

/-! ## 3. `lies`: its body, and the callee relation -/

theorem kLies_pp : ((0 : Nat), ()) ∈ kLies.pp := List.mem_singleton.mpr rfl
theorem kLies_ks : ((1 : Nat), (0 : Int)) ∈ kLies.ks := List.mem_singleton.mpr rfl
theorem kEin_pp : ((0 : Nat), ()) ∈ kEin.pp := List.mem_singleton.mpr rfl
theorem kEin_ks : ((1 : Nat), (0 : Int)) ∈ kEin.ks := List.mem_singleton.mpr rfl

/-- `return k->slots[i].stand;` corresponds to `lies`' body. -/
theorem lies_end (m : Nat) : EndCorr xLies m true kLies (refP.rumpf refLies) cLiesBody := by
  have hi : ExprCorr xLies kLies (.var 1) refIdxBodyLies :=
    ecorr_fest xLies kLies kLies_ks refIdxBodyLies (fun _ _ => rfl)
  have he := ecorr_slotParam xLies kLies kLies_pp () rfl refDarfBodyLies hi
  exact EndCorr.ret (by rfl) ⟨cU32, _, rfl, he, rfl⟩

/-- THE CALLEE RELATION of `lies` at depth 1, from its body. -/
theorem lies_fn : FnCorr refEL (rufAt refP refO 0 1) (CallAt refEL.lay tvOrc tvXR refCProg 1)
    refLies 1 cLies.params kLies :=
  cCorr_ruf refEL tvOrc tvXR refP refO 0 0 refCProg refLies 1 cLies rfl kLies 0
    (cCorr_end xLies 0 true (lies_end 0))

/-! ## 4. `einzahlen`: statement by statement -/

/-- `(void)b;` evaluates Gabbro's `b`. -/
theorem ein_void :
    ExprCorr xEin kEin (.var 2) (Expr.var (D := refD) (Λ := [Res.held (D := refD) ()]) .hier) :=
  ecorr_var xEin kEin .hier

/-- `k->slots[i].stand = 100;` against `konto[0] := 100`. -/
theorem ein_write (m : Nat) : StmtCorr xEin m kEin refWriteStAt (.store cStand cU32 (.lit 100)) := by
  have hi : ExprCorr xEin kEin (.var 1) refIdxEin :=
    ecorr_fest xEin kEin kEin_ks refIdxEin (fun _ _ => rfl)
  have he : ExprCorr xEin kEin (.lit 100) refHundert :=
    ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 100)
  exact scorr_assignSlotParam xEin kEin m kEin_pp () rfl _ _ hi he

theorem var_nil {τ : Ty} (x : Var [] τ) : False := nomatch x

/-- The arguments of `lies(k, i);` establish `lies`' locals relation. -/
theorem ein_args : ArgsTo xEin kEin refArgsLies [.var 0, .var 1] cLies.params kLies := by
  intro σ st ρG ρC _ hr
  have h0 : ρC 0 = .ptr ⟨.tab 0, 0⟩ := hr.2.1 _ kEin_pp
  have h1 : ρC 1 = .int 0 := hr.2.2 _ kEin_ks
  refine ⟨[.ptr ⟨.tab 0, 0⟩, .int 0], st,
    lokUpd (lokUpd (fun _ => .undef) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩), ?_, SameML.refl st, ?_, ?_⟩
  · simp only [evArgs, ev, h0, h1]
  · rfl
  · refine ⟨fun τ x => (var_nil x).elim, ?_, ?_⟩
    · intro q hq
      rw [List.mem_singleton.mp hq]
      rfl
    · intro q hq
      rw [List.mem_singleton.mp hq]
      rfl

/-- `lies(k, i);` against the call of `lies`. -/
theorem ein_call (m : Nat) :
    StmtCorr xEin m kEin (Stmt.call (V := vertragVon refD refEin) (l := false) refLies refArgsLies
      refHpLiesAt rfl) (.call 1 [.var 0, .var 1] none) :=
  scorr_call xEin kEin m refLies refArgsLies refHpLiesAt rfl lies_fn ein_args

/-- THE BODY of `einzahlen` against the emitted body, through
    `cCorr_end` (the terminal-block form of `cCorr_block`): `(void)b;` is
    a C-only statement, the write and the call correspond statement by
    statement, and the Gabbro `return` is the end of the `void` body. -/
theorem ein_end (m : Nat) : EndCorr xEin m true kEin (refP.rumpf refEin) cEinBody :=
  EndCorr.pre ein_void
    (EndCorr.cons (ein_write m) (EndCorr.cons (ein_call m) (EndCorr.retEnd (by rfl) rfl rfl)))

/-- The same two statements as a BLOCK, through `cCorr_block` itself. -/
theorem ein_block (m : Nat) :
    BlockSem xEin m kEin
      (Block.cons refWriteStAt (Block.cons (Stmt.call (V := vertragVon refD refEin) (l := false)
        refLies refArgsLies refHpLiesAt rfl) Block.nil))
      (.seq (.store cStand cU32 (.lit 100)) (.seq (.call 1 [.var 0, .var 1] none) .skip)) :=
  cCorr_block xEin m (BlockCorr.cons (ein_write m) (BlockCorr.cons (ein_call m) BlockCorr.nil))

/-- THE CALLEE RELATION of `einzahlen` at depth 2. -/
theorem ein_fn : FnCorr refEL (rufAt refP refO 0 2) (CallAt refEL.lay tvOrc tvXR refCProg 2)
    refEin 0 cEin.params kEin :=
  cCorr_ruf refEL tvOrc tvXR refP refO 0 1 refCProg refEin 0 cEin rfl kEin 0
    (cCorr_end xEin 0 true (ein_end 0))

/-! ## 5. The run, end to end -/

/-- The world at the call: `refSp0` (both slots `0`), empty trace. -/
def refW0 : World refD := refSp0.welt []

theorem refW0_corr : corrW refEL refW0 refSt0 := by
  refine ⟨?_, And.intro (fun g => nomatch g) (fun _ _ => rfl)⟩
  intro t _
  refine ⟨rfl, ?_⟩
  intro k f hk0 hk
  have hk2 : k < 2 := hk
  cases t
  cases f
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with e | e <;> subst e <;> rfl

/-- The C arguments of the call `einzahlen(k, 0, 7)`. -/
def einArgs : List CVal := [.ptr ⟨.tab 0, 0⟩, .int 0, .int 7]

theorem ein_bind : bindParams cEin.params einArgs =
    some (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩)) :=
  rfl

theorem ein_envRel : EnvRel refEL kEin refRho7
    (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ x
    cases x with
    | hier => rfl
    | dort y => exact nomatch y
  · intro q hq
    rw [List.mem_singleton.mp hq]
    rfl
  · intro q hq
    rw [List.mem_singleton.mp hq]
    rfl

/-- WITNESS (rule 13), `einzahlen` END TO END: the Gabbro call
    `einzahlen(7)` from `refSp0` and the emitted C `einzahlen(k, 0, 7)`
    from the zero state -- through `lies` at depth 1 -- both finish; the C
    call returns nothing; the final states are related; the slot moved
    from `0` to `100` on both sides; the observation trace is still empty. -/
theorem einzahlen_zeuge :
    ∃ (σ' : World refD) (st' : CSt),
      rufAt refP refO 0 2 refEin refW0 refRho7 = .ok σ' () ∧
      CallAt refEL.lay tvOrc tvXR refCProg 2 0 refSt0 einArgs st' none ∧
      corrW refEL σ' st' ∧
      (refW0.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧ st'.mem (.tab 0) 0 = .int 100 := by
  have hR : rufAt refP refO 0 2 refEin refW0 refRho7 = .ok _ () := rfl
  obtain ⟨st', rv, hC, hO⟩ := ein_fn refW0 refSt0 refRho7 einArgs _ refW0_corr ein_bind
    ein_envRel (by rw [hR]; rfl)
  rw [hR] at hO
  obtain ⟨hc, hret⟩ := hO
  have hrv : rv = none := hret
  subst hrv
  refine ⟨_, st', rfl, hC, hc, rfl, rfl, rfl, ?_⟩
  exact (hc.1 () rfl).2 0 () (by decide) (by decide)

/-! ## 6. A byte view and an atomic, instantiated

A second fixture, `bvD`: a byte carrier `Puffer` of 8 bytes (one field
`b : u8`, emitted as `uint8_t` records of one byte) and one `atomic`
global `A : u32 in 0 .. 100`. The C side: the carrier is table block 0
(`natLay 8 [uint8_t]`), `A` is global block 0 (`_Atomic uint32_t`), and a
byte view `V v = { .bytes = Puffer_speicher.slots, .len = 8 };` is the
stack local 0 of frame 1 (`natLay 1 [uint8_t *, uint32_t]`). -/

def bvD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 8
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 100
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Empty
  sig := fun f => nomatch f
  sigNr := fun _ =>
    { params := [], erg := none, gruende := 0, haelt := [], schreibt := fun _ => false,
      gschreibt := fun _ => true, konsumiert := [], produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ _ => Or.inr rfl

/-- The byte carrier's records: one `uint8_t`, one byte each. -/
def pufferLay : RecLay := natLay 8 [.int false .w8]

/-- The view struct `{ uint8_t *bytes; uint32_t len; }`. -/
def viewLay : RecLay := natLay 1 [.ptr, .int false .w32]

/-- The objects of the fixture: the carrier, the atomic, the view local. -/
def bvLay : CLayout := fun b =>
  match b with
  | .tab 0 => some { lay := pufferLay, kind := .plain, base := 0 }
  | .glob 0 => some { lay := scalarRec (.int false .w32), kind := .atomic, base := 0 }
  | .stk 1 0 => some { lay := viewLay, kind := .plain, base := 0 }
  | _ => none

theorem pufferLay_werte : pufferLay.ssize = 1 ∧ pufferLay.off 0 = 0 ∧ pufferLay.count = 8 ∧
    pufferLay.fty 0 = .int false .w8 ∧ viewLay.off 0 = 0 ∧ viewLay.ssize = 16 := by
  decide

def bvEL : EmitLay bvD where
  lay := bvLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => pufferLay
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun _ => rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun _ f f' _ => by cases f; cases f'; rfl
  fnr_fits := fun _ _ => rfl
  gnr := fun _ => 0
  gnr_inj := fun g g' _ => by cases g; cases g'; rfl
  gty := fun _ => .int false .w32
  lay_glob := fun _ => rfl
  gty_fits := fun _ => rfl

def bvO : Orakel bvD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => true

/-- Frame 1, no calls. -/
def xBv : TVCtx bvD := ⟨bvEL, tvOrc, 1, tvXR, tvXR, bvO, 0, fun f => nomatch f⟩

/-- The bytes `1, 2, 3, 4, 0, 0, 0, 0`. -/
def bvByte (k : Int) : Int := if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 3 else
  if k = 3 then 4 else 0

def bvByteZ (k : Int) : Zahl 0 255 :=
  ⟨bvByte k, by unfold bvByte; split <;> (try split) <;> (try split) <;> (try split) <;> decide,
    by unfold bvByte; split <;> (try split) <;> (try split) <;> (try split) <;> decide⟩

/-- The Gabbro world: the carrier holds the bytes, `A` holds `0`. -/
def bvW : World bvD :=
  { slots := fun _ k _ => bvByteZ k, globs := fun _ => ⟨0, by decide, by decide⟩, spur := [] }

/-- The C state: the carrier's cells, `A`'s cell, and the view's `bytes`
    cell pointing to the carrier; everything alive; no observation. -/
def bvSt : CSt where
  mem := fun b o => match b with
    | .tab 0 => .int (bvByte o)
    | .glob 0 => .int 0
    | .stk 1 0 => if o = 0 then .ptr ⟨.tab 0, 0⟩ else .int 8
    | _ => .undef
  live := fun _ => true
  obs := []

theorem bv_corr : corrW bvEL bvW bvSt := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · intro t _
    refine ⟨rfl, ?_⟩
    intro k f hk0 hk
    cases t
    cases f
    show CVal.int (bvByte (k.toNat * 1 + 0 : Nat)) = .int (bvByte k)
    congr 2
    omega
  · intro g _
    exact ⟨rfl, rfl⟩

/-- The carrier needs no guard. -/
theorem bvDarf : darf bvD () [] := fun _ h => nomatch h

/-- `(&v)->bytes`: the view's pointer, loaded from the view local. -/
def cViewBytes : CX := .ld (.fld (.addrL 0) 0) .ptr

theorem viewBytes_ev (ρ : CLok) :
    ev bvEL.lay tvOrc 1 cViewBytes bvSt ρ = some (.ptr ⟨.tab 0, 0⟩, bvSt) := by
  rfl

/-- WITNESS, byte view: `gabbro_le32(v->bytes + 0)` through the view local
    reads `0x04030201 = 67305985`, and it is the Gabbro reading
    `leseBytes Puffer.b 4 0` of the related world. -/
theorem bytesicht_zeuge (ρG : Env bvD []) (ρC : CLok) :
    ev bvEL.lay tvOrc 1 (le32 (.padd cViewBytes (.lit 0))) bvSt ρC =
      some (.int 67305985, bvSt) ∧
    (eval bvW (Expr.leseBytes (D := bvD) (Γ := []) (Λ := []) () () rfl 4 (Expr.lit ((0 : Nat) : Int))
      (Int.natCast_nonneg 0) (by decide) bvDarf) bvW ρG).n = 67305985 := by
  have h := le32_corr_at xBv (Γ := []) (Λ := []) () () rfl rfl rfl rfl rfl 0 (by decide)
    bvDarf bvW bvSt bv_corr ρG ρC cViewBytes (viewBytes_ev ρC)
  have hv : (eval bvW (Expr.leseBytes (D := bvD) (Γ := []) (Λ := []) () () rfl 4
      (Expr.lit ((0 : Nat) : Int)) (Int.natCast_nonneg 0) (by decide)
      bvDarf) bvW ρG).n = 67305985 := by
    rfl
  refine ⟨?_, hv⟩
  rw [← hv]
  exact h

/-- WITNESS, atomic: a strong compare-exchange on `A` expecting its value
    `0` succeeds and writes `42` (one observation carrying both orders),
    relating to Gabbro's write of `A`; a second one, still expecting `0`,
    fails, sees `42`, writes nothing (one observation), relation kept. -/
theorem atomar_zeuge :
    ∃ st1, aCas bvEL.lay bvSt (bvEL.globPtr ()) (.int false .w32) .acqRel .acquire 0 42 =
        some (true, 0, st1) ∧
      corrW bvEL (bvW.schreibGlob () [] ⟨42, by decide, by decide⟩) st1 ∧
      st1.obs = [.acas ⟨.glob 0, 0⟩ .acqRel .acquire 0 42 true] ∧
      st1.mem (.glob 0) 0 = .int 42 ∧
      aCas bvEL.lay st1 (bvEL.globPtr ()) (.int false .w32) .acqRel .acquire 0 42 =
        some (false, 42, CSt.mk st1.mem st1.live
          (.acas ⟨.glob 0, 0⟩ .acqRel .acquire 42 42 false :: st1.obs)) := by
  obtain ⟨st1, h1, hc1, ho1⟩ := cas_success bvEL bvW bvSt bv_corr () rfl rfl []
    ⟨42, by decide, by decide⟩ .acqRel .acquire rfl
  have hm : st1.mem (.glob 0) 0 = .int 42 := (hc1.2.1 () rfl).2
  obtain ⟨h2, -⟩ := cas_failure bvEL (bvW.schreibGlob () [] ⟨42, by decide, by decide⟩) st1 hc1 ()
    rfl rfl 0 ⟨42, by decide, by decide⟩ .acqRel .acquire rfl (by decide)
  exact ⟨st1, h1, hc1, ho1, hm, h2⟩

#print axioms lies_fn
#print axioms ein_end
#print axioms ein_block
#print axioms ein_fn
#print axioms einzahlen_zeuge
#print axioms bytesicht_zeuge
#print axioms atomar_zeuge

end Gabbro.Grammatik
