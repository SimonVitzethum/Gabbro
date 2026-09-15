/-
  File:      Grammatik/CFormenRZeuge.lean
  Subject:   The witnesses of `CFormenR.lean` (rule 13): the reason
             channel end to end on `beispiele/74-syscall-schreiben.gab`.

  THE EMITTED C (the binary built from this tree on ki-pc-fisch-101,
  2026-09-13), the caller:

      static uint64_t schreibe(uint64_t fd, uint64_t buf, uint64_t len) {
          uint64_t n;
          {
              IoError e;
              if (!write(fd, buf, len, &n, &e)) {
                  switch (e) {
                  case IoError_BadFd: {
                      return 0;
                  } break;
                  case IoError_Interrupted: {
                      return 0;
                  } break;
                  case IoError_WouldBlock: {
                      return 0;
                  } break;
                  }
                  __builtin_unreachable();      (under `#if defined(__GNUC__)`)
              }
          }
          return n;
      }

  with `typedef enum { IoError_BadFd = 9, IoError_Interrupted = 4,
  IoError_WouldBlock = 11 } IoError;` and the prototype `static bool
  write(uint64_t fd, uint64_t buf, uint64_t len, uint64_t *_wert,
  IoError *_grund);`.

  THE CALLEE. `write` is a `syscall`: its emitted body is an inline-asm
  stub whose kernel is the named assumption `linux_write_contract`. The
  fixture gives the kernel a STAND-IN written in the emitter's channel
  forms (a reason for `fd == 0`, the length otherwise):

      static bool write(uint64_t fd, uint64_t buf, uint64_t len,
                        uint64_t *_wert, IoError *_grund) {
          if (fd == 0) { *_grund = IoError_BadFd; return false; }
          *_wert = len;
          return true;
      }

  so the callee half (`kcorr_retGrund`, `kcorr_ret`, `cCorr_rufK`) is
  exercised on the shapes the emitter writes for every `impl fn … or R`,
  and the caller half (`bsemG_bindCallElse`, `gcorr_onGrund`, the ghost
  read `return n;`, `cCorr_rufG`) on the real caller.

  THE MODEL SIDE. `d74`: no carrier, `write` (`true`) with twelve reason
  indices -- the ordinal convention: reason `r` is index `r`, so `BadFd`
  is 9, `Interrupted` 4, `WouldBlock` 11, and the other nine indices are
  arms that fail (a foreign call answering `never`, the hardware
  assumption); `schreibe` (`false`). C numbering: function 0 is `write`,
  1 is `schreibe`; in `schreibe` the locals are `fd = 0`, `buf = 1`,
  `len = 2`, `n = 4`, `e = 5` (address-taken), the call's answer `6`,
  the ghosts `7` (for `n`) and `8` (for `e`).
-/
import Grammatik.CFormenR

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

/-- `u64` -/
abbrev u64T : Ty := .int 0 18446744073709551615

def s74Write : Signatur Empty Empty Empty Empty where
  params := [u64T, u64T, u64T]
  erg := some u64T
  gruende := 12
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def s74Schreibe : Signatur Empty Empty Empty Empty where
  params := [u64T, u64T, u64T]
  erg := some u64T
  gruende := 0
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def d74 : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun e => nomatch e
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun e => nomatch e
  eigner := fun e => nomatch e
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => s74Write | _ => s74Schreibe
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Unit
  traeger := fun _ => []
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some .never
  aschreibt := fun _ e => nomatch e
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ _ h => by simp at h
  ggeteilt_bewacht := fun g => nomatch g

def fWrite : d74.Fn := show Bool from true
def fSchreibe : d74.Fn := show Bool from false

abbrev V74w : Vertrag d74 := vertragVon d74 fWrite
abbrev V74s : Vertrag d74 := vertragVon d74 fSchreibe

/-- The three parameters, `fd` first. -/
abbrev Γ74 : Ctx := [u64T, u64T, u64T]

def vFd : Var Γ74 u64T := .hier
def vBuf : Var Γ74 u64T := .dort .hier
def vLen : Var Γ74 u64T := .dort (.dort .hier)

/-! ## 2. The stand-in body of `write` -/

/-- `if fd == 0 { return BadFd; } return len;` -/
def rumpfWrite : Endblock d74 V74w false Γ74 [] :=
  .cons (Stmt.ite (Expr.eq (Expr.var vFd) (Expr.lit 0))
      (.cons (Stmt.retGrund ⟨9, by decide⟩ (List.Perm.refl _)) .nil) .nil)
    (.ret (.wert (Expr.var vLen)) (List.Perm.refl _))

/-! ## 3. The body of `schreibe` -/

/-- An arm that fails: a foreign call answering `never` (an index no
    reason has). -/
def armNie {Γ : Ctx} : Block d74 V74s false Γ [] [] :=
  .bindAxiom () .nil rfl (fun t => nomatch t) (fun g => nomatch g) (fun t => nomatch t)
    (fun g => nomatch g) .nil

/-- `{ return 0; }` -/
def armNull {Γ : Ctx} : Block d74 V74s false Γ [] [] :=
  .cons (Stmt.ret (.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0))) (List.Perm.refl _)) .nil

abbrev ΓE : Ctx := .grund 12 :: Γ74

/-- The twelve arms: indices 4, 9, 11 are the reasons, all `return 0;`. -/
def arms74 : GrundArms d74 V74s false ΓE [] [] 12 :=
  .cons armNie (.cons armNie (.cons armNie (.cons armNie (.cons armNull (.cons armNie
    (.cons armNie (.cons armNie (.cons armNie (.cons armNull (.cons armNie
    (.cons armNull .nil)))))))))))

/-- `else (e) { match e { … } }` -/
def err74 : Endblock d74 V74s false ΓE [] :=
  .cons (Stmt.onGrund (Expr.var .hier) arms74)
    (.ret (.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0))) (List.Perm.refl _))

/-- `return n;` -/
def rest74 : Block d74 V74s false (u64T :: Γ74) [] [] :=
  .cons (Stmt.ret (.wert (Expr.var .hier)) (List.Perm.refl _)) .nil

def args74 : Args d74 Γ74 [] (d74.params fWrite) :=
  .cons (Expr.var vFd) (.cons (Expr.var vBuf) (.cons (Expr.var vLen) .nil))

theorem hp74 : RufPasst d74 V74s (d74.signatur fWrite) [] where
  hw := fun t => nomatch t
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl _, List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- `let n = write(fd, buf, len) else (e) { … } return n;`, in a `breaking`
    block (the model's `Endblock` binds through no call: a block holds
    the binding, CFormenR.lean CUTS). -/
def block74 : Block d74 V74s false Γ74 [] [] :=
  .bindCallElse fWrite args74 rfl hp74 (by decide) err74 rest74

def rumpfSchreibe : Endblock d74 V74s false Γ74 [] :=
  .cons (Stmt.breaking () block74)
    (.ret (.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0))) (List.Perm.refl _))

def p74 : Programm d74 where
  invariante := fun _ => .wahr
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | true => rumpfWrite
    | false => rumpfSchreibe

def o74 : Orakel d74 where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-! ## 4. The C side -/

/-- `uint64_t` -/
def cU64 : CTy := .int false .w64
/-- `IoError` (an enum; its constants are `int`s, C11 6.7.2.2p3) -/
def cIo : CTy := .int true .w32

/-- The stack cells of `schreibe`'s frame (2): `n` (local 4) and `e`
    (local 5). No carrier, no global. -/
def lay74 : CLayout := fun b =>
  match b with
  | .stk 2 4 => some { lay := scalarRec cU64, kind := .plain, base := 0 }
  | .stk 2 5 => some { lay := scalarRec cIo, kind := .plain, base := 0 }
  | _ => none

def el74 : EmitLay d74 where
  lay := lay74
  tnr := fun t => nomatch t
  tnr_inj := fun t => nomatch t
  trec := fun t => nomatch t
  lay_tab := fun t => nomatch t
  trec_wf := fun t => nomatch t
  trec_count := fun t => nomatch t
  fnr := fun t => nomatch t
  fnr_lt := fun t => nomatch t
  fnr_inj := fun t => nomatch t
  fnr_fits := fun t => nomatch t
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- Without a carrier every state is related to every world. -/
theorem corr74 (σ : World d74) (st : CSt) : corrW el74 σ st :=
  ⟨fun t => (nomatch t), And.intro (fun g => (nomatch g)) (fun _ h => Bool.noConfusion h)⟩

/-- No device. -/
def orc74 : DevOrc := fun _ _ _ => 0

/-- `write`'s channel: `_wert` is local 3, `_grund` local 4, a reason's
    constant its index. -/
def κ74 (wp gp : CPtr) : Kanal := ⟨3, 4, wp, gp, cU64, cIo, fun r => (r : Int)⟩

/-- The stand-in body of `write`, in the emitter's channel forms. -/
def cWriteBody : CS :=
  .seq (.ite (.cmp .eq CIT.u64 (.var 0) (.lit 0))
      (.seq (.seq (.store (.var 4) cIo (.lit 9)) (.ret (some (cBoolTy, .lit 0)))) .skip) .skip)
    (.seq (.store (.var 3) cU64 (.var 2)) (.ret (some (cBoolTy, .lit 1))))

def cWrite : CFun :=
  { params := [(0, cU64), (1, cU64), (2, cU64), (3, .ptr), (4, .ptr)], locals := [],
    body := cWriteBody }

/-- The arm `{ return 0; }` and the `switch (e)` of `schreibe`. -/
def cArm : CS := .seq (.ret (some (cU64, .lit 0))) .skip

def cArms : List (Int × CS) := [(9, .seq cArm .brk), (4, .seq cArm .brk), (11, .seq cArm .brk)]

/-- The emitted body of `schreibe`: the call into `tmp = 6`, the `switch`
    on `e`'s cell, `__builtin_unreachable()` (stuck, `CX.trap`), and
    `return n;` from `n`'s cell. -/
def cSchreibeBody : CS :=
  callElseCS 0 [.var 0, .var 1, .var 2] 4 5 6
    (.seq (.sw (.ld (.addrL 5) cIo) cArms) (.expr .trap))
    (.seq (.ret (some (cU64, .ld (.addrL 4) cU64))) .skip)

def cSchreibe : CFun :=
  { params := [(0, cU64), (1, cU64), (2, cU64)], locals := [4, 5], body := cSchreibeBody }

def pr74 : CProg
  | 0 => some cWrite
  | 1 => some cSchreibe
  | _ => none

/-- No foreign call returns (the arms that fail have no C). -/
def xr74 : CCallR := fun _ _ _ _ _ => False

/-- The parameters in C locals 0 to 2. -/
def k74 : CEnvLay d74 Γ74 := ⟨[0, 1, 2], [], []⟩

/-! ## 5. The callee: `write`'s stand-in -/

/-- `write` runs in frame 1, calling nothing. -/
def xW74 : TVCtx d74 :=
  ⟨el74, orc74, 1, CallAt el74.lay orc74 xr74 pr74 0, xr74, o74, 0, rufAt p74 o74 0 0⟩

theorem write_end (wp gp : CPtr) (hsw : ∃ f' x', wp.blk = .stk f' x')
    (hsg : ∃ f' x', gp.blk = .stk f' x') :
    EndSemG xW74 0 true ⟨[], some (κ74 wp gp)⟩ k74 (p74.rumpf fWrite) cWrite.body := by
  obtain ⟨fw, xw, hw⟩ := hsw
  obtain ⟨fg, xg, hg⟩ := hsg
  have hc : ExprCorr xW74 k74 (.cmp .eq CIT.u64 (.var 0) (.lit 0))
      (Expr.eq (Λ := []) (Expr.var vFd) (Expr.lit 0)) :=
    ecorr_eq xW74 k74 CIT.u64 (ecorr_var xW74 k74 vFd) (ecorr_lit xW74 k74 0)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  have ht : BlockSemG xW74 0 ⟨[], some (κ74 wp gp)⟩ k74
      (Block.cons (Stmt.retGrund (V := V74w) (l := false) ⟨9, by decide⟩ (List.Perm.refl _)) .nil)
      (.seq (retGrundCS (κ74 wp gp) 9) .skip) :=
    cCorrG_block _ _ _ (BlockCorrG.cons
      (kcorr_retGrund xW74 0 _ k74 (κ74 wp gp) rfl ⟨9, by decide⟩ (List.Perm.refl _) rfl hg)
      BlockCorrG.nil)
  have he : BlockSemG xW74 0 ⟨[], some (κ74 wp gp)⟩ k74 (Block.nil (V := V74w) (l := false)
      (Γ := Γ74) (Λ := [])) .skip :=
    cCorrG_block _ _ _ BlockCorrG.nil
  have hE : ErgCorrK xW74 k74 cU64 (Λ := []) (e := some u64T) (ErgExpr.wert (Expr.var vLen))
      (some (CX.var 2)) := ⟨.var 2, rfl, ecorr_var xW74 k74 vLen, rfl⟩
  have hR : EndCorrG xW74 0 true ⟨[], some (κ74 wp gp)⟩ k74
      (Endblock.ret (V := V74w) (l := false) (ErgExpr.wert (Expr.var vLen)) (List.Perm.refl _))
      (retKCS (κ74 wp gp) [] (some (CX.var 2))) :=
    EndCorrG.retK (κ74 wp gp) rfl (List.Perm.refl _) hE hw
  have hI := gcorr_ite xW74 0 ⟨[], some (κ74 wp gp)⟩ k74 hc ht he
  exact cCorrG_end xW74 0 true _ (EndCorrG.cons hI hR)

/-- THE CALLEE RELATION of `write` (depth 1), from its body. -/
theorem write_fn : FnCorrK el74 (rufAt p74 o74 0 1) (CallAt el74.lay orc74 xr74 pr74 1) fWrite 0
    cWrite.params k74 3 4 cU64 cIo (fun r => (r : Int)) 1 :=
  cCorr_rufK el74 orc74 xr74 p74 o74 0 0 pr74 fWrite 0 cWrite rfl k74 rfl 0 3 4 cU64 cIo
    (fun r => (r : Int)) [] (fun _ hg => nomatch hg) (fun _ hq => nomatch hq) write_end

/-! ## 6. The caller: `schreibe` -/

/-- The ghosts: `7` is `n`'s cell (local 4), `8` is `e`'s cell (local 5). -/
def g74 : GCtx := ⟨[(7, 4, cU64), (8, 5, cIo)], none⟩

/-- `schreibe` runs in frame 2, `write` at depth 1. -/
def xS74 : TVCtx d74 :=
  ⟨el74, orc74, 2, CallAt el74.lay orc74 xr74 pr74 1, xr74, o74, 0, rufAt p74 o74 0 1⟩

theorem gsFind74_n : gsFind g74.gs 7 = some (4, cU64) := rfl
theorem gsFind74_e : gsFind g74.gs 8 = some (5, cIo) := rfl

theorem gOk74 : GOk xS74 g74 := by
  intro q hq
  simp only [g74, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨_, rfl, rfl, by decide⟩
  · exact ⟨_, rfl, rfl, by decide⟩

theorem inj74 : ∀ g e τ', gsFind g74.gs g = some (e, τ') → (e = 4 → g = 7) ∧ (e = 5 → g = 8) := by
  intro g e τ' h
  simp only [g74, gsFind] at h
  by_cases h7 : g = 7
  · rw [if_pos h7] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨fun _ => h7, fun h5 => by omega⟩
  · rw [if_neg h7] at h
    by_cases h8 : g = 8
    · rw [if_pos h8] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨fun h4 => by omega, fun _ => h8⟩
    · rw [if_neg h8] at h
      exact absurd h (by simp)

/-- The call keeps the frame: `write`'s stand-in calls nothing, so it
    changes no lifetime outside its own frame; the only ghost cells are
    the two it writes. -/
theorem keeps74 : CallKeeps xS74 g74 0 4 5 := by
  intro st vs st' rv h
  refine ⟨?_, ?_, fun κ hk => by simp [g74] at hk⟩
  · intro q hq h4 h5
    simp only [g74, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl h4
    · exact absurd rfl h5
  · intro q _
    exact callAt_live (n := 0) (rfl : pr74 0 = some cWrite) rfl h _ (fun x hx => by
      cases hx)

/-- The arguments of `write(fd, buf, len, &n, &e)`. -/
theorem args74_to : ArgsToK xS74 g74 k74 args74 [.var 0, .var 1, .var 2] 4 5 cWrite.params k74 3 4 := by
  intro σ st ρG ρC _ hrel
  cases ρG with
  | cons a ρ1 =>
      cases ρ1 with
      | cons b ρ2 =>
          cases ρ2 with
          | cons c ρ3 =>
              cases ρ3 with
              | nil =>
                  have h0 := hrel.1.1 _ vFd
                  have h1 := hrel.1.1 _ vBuf
                  have h2 := hrel.1.1 _ vLen
                  have e0 : ρC 0 = .int (show Zahl 0 18446744073709551615 from a).n := h0
                  have e1 : ρC 1 = .int (show Zahl 0 18446744073709551615 from b).n := h1
                  have e2 : ρC 2 = .int (show Zahl 0 18446744073709551615 from c).n := h2
                  have ra := (show Zahl 0 18446744073709551615 from a).lo_le
                  have ra' := (show Zahl 0 18446744073709551615 from a).le_hi
                  have rb := (show Zahl 0 18446744073709551615 from b).lo_le
                  have rb' := (show Zahl 0 18446744073709551615 from b).le_hi
                  have rc := (show Zahl 0 18446744073709551615 from c).lo_le
                  have rc' := (show Zahl 0 18446744073709551615 from c).le_hi
                  have cv : ∀ v : Int, 0 ≤ v → v ≤ 18446744073709551615 →
                      convV cU64 (.int v) = some (.int v) := fun v h1 h2 => by
                    show (match conv ⟨false, .w64⟩ v with | some b => some (CVal.int b) | none => none) = _
                    rw [conv_id ⟨by show (0 : Int) ≤ v; omega, by show v ≤ 18446744073709551615; omega⟩]
                  refine ⟨[.int (show Zahl 0 18446744073709551615 from a).n,
                    .int (show Zahl 0 18446744073709551615 from b).n,
                    .int (show Zahl 0 18446744073709551615 from c).n,
                    .ptr ⟨.stk 2 4, 0⟩, .ptr ⟨.stk 2 5, 0⟩], st,
                    lokUpd (lokUpd (lokUpd (lokUpd (lokUpd (fun _ => .undef) 4 (.ptr ⟨.stk 2 5, 0⟩)) 3
                      (.ptr ⟨.stk 2 4, 0⟩)) 2 (.int (show Zahl 0 18446744073709551615 from c).n)) 1
                      (.int (show Zahl 0 18446744073709551615 from b).n)) 0
                      (.int (show Zahl 0 18446744073709551615 from a).n), ?_, SameML.refl st, ?_, ?_,
                    rfl, rfl⟩
                  · simp only [List.cons_append, List.nil_append, evArgs, ev, e0, e1, e2]
                    rfl
                  · simp only [cWrite, bindParams, cv _ ra ra', cv _ rb rb', cv _ rc rc']
                    rfl
                  · refine ⟨fun τ x => ?_, fun _ hq => (nomatch hq), fun _ hq => (nomatch hq)⟩
                    cases x with
                    | hier => rfl
                    | dort y =>
                        cases y with
                        | hier => rfl
                        | dort z =>
                            cases z with
                            | hier => rfl
                            | dort w => exact nomatch w

/-- `ret` changes no memory: it keeps every cell. -/
theorem keeps_ret (X : TVCtx d74) (G : GCtx) {Γ : Ctx} (K : CEnvLay d74 Γ) (τ : CTy) (c : CX) :
    KeepsG X G K (.ret (some (τ, c))) := by
  intro σ st ρG ρC o _ _ hx
  cases hx with
  | retS he _ => exact keeps_sameML X G (ev_same _ _ _ _ _ _ _ _ he)

/-- `{ return 0; }` in the error block (the reason `e` a ghost). -/
theorem armNull_corr :
    BlockSemG xS74 0 g74 (k74.push (.grund 12) 8) (armNull (Γ := ΓE)) cArm := by
  have hE : ErgCorr xS74 (k74.push (.grund 12) 8) (Λ := []) (e := some u64T)
      (ErgExpr.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0))) (some (cU64, .lit 0)) :=
    ⟨cU64, .lit 0, rfl, ecorr_weiter _ _ _ _ (ecorr_lit _ _ 0), rfl⟩
  exact cCorrG_block _ _ _ (BlockCorrG.cons
    (liftG xS74 0 g74 _ (scorr_ret xS74 0 _ (V := V74s) (l := false) (List.Perm.refl _) hE)
      (fun _ _ => rfl) (fun κ hk => by simp [g74] at hk) (keeps_ret _ _ _ _ _)
      (fun h => absurd rfl h)) BlockCorrG.nil)

theorem arms74_nie : ∀ (i : Fin 12) (σ : World d74) (ρ : Env d74 ΓE),
    (execBlock o74 0 (rufAt p74 o74 0 1) (arms74.get i) σ ρ).istOk = false := by
  intro i σ ρ
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl
  | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl
  | ⟨11, _⟩ => rfl

theorem onGrund74_nie : ∀ (σ : World d74) (ρ : Env d74 ΓE),
    (execStmt xS74.O xS74.passes xS74.R (Stmt.onGrund (Expr.var .hier) arms74 (V := V74s)
      (Λ := []) (l := false)) σ ρ).istOk = false :=
  fun σ ρ => (congrArg Ausgang.istOk (execGrund_get _ _ _ arms74 _ _ _)).trans (arms74_nie _ _ _)

/-- The error block: `switch (e) { … } __builtin_unreachable();`. -/
theorem err74_corr : EndSemG xS74 0 false g74 (k74.push (.grund 12) 8) err74
    (.seq (.sw (.ld (.addrL 5) cIo) cArms) (.expr .trap)) := by
  have harms : ∀ i : Fin 12, (∃ c, cArms.lookup ((i : Nat) : Int) = some (.seq c .brk) ∧
      BlockSemG xS74 0 g74 (k74.push (.grund 12) 8) (arms74.get i) c) ∨
      (∀ σ ρ, (execBlock xS74.O xS74.passes xS74.R (arms74.get i) σ ρ).istFehler = true) := by
    intro i
    match i with
    | ⟨0, _⟩ => exact .inr fun _ _ => rfl
    | ⟨1, _⟩ => exact .inr fun _ _ => rfl
    | ⟨2, _⟩ => exact .inr fun _ _ => rfl
    | ⟨3, _⟩ => exact .inr fun _ _ => rfl
    | ⟨4, _⟩ => exact .inl ⟨cArm, rfl, armNull_corr⟩
    | ⟨5, _⟩ => exact .inr fun _ _ => rfl
    | ⟨6, _⟩ => exact .inr fun _ _ => rfl
    | ⟨7, _⟩ => exact .inr fun _ _ => rfl
    | ⟨8, _⟩ => exact .inr fun _ _ => rfl
    | ⟨9, _⟩ => exact .inl ⟨cArm, rfl, armNull_corr⟩
    | ⟨10, _⟩ => exact .inr fun _ _ => rfl
    | ⟨11, _⟩ => exact .inl ⟨cArm, rfl, armNull_corr⟩
  have hs := gcorr_onGrund xS74 0 g74 (k74.push (.grund 12) 8) (V := V74s) (l := false)
    (Λ := []) (Λ' := []) (arms := arms74) (carms := cArms)
    (ecorr_var xS74 (k74.push (.grund 12) 8) .hier) harms
  have hs' := gcorr_seqTot xS74 0 g74 _ (.expr .trap) hs onGrund74_nie
  exact cCorrG_end _ _ _ _ (EndCorrG.endet hs' onGrund74_nie)

/-- The rest: `return n;` from `n`'s cell. -/
theorem rest74_corr : BlockSemG xS74 0 g74 (k74.push u64T 7) rest74
    (.seq (.ret (some (cU64, .ld (.addrL 4) cU64))) .skip) := by
  have hE : ErgCorr xS74 (k74.push u64T 7) (Λ := []) (e := some u64T)
      (ErgExpr.wert (Expr.var .hier)) (some (cU64, .var 7)) :=
    ⟨cU64, .var 7, rfl, ecorr_var xS74 (k74.push u64T 7) .hier, rfl⟩
  exact cCorrG_block _ _ _ (BlockCorrG.cons
    (liftG_zs xS74 0 g74 _ (scorr_ret xS74 0 _ (V := V74s) (l := false) (List.Perm.refl _) hE) rfl
      (fun _ _ => rfl) (fun κ hk => by simp [g74] at hk) (keeps_ret _ _ _ _ _)
      (fun h => absurd rfl h)) BlockCorrG.nil)

/-- THE CALL SITE of `schreibe`, through `bsemG_bindCallElse`. -/
theorem block74_corr : BlockSemG xS74 0 g74 k74 block74 cSchreibeBody :=
  bsemG_bindCallElse xS74 0 g74 k74 fWrite args74 rfl hp74 (by decide) err74 rest74
    write_fn (by decide) args74_to gsFind74_n gsFind74_e gOk74 (fun _ => rfl) rfl rfl rfl rfl
    (fun κ hk => by simp [g74] at hk) keeps74 inj74 err74_corr rest74_corr

theorem block74_nie : ∀ (σ : World d74) (ρ : Env d74 Γ74),
    (execBlock o74 0 (rufAt p74 o74 0 1) block74 σ ρ).istOk = false := by
  intro σ ρ
  simp only [block74, execBlock]
  split
  · rfl
  · rename_i σ' r _
    simp only [err74, execEnd]
    split
    · rename_i heq
      have h2 := onGrund74_nie σ' (.cons r ρ)
      exact absurd ((congrArg Ausgang.istOk heq).symm.trans h2) (by simp [Ausgang.istOk])
    all_goals rfl
  · rfl
  · rfl

/-- THE BODY of `schreibe` against its emitted body. -/
theorem schreibe_end : EndSemG xS74 0 true g74 k74 (p74.rumpf fSchreibe) cSchreibe.body :=
  cCorrG_end xS74 0 true g74 (EndCorrG.endet (gcorr_breaking xS74 0 g74 k74 () block74_corr)
    (fun σ ρ => block74_nie σ ρ))

/-- THE CALLEE RELATION of `schreibe` (depth 2), through `cCorr_rufG`. -/
theorem schreibe_fn : FnCorr el74 (rufAt p74 o74 0 2) (CallAt el74.lay orc74 xr74 pr74 2) fSchreibe 1
    cSchreibe.params k74 :=
  cCorr_rufG el74 orc74 xr74 p74 o74 0 1 pr74 fSchreibe 1 cSchreibe rfl k74 rfl 0 g74.gs
    (by decide) (by decide) schreibe_end

/-! ## 7. The two runs, end to end -/

def w74 : World d74 := { slots := fun t => (nomatch t), globs := fun g => (nomatch g), spur := [] }

def st74 : CSt := { mem := fun _ _ => .undef, live := fun _ => true, obs := [] }

def z64 (n : Nat) (h : n ≤ 18446744073709551615 := by decide) : Zahl 0 18446744073709551615 :=
  ⟨n, by omega, by omega⟩

def rho74 (a b c : Nat) (ha : a ≤ 18446744073709551615 := by decide)
    (hb : b ≤ 18446744073709551615 := by decide) (hc : c ≤ 18446744073709551615 := by decide) :
    Env d74 (d74.params fSchreibe) :=
  .cons (z64 a ha) (.cons (z64 b hb) (.cons (z64 c hc) .nil))

theorem envRel74 (a b c : Nat) (ha : a ≤ 18446744073709551615) (hb : b ≤ 18446744073709551615)
    (hc : c ≤ 18446744073709551615) :
    EnvRel el74 k74 (rho74 a b c ha hb hc)
      (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int c)) 1 (.int b)) 0 (.int a)) := by
  refine ⟨fun τ x => ?_, fun _ hq => (nomatch hq), fun _ hq => (nomatch hq)⟩
  cases x with
  | hier => rfl
  | dort y =>
      cases y with
      | hier => rfl
      | dort z =>
          cases z with
          | hier => rfl
          | dort w => exact nomatch w

theorem bind74 (a b c : Nat) (ha : a ≤ 18446744073709551615) (hb : b ≤ 18446744073709551615)
    (hc : c ≤ 18446744073709551615) :
    bindParams cSchreibe.params [.int a, .int b, .int c] =
      some (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int c)) 1 (.int b)) 0 (.int a)) := by
  have cv : ∀ v : Nat, v ≤ 18446744073709551615 → convV cU64 (.int (v : Int)) = some (.int v) :=
    fun v h => by
      show (match conv ⟨false, .w64⟩ (v : Int) with | some b => some (CVal.int b) | none => none) = _
      rw [conv_id ⟨by show (0 : Int) ≤ v; omega, by show (v : Int) ≤ 18446744073709551615; omega⟩]
  simp only [cSchreibe, bindParams, cv a ha, cv b hb, cv c hc]

/-- WITNESS (rule 13), `schreibe` END TO END, both channels:
    `schreibe(3, 7, 5)` -- `write` answers `true` and `5` through `&n`,
    the C returns `n`'s cell -- and `schreibe(0, 7, 5)` -- `write`
    answers `false` and `BadFd` (9) through `&e`, the C `switch` takes
    `case 9` and returns `0`. The Gabbro calls return the same numbers,
    and the final states are related. -/
theorem schreibe_zeuge :
    (∃ (σ' : World d74) (st' : CSt),
      rufAt p74 o74 0 2 fSchreibe w74 (rho74 3 7 5) = .ok σ' (z64 5) ∧
      CallAt el74.lay orc74 xr74 pr74 2 1 st74 [.int 3, .int 7, .int 5] st' (some (.int 5)) ∧
      corrW el74 σ' st') ∧
    (∃ (σ' : World d74) (st' : CSt),
      rufAt p74 o74 0 2 fSchreibe w74 (rho74 0 7 5) = .ok σ' (z64 0) ∧
      CallAt el74.lay orc74 xr74 pr74 2 1 st74 [.int 0, .int 7, .int 5] st' (some (.int 0)) ∧
      corrW el74 σ' st') := by
  constructor
  · have hR : rufAt p74 o74 0 2 fSchreibe w74 (rho74 3 7 5) = .ok _ (z64 5) := rfl
    obtain ⟨st', rv, hC, hO⟩ := schreibe_fn w74 st74 (rho74 3 7 5) [.int 3, .int 7, .int 5] _
      (corr74 _ _) (bind74 3 7 5 (by decide) (by decide) (by decide))
      (envRel74 3 7 5 (by decide) (by decide) (by decide)) (by rw [hR]; rfl)
    rw [hR] at hO
    obtain ⟨hc, c, hrv, hvc⟩ := hO
    have hc1 : c = .int 5 := hvc
    subst hrv; subst hc1
    exact ⟨_, st', rfl, hC, hc⟩
  · have hR : rufAt p74 o74 0 2 fSchreibe w74 (rho74 0 7 5) = .ok _ (z64 0) := rfl
    obtain ⟨st', rv, hC, hO⟩ := schreibe_fn w74 st74 (rho74 0 7 5) [.int 0, .int 7, .int 5] _
      (corr74 _ _) (bind74 0 7 5 (by decide) (by decide) (by decide))
      (envRel74 0 7 5 (by decide) (by decide) (by decide)) (by rw [hR]; rfl)
    rw [hR] at hO
    obtain ⟨hc, c, hrv, hvc⟩ := hO
    have hc1 : c = .int 0 := hvc
    subst hrv; subst hc1
    exact ⟨_, st', rfl, hC, hc⟩

#print axioms write_fn
#print axioms block74_corr
#print axioms schreibe_end
#print axioms schreibe_fn
#print axioms schreibe_zeuge

end Gabbro.Grammatik
