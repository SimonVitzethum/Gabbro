/- Part 6 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T5

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 11. TARGET A: the machine realises the sequential result -/

/-- **TARGET A -- adequacy of the call machine G for call-free bodies.**
    Thread `f` of `M` runs a frame of `fn` (actual parameters `rho`, entry
    world `s0`) above a caller frame that does not wait for a bound value
    (`hnw`: the verbatim pop demands it since 2026-09-13), with residue
    `.ende b` for a covered (call-free, `EndG`) end block `b` at environment
    `ρ`; its static holdings `Λ` name exactly the locks its trace holds; no
    other thread holds a lock `b` may take (`A`). If the sequential semantics, started at
    the thread's current world `M.weltVon f`, returns `v` in world `σ'`,
    then steps of thread `f` alone reach a machine `M'` that has popped the
    frame, logged `rueck fn rho v s0 σ'` with THE SAME value `v`, and whose
    shared memory is `σ'.speicher`.

    How the machine's read world relates: the `rueck` step reads the result
    at `s1 = (M'.weltVon f).lese Λ e.orte` (`e` the returned expression)
    and logs `s1`; `execEnd`'s `ret` returns `σ.lese Λ e.orte`. The theorem
    shows these are EQUAL: the logged `s1` IS `σ'` -- trace included --
    and the new memory is `s1.speicher = σ'.speicher`. Other threads are
    untouched. -/
theorem rufG_adaequat (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndG A b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes keinRuf b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ M', RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  have hsp : (M.weltVon f).spur = spur := by
    show (M.faeden f).spur = spur
    rw [hM]
  have hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende b) (M.weltVon f) :=
    ⟨by rw [hsp]; exact hM, rfl⟩
  obtain ⟨M', hl, hG⟩ := endRet P O passes f fn caller rst rho s0 log A hnw b hb
    (M.weltVon f) σ' ρ v hexec M hZ (by rw [hsp]; exact hΛ) hfrei
  exact ⟨M', hl, hG.1, hG.2, rufLaufG_fremd hl⟩

/-! ### The covered fragment is call-free in the sense of `HoareRegeln.lean`

    `EndG` refines `EndOhneRuf`: every covered body is a body the Hoare
    rules' call-freedom predicate accepts, so the sequential side of
    TARGET A is `R`-independent (`endOhneRuf_Runabhaengig`). -/

theorem blattG_ohneRuf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) : StmtOhneRuf s := by
  cases h <;> constructor

mutual

theorem stmtG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    StmtG A mr s → StmtOhneRuf s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ => blattG_ohneRuf (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattG_ohneRuf (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ => blattG_ohneRuf (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattG_ohneRuf (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ => blattG_ohneRuf (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattG_ohneRuf (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ => blattG_ohneRuf (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattG_ohneRuf (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattG_ohneRuf (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ => blattG_ohneRuf (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ => blattG_ohneRuf (.retires m s h a)
  | _, _, _, _, _, .ite _ t e, hs =>
      .ite _ _ _ (blockG_ohneRuf t hs.ite_inv.1) (blockG_ohneRuf e hs.ite_inv.2)
  | _, _, _, _, _, .onOption _ p a, hs =>
      .onOption _ _ _ (blockG_ohneRuf p hs.onOption_inv.1) (blockG_ohneRuf a hs.onOption_inv.2)
  | _, _, _, _, _, .onTag _ arms, hs => .onTag _ _ (armsG_ohneRuf arms hs.onTag_inv)
  | _, _, _, _, _, .onWhy _ arms, hs => .onWhy _ _ (grundG_ohneRuf arms hs.onGrund_inv)
  | _, _, _, _, _, .call .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .locks _ _ body, hs => .locks _ _ _ (blockG_ohneRuf body hs.locks_inv.2)
  | _, _, _, _, _, .breaking _ body, hs => .breaking _ _ (blockG_ohneRuf body hs.breaking_inv)
  | _, _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .ret e hΛ, _ => .ret e hΛ
  | _, _, _, _, _, .retWhy .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    BlockG A mr b → BlockOhneRuf b
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons s rest, hb =>
      .cons _ _ (stmtG_ohneRuf s hb.cons_inv.1) (blockG_ohneRuf rest hb.cons_inv.2)
  | _, _, _, _, _, .bind _ rest, hb => .bind _ _ (blockG_ohneRuf rest hb.bind_inv)
  | _, _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .regRead _ _ rest, hb => .regRead _ _ _ (blockG_ohneRuf rest hb.regLies_inv)
  | _, _, _, _, _, .regReadElse _ _ _ sonst rest, hb =>
      .regReadElse _ _ _ _ _ (endG_ohneRuf sonst hb.regLiesElse_inv.2.2.1)
        (blockG_ohneRuf rest hb.regLiesElse_inv.2.1)
  | _, _, _, _, _, .awaits _ _ _ _ rest, hb =>
      .awaits _ _ _ _ _ (blockG_ohneRuf rest hb.awaits_inv)
  | _, _, _, _, _, .exchange _ _ _ _ rest, hb =>
      .exchange _ _ _ _ _ (blockG_ohneRuf rest hb.exchange_inv)
  | _, _, _, _, _, .narrow _ _ _ sonst rest, hb =>
      .narrow _ _ _ _ _ (endG_ohneRuf sonst hb.narrow_inv.2.2.1)
        (blockG_ohneRuf rest hb.narrow_inv.2.1)
  | _, _, _, _, _, .check _ sonst rest, hb =>
      .check _ _ _ (endG_ohneRuf sonst hb.pruefung_inv.2.2.1)
        (blockG_ohneRuf rest hb.pruefung_inv.2.1)
  | _, _, _, _, _, .float _ _ _ _ _ rest, hb =>
      .float _ _ _ _ _ _ (blockG_ohneRuf rest hb.gleit_inv)
  | _, _, _, _, _, .floatLit _ _ _ rest, hb =>
      .floatLit _ _ _ _ (blockG_ohneRuf rest hb.gleitLit_inv)
  | _, _, _, _, _, .floatOf _ _ _ rest, hb =>
      .floatOf _ _ _ _ (blockG_ohneRuf rest hb.gleitVon_inv)
  | _, _, _, _, _, .floatNarrow _ _ _ sonst rest, hb =>
      .floatNarrow _ _ _ _ _ (endG_ohneRuf sonst hb.gleitNarrow_inv.2.2.1)
        (blockG_ohneRuf rest hb.gleitNarrow_inv.2.1)

theorem endG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    EndG A e → EndOhneRuf e
  | _, _, _, .ret e hΛ, _ => .ret e hΛ
  | _, _, _, .retWhy .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he =>
      .cons _ _ (stmtG_ohneRuf s he.cons_inv.1) (endG_ohneRuf rest he.cons_inv.2.1)
  | _, _, _, .bind _ rest, he => .bind _ _ (endG_ohneRuf rest he.bind_inv)

theorem armsG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs), ArmsG A mr arms → ArmsOhneRuf arms
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .cons b rest, ha =>
      .cons _ _ (blockG_ohneRuf b ha.cons_inv.1) (armsG_ohneRuf rest ha.cons_inv.2)

theorem grundG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A mr arms → GrundArmsOhneRuf arms
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .cons b rest, ha =>
      .cons _ _ (blockG_ohneRuf b ha.cons_inv.1) (grundG_ohneRuf rest ha.cons_inv.2)

end
/-- **TARGET A for any call handler.** A covered body is call-free, so the
    sequential run under ANY handler `R` (e.g. `rufAt P O passes fuel`, the
    one the program semantics and the Hoare rules use) is the run under
    `keinRuf`; `rufG_adaequat` applies verbatim. -/
theorem rufG_adaequat_R (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndG A b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes R b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ M', RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  rw [endOhneRuf_Runabhaengig O passes R keinRuf b (endG_ohneRuf b hb)] at hexec
  exact rufG_adaequat P O passes M f fn rho s0 caller rst spur log ρ b A hb hM hnw hΛ hfrei σ' v hexec

/-! ## 12. Witness: a `locks` block around an `if` whose taken branch writes

    `adD` has one table `konto` (2 slots, one `.int 0 100` field) guarded by
    one lock (`braucht`), and two functions over `Bool`: `true` (no
    parameters, returns `.int 0 100`, holds NO lock at entry, may write the
    table) and `false` (the caller, returns nothing). The body of `true` is

        locks m { if true { konto[0] := 5 } else { } }; return 7

    The frame of `true` runs above a caller frame; every thread's trace is
    empty, so no other thread holds `m`. -/

def adSigA : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def adSigB : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def adD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => adSigA | _ => adSigB
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The witness function (`true`) and the caller (`false`). -/
def adFn : adD.Fn := show adD.Fn from true

def adCallerFn : adD.Fn := show adD.Fn from false

/-- The holdings inside the `locks` body. -/
def adΛL : List (Res adD) := [Res.held (D := adD) ()]

theorem adDarf : darf adD () adΛL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

def adIdx : Expr adD [] adΛL (.index (adD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

def adFuenf : Expr adD [] adΛL (adD.typ () ()) :=
  .widen (by decide) (by decide) (.lit 5)

/-- `konto[0] := 5`. -/
def adWrite : Stmt adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .assignSlot () () adIdx adFuenf rfl adDarf

/-- The taken branch: the write. -/
def adThen : Block adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .cons adWrite .nil

/-- `if true { konto[0] := 5 } else { }`. -/
def adIte : Stmt adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .ite .tru adThen .nil

def adBody : Block adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .cons adIte .nil

/-- `locks m { … }`: nothing is held before, so the rank side is empty. -/
def adLocks : Stmt adD (vertragVon adD adFn) false [] [] [] :=
  .locks () (fun _ h => absurd h List.not_mem_nil) adBody

def adSieben : Expr adD [] [] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 7)

/-- The body: `locks m { if true { konto[0] := 5 } else { } }; return 7`. -/
def adRumpf : Endblock adD (vertragVon adD adFn) false [] [] :=
  .cons adLocks (.ret (.val adSieben) List.Perm.nil)

def adCallerRumpf : Endblock adD (vertragVon adD adCallerFn) false [] [] :=
  .ret .empty List.Perm.nil

def adP : Programm adD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => adRumpf
    | false => adCallerRumpf

def adO : Orakel adD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- Start memory: every slot reads `0`. -/
def adSp0 : Speicher adD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- The suspended caller frame. -/
def adCaller : RufRahmenG adD :=
  ⟨adCallerFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adCallerRumpf⟩⟩

/-- Every thread: the witness frame above the caller, empty trace, empty log. -/
def adFaden : RufFadenG adD :=
  ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adRumpf⟩⟩,
    [], []⟩

def adM : RufMaschineG adD := ⟨adSp0, fun _ => adFaden, [], adSp0.welt []⟩

/-- The body is in the covered fragment, with the one lock admitted. -/
theorem adRumpf_G : EndG (fun L : adD.Lock => L = ()) adRumpf :=
  EndG.cons _ _
    (StmtG.locks (A := fun L : adD.Lock => L = ()) () _ adBody rfl
      (BlockG.cons _ _
        (StmtG.ite _ _ _
          (BlockG.cons _ _ (StmtG.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockG.nil)
          BlockG.nil)
        BlockG.nil))
    (EndG.ret _ _)

/-- No thread of `adM` holds any lock. -/
theorem adM_frei : ∀ L : adD.Lock, L = () → RufFreiG adM 0 L := by
  intro L _ g _ hm
  simp [adM, adFaden, offen] at hm

/-- The frame's holdings are exactly the (empty) held locks. -/
theorem adM_held : HeldGenau ([] : List (Res adD)) (offen ([] : List (Ereignis adD))) := by
  intro L
  simp [offen]

/-- The sequential run of the body: a normal return with the written slot. -/
theorem adRumpf_exec : ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
    execEnd adO 0 keinRuf adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (show Zahl 0 100 from v).n = 7 :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat`.** Every premise is instantiated jointly
    on the non-degenerate program above: the body takes a lock (`locks`)
    and, inside, runs an `if` whose taken branch WRITES the table. The
    sequential semantics returns `7` in a world where slot 0 moved `0 -> 5`;
    the machine, by steps of thread 0 alone, pops the frame logging that
    same `7` and that same world, and its memory holds the moved slot. -/
theorem rufG_adaequat_zeuge :
    ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
      execEnd adO 0 keinRuf adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ ((adM.weltVon 0).slots () 0 ()).n = 0 ∧
      (show Zahl 0 100 from v).n = 7 ∧
      ∃ M', RufLaufG adP adO 0 0 adM M' ∧
        M'.faeden 0 = ⟨[], adCaller, σ'.spur,
          [RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) σ']⟩ ∧
        M'.speicher = σ'.speicher ∧ (M'.speicher.slots () 0 ()).n = 5 ∧
        (∀ g, g ≠ 0 → M'.faeden g = adM.faeden g) := by
  obtain ⟨σ', v, hex, h5, h7⟩ := adRumpf_exec
  obtain ⟨M', hl, hf, hsp, hfr⟩ := rufG_adaequat adP adO 0 adM 0 adFn Env.nil
    (adSp0.welt []) adCaller [] [] [] Env.nil adRumpf (fun L : adD.Lock => L = ())
    adRumpf_G rfl rfl adM_held adM_frei σ' v hex
  refine ⟨σ', v, hex, h5, rfl, h7, M', hl, hf, hsp, ?_, hfr⟩
  rw [hsp]
  exact h5

/-- **Witness for `rufG_adaequat_R`.** Every premise jointly, on the same
    program, with the handler the PROGRAM semantics uses, `rufAt adP adO 0 1`
    (the body is call-free, so its run does not consult it): the sequential
    run returns `7` with slot 0 moved `0 -> 5`, and the machine pops the
    frame (its caller does not wait: `hnw` by `rfl`) logging that value
    and that world, its memory holding the moved slot. -/
theorem rufG_adaequat_R_zeuge :
    ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
      execEnd adO 0 (rufAt adP adO 0 1) adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (show Zahl 0 100 from v).n = 7 ∧
      ∃ M', RufLaufG adP adO 0 0 adM M' ∧
        M'.faeden 0 = ⟨[], adCaller, σ'.spur,
          [RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) σ']⟩ ∧
        (M'.speicher.slots () 0 ()).n = 5 := by
  have hex : ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
      execEnd adO 0 (rufAt adP adO 0 1) adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (show Zahl 0 100 from v).n = 7 := ⟨_, _, rfl, rfl, rfl⟩
  obtain ⟨σ', v, hex, h5, h7⟩ := hex
  obtain ⟨M', hl, hf, hsp, _⟩ := rufG_adaequat_R adP adO 0 (rufAt adP adO 0 1) adM 0 adFn Env.nil
    (adSp0.welt []) adCaller [] [] [] Env.nil adRumpf (fun L : adD.Lock => L = ())
    adRumpf_G rfl rfl adM_held adM_frei σ' v hex
  refine ⟨σ', v, hex, h5, h7, M', hl, hf, ?_⟩
  rw [hsp]
  exact h5

/-! ## 13. Toward TARGET B: forms that never consult the oracle

    The converse was written to survive the machine's bare `nimmt`/`gibt`
    steps (removed from G on 2026-09-13; the statements below hold a
    fortiori): they changed only the thread's trace. The sequential
    semantics depends on the trace only through the oracle (`regLies`,
    `regLiesElse`, `awaits` hand the whole world to `O`), so the converse
    is stated for bodies without those forms. -/

mutual

/-- The statement never hands the world to the oracle. -/
def Stmt.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ohneOrakel && e.ohneOrakel
  | .onOption _ p a => p.ohneOrakel && a.ohneOrakel
  | .onTag _ arms => arms.ohneOrakel
  | .onWhy _ arms => arms.ohneOrakel
  | .locks _ _ body => body.ohneOrakel
  | .breaking _ body => body.ohneOrakel
  | .traverse _ _ body => body.ohneOrakel
  | .retry _ _ body u => body.ohneOrakel && u.ohneOrakel
  | .forever _ _ body => body.ohneOrakel
  | .axiomCall .. => false
  | _ => true

def Block.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ohneOrakel && rest.ohneOrakel
  | .bind _ rest => rest.ohneOrakel
  | .bindCall _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallInd _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallElse _ _ _ _ _ err rest => err.ohneOrakel && rest.ohneOrakel
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.ohneOrakel
  | .narrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .check _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .float _ _ _ _ _ rest => rest.ohneOrakel
  | .floatLit _ _ _ rest => rest.ohneOrakel
  | .floatOf _ _ _ rest => rest.ohneOrakel
  | .floatNarrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel

def Endblock.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.ohneOrakel && rest.ohneOrakel
  | .bind _ rest => rest.ohneOrakel
  | .bindCall _ _ _ _ _ rest => rest.ohneOrakel
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false

def Arms.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ohneOrakel && rest.ohneOrakel

def GrundArms.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ohneOrakel && rest.ohneOrakel

end
/-- `armWahlG` selects an oracle-free arm of oracle-free arms. -/
theorem armWahlG_ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.ohneOrakel = true → (armWahlG arms v).2.1.ohneOrakel = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at h
      exact armWahlG_ohneOrakel rest _ h.2


end Gabbro.Grammatik
