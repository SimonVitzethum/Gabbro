module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T6.Teil1Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T6.Teil1Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T5

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  simp only [adM, adFaden, offen, List.not_mem_nil] at hm

/-- The frame's holdings are exactly the (empty) held locks. -/
theorem adM_held : HeldGenau ([] : List (Res adD)) (offen ([] : List (Ereignis adD))) := by
  intro L
  simp only [List.not_mem_nil, offen]

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

end Gabbro.Grammatik
