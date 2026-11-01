module

public import Grammatik.Kern.Semantik.Syscall.Syscall
public import Grammatik.Kern.Syntax.Satz

@[expose] public section



namespace Gabbro.Grammatik

/-- A kernel dispatch entry: the call number, the register map, and the
    proved contract (requires `Pk`, ensures `Qk` over the raw answer,
    effects `Ek`/`EkG`). -/
structure KernelEintragG (A : Type) (D : Deklaration) (Params : Ctx) where
  nummer : Nat
  /-- The machine side of the gate: `SysAbi` (x86_64) or `SysAbiArm` (AArch64), see
      `SyscallAllg.lean`. The pairing only COMPARES it and hands it to the implementation. -/
  abi : A
  Pk : World D → Env D Params → Prop
  Qk : World D → World D → Int → Env D Params → Prop
  Ek : D.Tab → Bool
  EkG : D.Glob → Bool

/-- The user-side `syscall` declaration for one number: the register map,
    the errno table, the declared ok-range, and the declared contract
    (requires `Pu`, ensures `Qu` over the DECODED answer, effects
    `Eu`/`EuG`). -/
structure UserSyscallG (A : Type) (D : Deklaration) (Params : Ctx) (Grund : Type)
    [DecidableEq Grund] where
  nummer : Nat
  abi : A
  tab : FehlerTabelle Grund
  lo : Int
  hi : Int
  Pu : World D → Env D Params → Prop
  Qu : World D → World D → SysAntwort Int Grund → Env D Params → Prop
  Eu : D.Tab → Bool
  EuG : D.Glob → Bool

/-- The x86_64 instances (the original names; every earlier statement and witness is about them). -/
abbrev KernelEintrag (D : Deklaration) (Params : Ctx) : Type := KernelEintragG SysAbi D Params

abbrev UserSyscall (D : Deklaration) (Params : Ctx) (Grund : Type) [DecidableEq Grund] : Type :=
  UserSyscallG SysAbi D Params Grund

/-- Forget the range proof of an `ok` payload: the user contract talks
    about plain integers, the decoder about range-checked ones. -/
def antwortInt {Grund : Type} {lo hi : Int} :
    SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } Grund → SysAntwort Int Grund
  | .ok v => .ok v.val
  | .why r => .why r
  | .unerwartet u => .unerwartet u

/-- The oracle premise for ONE axiom: exactly the per-axiom instance of
    the current `GutO` (frame of the declared axiom writes, unchanged locks,
    and the conditional recording clause over `axiomSpur`), plus the decoded
    user contract whenever the user requires-clause holds at entry. -/
def PaarGut (D : Deklaration) (a : D.Ax) (O : Orakel D)
    {A : Type} {Grund : Type} [DecidableEq Grund]
    (u : UserSyscallG A D (D.aparams a) Grund) : Prop :=
  (∀ σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt ∧
    ((∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt) →
     (∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt) →
     ∃ tabs : List D.Tab, ∃ globs : List D.Glob, ∃ Λe : List (Res D),
       (∀ t, D.aschreibt a t = true → t ∈ tabs) ∧
       (∀ g, D.agschreibt a g = true → g ∈ globs) ∧
       (∀ t, D.aschreibt a t = true → darf D t Λe) ∧
       (∀ g, D.agschreibt a g = true → gdarf D g Λe) ∧
       (∀ m st, Res.marke m st ∉ Λe) ∧
       HeldIn Λe σ.haelt ∧
       (O.wirkt a σ ρ).1.spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur)) ∧
  (∀ σ ρ, u.Pu σ ρ → u.Qu σ (O.wirkt a σ ρ).1
    (antwortInt (dekodiere u.tab u.lo u.hi (O.wirkt a σ ρ).2)) ρ)

/-- The pairing theorem (PLAN-SYSCALL.md section 2, item 4, aligned with
    the recording `GutO` of lane 80): register maps agree, `Pu -> Pk`,
    `Qk -> Qu` after decoding, `Ek ⊆ Eu` with `Eu`/`EuG` coinciding with the
    declared axiom writes, and the kernel entry's contract holds for its
    implementation `K` -- including the kernel recording the same
    `axiomSpur` events -- then the oracle premise holds for that `Ax` as the
    per-axiom `GutO` instance plus the decoded contract, so the syscall
    needs no named assumption. Every premise is load-bearing: `hnum`/`habi`
    transport the kernel behaviour to the user dispatch identity,
    `hreq` discharges the kernel precondition, `hens` the user
    postcondition, `hsub`/`hsubG` with `hEu`/`hEuG` widen the kernel frame
    to the declared axiom frame, `hKeff` supplies the kernel frame, locks,
    and recording, `hKcon` the kernel postcondition, `hO` ties the oracle
    to `K`. -/
theorem syscall_paarung (D : Deklaration) (a : D.Ax) (O : Orakel D)
    {A : Type} {Grund : Type} [DecidableEq Grund]
    (k : KernelEintragG A D (D.aparams a)) (u : UserSyscallG A D (D.aparams a) Grund)
    (K : Nat → A → World D → Env D (D.aparams a) → World D → Int → Prop)
    (hnum : k.nummer = u.nummer)
    (habi : k.abi = u.abi)
    (hreq : ∀ σ ρ, u.Pu σ ρ → k.Pk σ ρ)
    (hens : ∀ σ σ' roh ρ, k.Qk σ σ' roh ρ →
      u.Qu σ σ' (antwortInt (dekodiere u.tab u.lo u.hi roh)) ρ)
    (hsub : ∀ t, k.Ek t = true → u.Eu t = true)
    (hsubG : ∀ g, k.EkG g = true → u.EuG g = true)
    (hEu : ∀ t, u.Eu t = D.aschreibt a t)
    (hEuG : ∀ g, u.EuG g = D.agschreibt a g)
    (hKeff : ∀ σ ρ σ' roh, K k.nummer k.abi σ ρ σ' roh →
      Rahmen k.Ek k.EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
      ((∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt) →
       (∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt) →
       ∃ tabs : List D.Tab, ∃ globs : List D.Glob, ∃ Λe : List (Res D),
         (∀ t, D.aschreibt a t = true → t ∈ tabs) ∧
         (∀ g, D.agschreibt a g = true → g ∈ globs) ∧
         (∀ t, D.aschreibt a t = true → darf D t Λe) ∧
         (∀ g, D.agschreibt a g = true → gdarf D g Λe) ∧
         (∀ m st, Res.marke m st ∉ Λe) ∧
         HeldIn Λe σ.haelt ∧
         σ'.spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur))
    (hKcon : ∀ σ ρ σ' roh, K k.nummer k.abi σ ρ σ' roh → k.Pk σ ρ →
      k.Qk σ σ' roh ρ)
    (hO : ∀ σ ρ, ∃ σ' roh, K u.nummer u.abi σ ρ σ' roh ∧
      O.wirkt a σ ρ = (σ', roh)) :
    PaarGut D a O u := by
  have hW : ∀ t, k.Ek t = true → D.aschreibt a t = true := by
    intro t ht
    rw [← hEu t]
    exact hsub t ht
  have hG : ∀ g, k.EkG g = true → D.agschreibt a g = true := by
    intro g hg
    rw [← hEuG g]
    exact hsubG g hg
  refine ⟨?_, ?_⟩
  · intro σ ρ
    obtain ⟨σ', roh, hKbeh, hOeq⟩ := hO σ ρ
    rw [← hnum, ← habi] at hKbeh
    obtain ⟨hfr, hha, hcond⟩ := hKeff σ ρ σ' roh hKbeh
    have hfst : (O.wirkt a σ ρ).1 = σ' := by rw [hOeq]
    refine ⟨hfst ▸ hfr.weiter hW hG, ?_, ?_⟩
    · rw [hfst]; exact hha
    · intro hgt hgg
      obtain ⟨tabs, globs, Λe, hct, hcg, hdt, hdg, hmf, hhi, hspur⟩ :=
        hcond hgt hgg
      refine ⟨tabs, globs, Λe, hct, hcg, hdt, hdg, hmf, hhi, ?_⟩
      rw [hfst]; exact hspur
  · intro σ ρ hPu
    obtain ⟨σ', roh, hKbeh, hOeq⟩ := hO σ ρ
    rw [← hnum, ← habi] at hKbeh
    rw [hOeq]
    dsimp only
    exact hens σ σ' roh ρ (hKcon σ ρ σ' roh hKbeh (hreq σ ρ hPu))

/-! ## 2. Toy `write` fixture: number 1, PLAN-SYSCALL.md section 1 -/

/-- Parameter types of the toy `write`: `(fd, len)`. -/
abbrev swParams : Ctx := [.int 0 7, .int 0 8192]

/-- One unshared table holding offsets (the `os.fds` analog), one
    function writing it, one axiom: the toy `write` syscall. -/
def swD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 8
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 8192
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun g => nomatch g
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Unit
  aparams := fun _ => swParams
  aerg := fun _ => some (.int 0 8192)
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => nomatch g
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-! ## 3. Arguments, contracts, oracle, implementation -/

/-- The `fd` argument of a toy-write environment. -/
def swFd (ρ : Env swD swParams) : Int :=
  match ρ with
  | .cons fd _ => fd.n

/-- The `len` argument of a toy-write environment. -/
def swLen (ρ : Env swD swParams) : Int :=
  match ρ with
  | .cons _ (.cons len _) => len.n

/-- `len` stays in its declared range. -/
theorem swLen_bereich (ρ : Env swD swParams) :
    0 ≤ swLen ρ ∧ swLen ρ ≤ 8192 := by
  cases ρ with
  | cons _ rest =>
    cases rest with
    | cons len _ => exact Val.int_bereich len

/-- The kernel dispatch entry for number 1: requires the descriptor slot
    nonzero (`Open(fd)` analog), ensures a count `≤ len` with the offset
    bumped, or EBADF (`-9`) leaving memory alone; writes the table. Memory
    only (slots), not the trace: the implementation records the declared
    write as the `axiomSpur` event, so the postcondition must allow the
    extra trace. -/
def swK : KernelEintrag swD (swD.aparams ()) where
  nummer := 1
  abi := schreibAbi
  Pk := fun σ ρ => (σ.slots () (swFd ρ) ()).n ≠ 0
  Qk := fun σ σ' roh ρ =>
    (0 ≤ roh ∧ roh ≤ swLen ρ ∧
      σ'.slots = (σ.storeSlot () (swFd ρ) () ⟨1, by decide, by decide⟩).slots) ∨
    (roh = -9 ∧ σ'.slots = σ.slots)
  Ek := fun _ => true
  EkG := fun g => nomatch g

/-- The user side of PLAN-SYSCALL.md section 1: same number and map, the
    `write` errno table, ok-range `0 .. 8192`, `result ≤ len`, declares
    the table written. -/
def swU : UserSyscall swD (swD.aparams ()) IoFehler where
  nummer := 1
  abi := schreibAbi
  tab := schreibFehler
  lo := 0
  hi := 8192
  Pu := fun σ ρ => (σ.slots () (swFd ρ) ()).n ≠ 0
  Qu := fun _ _ ans ρ => match ans with
    | .ok v => v ≤ swLen ρ
    | .why _ => True
    | .unerwartet _ => False
  Eu := fun _ => true
  EuG := fun g => nomatch g

/-- The oracle answering through the kernel: bump the offset slot,
    answer count `0` (always `≤ len`), and record the declared write as the
    `axiomSpur` event the recording `GutO` demands (here over the complete
    domains `[()]`/`[]` with the empty guard trace, which `darf` admits
    since `swD` guards nothing). Locks are untouched (a `zugriff` event
    leaves `offen` unchanged). -/
def swO : Orakel swD where
  wirkt := fun _ σ ρ =>
    ((σ.storeSlot () (swFd ρ) () ⟨1, by decide, by decide⟩).merke
      (axiomSpur [()] [] () [] σ.haelt), 0)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- The kernel implementation relation: the proved frame and postcondition
    travel with every behaviour, indexed by dispatch identity, plus the
    recorded `axiomSpur` event over the complete domains. -/
def swKbeh (n : Nat) (ab : SysAbi) (σ : World swD)
    (ρ : Env swD (swD.aparams ())) (σ' : World swD) (roh : Int) : Prop :=
  n = 1 ∧ ab = schreibAbi ∧ swK.Qk σ σ' roh ρ ∧
    Rahmen swK.Ek swK.EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
    σ'.spur = axiomSpur [()] [] () [] σ.haelt ++ σ.spur

/-! ## 4. The pairing premises, instantiated jointly -/

/-- Same number. -/
theorem swNum : swK.nummer = swU.nummer := by rfl

/-- Same register map. -/
theorem swAbi : swK.abi = swU.abi := by rfl

/-- `Pu -> Pk`: identical requires-clauses. -/
theorem swReq : ∀ σ ρ, swU.Pu σ ρ → swK.Pk σ ρ :=
  fun _ _ h => h

/-- `Ek ⊆ Eu` on tables. -/
theorem swSub : ∀ t, swK.Ek t = true → swU.Eu t = true :=
  fun _ _ => rfl

/-- `Ek ⊆ Eu` on globals: vacuous, there are none. -/
theorem swSubG : ∀ g, swK.EkG g = true → swU.EuG g = true :=
  fun g => nomatch g

/-- `Eu` coincides with the declared axiom writes. -/
theorem swEu : ∀ t, swU.Eu t = swD.aschreibt () t :=
  fun _ => rfl

/-- `EuG` coincides with the declared axiom global writes: vacuous. -/
theorem swEuG : ∀ g, swU.EuG g = swD.agschreibt () g :=
  fun g => nomatch g

/-- The implementation keeps the kernel frame and locks, and records the
    declared write over the complete domains with the empty guard trace
    (admitted since `swD` guards nothing). -/
theorem swEff : ∀ σ ρ σ' roh, swKbeh swK.nummer swK.abi σ ρ σ' roh →
    Rahmen swK.Ek swK.EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
    ((∀ t, swD.aschreibt () t = true → ∀ L, Sum.inl L ∈ swD.braucht t → L ∈ σ.haelt) →
     (∀ g, swD.agschreibt () g = true → ∀ L, Sum.inl L ∈ swD.gbraucht g → L ∈ σ.haelt) →
     ∃ tabs : List swD.Tab, ∃ globs : List swD.Glob, ∃ Λe : List (Res swD),
       (∀ t, swD.aschreibt () t = true → t ∈ tabs) ∧
       (∀ g, swD.agschreibt () g = true → g ∈ globs) ∧
       (∀ t, swD.aschreibt () t = true → darf swD t Λe) ∧
       (∀ g, swD.agschreibt () g = true → gdarf swD g Λe) ∧
       (∀ m st, Res.marke m st ∉ Λe) ∧
       HeldIn Λe σ.haelt ∧
       σ'.spur = axiomSpur tabs globs () Λe σ.haelt ++ σ.spur) := by
  intro σ ρ σ' roh h
  obtain ⟨hn, hab, hQk, hfr, hha, hspur⟩ := h
  refine ⟨hfr, hha, fun hgt hgg => ?_⟩
  refine ⟨[()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, hspur⟩
  · intro t _
    cases t
    exact List.Mem.head _
  · intro g hg
    exact nomatch g
  · intro t _ w hw
    have hnil : swD.braucht t = [] := rfl
    rw [hnil] at hw
    simp only [List.not_mem_nil] at hw
  · intro g hg
    exact nomatch g
  · intro m st hm
    exact nomatch m
  · intro L hL
    exact nomatch L

/-- The implementation delivers the kernel postcondition. -/
theorem swCon : ∀ σ ρ σ' roh, swKbeh swK.nummer swK.abi σ ρ σ' roh →
    swK.Pk σ ρ → swK.Qk σ σ' roh ρ :=
  fun _ _ _ _ h _ => h.2.2.1

/-- Every oracle answer is a kernel behaviour: count `0` (always
    `≤ len`) with the offset bumped and the write event recorded. -/
theorem swO_trifft : ∀ σ ρ, ∃ σ' roh,
    swKbeh swU.nummer swU.abi σ ρ σ' roh ∧ swO.wirkt () σ ρ = (σ', roh) := by
  intro σ ρ
  refine ⟨(σ.storeSlot () (swFd ρ) () ⟨1, by decide, by decide⟩).merke
      (axiomSpur [()] [] () [] σ.haelt), 0,
    ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, rfl⟩
  · exact .inl ⟨by omega, (swLen_bereich ρ).1, rfl⟩
  · exact (rahmen_storeSlot swK.Ek swK.EkG σ () (swFd ρ) ()
      (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)) rfl).trans
      (rahmen_gleich rfl rfl)

/-- `Qk -> Qu` after decoding: a count in range decodes to `ok` with
    payload `roh ≤ len`; EBADF decodes to its listed reason. -/
theorem swEns : ∀ σ σ' roh ρ, swK.Qk σ σ' roh ρ →
    swU.Qu σ σ' (antwortInt (dekodiere swU.tab swU.lo swU.hi roh)) ρ := by
  intro σ σ' roh ρ h
  cases h with
  | inl hok =>
    obtain ⟨h0, hlen, heq⟩ := hok
    have hle : roh ≤ 8192 := by
      have hb := (swLen_bereich ρ).2
      omega
    have hdec : dekodiere schreibFehler 0 8192 roh = .ok ⟨roh, h0, hle⟩ :=
      dekodiere_ok_bereich schreibFehler 0 8192 roh h0 ⟨h0, hle⟩
    show swU.Qu σ σ' (antwortInt (dekodiere schreibFehler 0 8192 roh)) ρ
    rw [hdec]
    show roh ≤ swLen ρ
    exact hlen
  | inr heb =>
    obtain ⟨hrfl, heq⟩ := heb
    subst hrfl
    have hfirst : ersterEintrag schreibFehler 9 IoFehler.badFd :=
      ⟨[], [(4, .interrupted), (11, .wouldBlock)], rfl, by decide⟩
    have hdec : dekodiere schreibFehler 0 8192 (-(9 : Int)) = .why IoFehler.badFd :=
      dekodiere_tabelle schreibFehler 0 8192 9 IoFehler.badFd hfirst (by decide)
    show swU.Qu σ σ' (antwortInt (dekodiere schreibFehler 0 8192 (-9))) ρ
    rw [hdec]
    show True
    exact trivial

/-! ## 5. Witness: the pairing holds, on a non-degenerate program -/

/-- Start world: every offset slot reads `0`, empty trace. -/
def swWelt0 : World swD :=
  { slots := fun _ _ _ => ⟨0, by decide, by decide⟩
    globs := fun g => nomatch g
    spur := [] }

/-- ZEUGE: all ten pairing premises hold jointly for the toy `write`
    (number 1, `schreibAbi`, `schreibFehler`, `result ≤ len`), and the
    program is non-degenerate: function `()` writes table `()`, and a
    `storeSlot` step moves memory (`0 -> 1` at slot `0`). -/
theorem syscall_paarung_zeuge :
    PaarGut swD () swO swU ∧ swD.schreibt () () = true ∧
    ∃ (σ σ' : World swD), σ'.slots () 0 () ≠ σ.slots () 0 () :=
  ⟨syscall_paarung swD () swO swK swU swKbeh swNum swAbi swReq swEns
      swSub swSubG swEu swEuG swEff swCon swO_trifft,
    rfl,
    swWelt0,
    swWelt0.storeSlot () 0 ()
      (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)),
    by
      have hn1 : ((swWelt0.storeSlot () 0 ()
          (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192))).slots () 0 ()).n
          = 1 := rfl
      have hn0 : (swWelt0.slots () 0 ()).n = 0 := rfl
      intro hcon
      have hn := congrArg Zahl.n hcon
      rw [hn1, hn0] at hn
      omega⟩

/-! ## 6. Rejection: an undeclared kernel write breaks the user frame -/

end Gabbro.Grammatik
