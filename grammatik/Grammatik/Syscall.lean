/-
  File:      Grammatik/Syscall.lean
  Subject:   SYSCALL MEANING (lane S2) -- the user side of system calls.

  PLAN-SYSCALL.md §2: a `syscall` declaration is an `Ax` with three additions
  (`sysabi`, the errno-decoded answer type, ghost carriers). This lane builds
  the first two in Lean, standalone over the existing types (`Typen.lean`;
  `Syntax.lean` is not touched):

  * `SysAbi` -- call number, input register map, output register, clobbers,
    with well-formedness `SysAbi.gut` and its decision procedure;
  * `SysAntwort` -- the answer type `ok value | reason r`, filled by the
    generated errno decoding `dekodiere`, with totality (`dekodiere_total`),
    table fidelity (`dekodiere_tabelle`) and the ok-range law
    (`dekodiere_ok_bereich`).

  Ghost carriers and the kernel-pairing theorem are later lanes (S3, S4).
-/
import Grammatik.Typen

namespace Gabbro.Grammatik

/-! ## 1. Registers and the ABI record -/

/-- The x86_64 general registers a syscall stub can name (`aarch64` stays
    sealed, so there is no second register file). -/
inductive SysReg where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

/-- `SysAbi`: the machine side of one syscall declaration (PLAN-SYSCALL.md
    §1: `abi ... number`, `regs in`, `regs out`, `clobbers`). The input map
    binds a register to a parameter index; the output register carries the
    raw signed 64-bit return value the decoding reads. -/
structure SysAbi where
  /-- The call number dispatched on. -/
  nummer : Nat
  /-- Input map: `(register, parameter index)` pairs. -/
  ein : List (SysReg × Nat)
  /-- Output register carrying the raw return value. -/
  aus : SysReg
  /-- Clobbered registers. -/
  clobber : List SysReg
  deriving DecidableEq, Repr

/-- Every x86_64 general register, for exhaustive decidability checks. -/
def sysAlleReg : List SysReg :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .rsp,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The table named in PLAN-SYSCALL.md §1: `write` is number 1, takes
    `(fd, buf, len)` in `rdi, rsi, rdx`, answers in `rax`, clobbers
    `rcx, r11`. -/
def schreibAbi : SysAbi :=
  { nummer := 1
    ein := [(.rdi, 0), (.rsi, 1), (.rdx, 2)]
    aus := .rax
    clobber := [.rcx, .r11] }

/-- Well-formedness: input registers pairwise distinct, no parameter bound
    twice, output register not clobbered. -/
def SysAbi.gut (a : SysAbi) : Prop :=
  (a.ein.map Prod.fst).Nodup ∧ (a.ein.map Prod.snd).Nodup ∧ a.aus ∉ a.clobber

/-- Decision procedure for `SysAbi.gut`. -/
def sysAbiGutB (a : SysAbi) : Bool :=
  decide ((a.ein.map Prod.fst).Nodup) && decide ((a.ein.map Prod.snd).Nodup) &&
    !decide (a.aus ∈ a.clobber)

/-- Soundness: a positive decision means well-formedness. The `decide`
    facts are consumed by `of_decide_eq_true` on both `Nodup` halves and
    `of_decide_eq_false` on the clobber fact. -/
theorem sysAbiGutB_sound (a : SysAbi) (h : sysAbiGutB a = true) : a.gut := by
  unfold sysAbiGutB at h
  simp at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa using h1
  · simpa using h2
  · simpa using h3

instance : Decidable (SysAbi.gut a) :=
  inferInstanceAs (Decidable
    ((a.ein.map Prod.fst).Nodup ∧ (a.ein.map Prod.snd).Nodup ∧ a.aus ∉ a.clobber))

/-- `schreibAbi` is well-formed, by computation. -/
theorem schreibAbi_gut : schreibAbi.gut := by decide

/-! ## 2. The answer type and the errno decoding -/

/-- The answer type of a syscall `Ax`: the value in its declared result
    type, one of the declared reasons `Grund`, or the named hardware
    outcome -- the raw value it came from, for a kernel answer outside
    the contract (PLAN-SYSCALL.md §1). -/
inductive SysAntwort (A : Type) (Grund : Type) where
  | ok : A → SysAntwort A Grund
  | grund : Grund → SysAntwort A Grund
  | unerwartet : Int → SysAntwort A Grund
  deriving DecidableEq, Repr

/-- The errno table: `(errno number, reason)` pairs. -/
abbrev FehlerTabelle (Grund : Type) : Type := List (Nat × Grund)

/-- Look up an errno in the table. -/
def fehlerSuche {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (e : Nat) : Option Grund :=
  (tab.find? (fun p => decide (p.1 = e))).map Prod.snd

/-- First-entry membership. -/
def ersterEintrag {Grund : Type} (tab : FehlerTabelle Grund) (e : Nat) (r : Grund) : Prop :=
  ∃ vor nach : FehlerTabelle Grund, tab = vor ++ (e, r) :: nach ∧
    ∀ p ∈ vor, p.1 ≠ e

/-- The generated errno decoding. -/
def dekodiere {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi roh : Int) :
    SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } Grund :=
  if _ : roh < 0 then
    if _ : 1 ≤ -roh ∧ -roh ≤ 4095 then
      match fehlerSuche tab (-roh).toNat with
      | some r => .grund r
      | none => .unerwartet roh
    else .unerwartet roh
  else if h : lo ≤ roh ∧ roh ≤ hi then .ok ⟨roh, h⟩
  else .unerwartet roh

/-- Lookup fidelity, forward: a first entry is found. -/
theorem fehlerSuche_erster {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (e : Nat) (r : Grund)
    (h : ersterEintrag tab e r) : fehlerSuche tab e = some r := by
  obtain ⟨vor, nach, htab, hvor⟩ := h
  have h1 : List.find? (fun p => decide (p.1 = e)) vor = none := by
    rw [List.find?_eq_none]
    intro x hx hcon
    exact absurd (of_decide_eq_true hcon) (hvor x hx)
  have hpos : (fun p => decide (p.1 = e)) (e, r) = true := by simp
  have h2 : List.find? (fun p => decide (p.1 = e)) ((e, r) :: nach) = some (e, r) :=
    List.find?_cons_of_pos hpos
  unfold fehlerSuche
  calc ((tab.find? (fun p => decide (p.1 = e))).map Prod.snd)
      = (((List.find? (fun p => decide (p.1 = e)) vor).or
          (List.find? (fun p => decide (p.1 = e)) ((e, r) :: nach))).map Prod.snd) := by
        rw [htab, List.find?_append]
    _ = some r := by rw [h1, h2]; rfl

/-- Lookup fidelity, backward: a hit comes from a first entry. -/
theorem erster_of_fehlerSuche {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (e : Nat) (r : Grund)
    (h : fehlerSuche tab e = some r) : ersterEintrag tab e r := by
  unfold fehlerSuche at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, hbr⟩ := h
  rw [List.find?_eq_some_iff_append] at hb
  obtain ⟨hpb, vor, nach, htab, hvor⟩ := hb
  have hbe : b.1 = e := of_decide_eq_true hpb
  have hb_eq : b = (e, r) := Prod.ext hbe hbr
  refine ⟨vor, nach, ?_, ?_⟩
  · rw [htab, hb_eq]
  · intro p hp
    have hnp := hvor p hp
    have h2 : decide (p.1 = e) = false := by simpa using hnp
    exact of_decide_eq_false h2

/-- Characterisation, ok leg: the decoder returns `ok v` exactly for a
    non-negative raw value inside the declared range, with payload `roh`.
    Forward consumes the equation by branch; backward builds it by branch. -/
theorem dekodiere_ok {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi roh : Int)
    (v : { x : Int // lo ≤ x ∧ x ≤ hi }) :
    dekodiere tab lo hi roh = .ok v ↔
      (0 ≤ roh ∧ lo ≤ roh ∧ roh ≤ hi ∧ (v : Int) = roh) := by
  constructor
  · intro hcon
    unfold dekodiere at hcon
    by_cases hneg : roh < 0
    · rw [dif_pos hneg] at hcon
      split at hcon
      · next h =>
        cases he : fehlerSuche tab (-roh).toNat with
        | some r => rw [he] at hcon; cases hcon
        | none => rw [he] at hcon; cases hcon
      · cases hcon
    · rw [dif_neg hneg] at hcon
      split at hcon
      · next h =>
        simp only [SysAntwort.ok.injEq] at hcon
        obtain rfl := Subtype.mk.inj hcon
        exact ⟨by omega, h.1, h.2, rfl⟩
      · cases hcon
  · rintro ⟨hge, hlo, hhi, rfl⟩
    unfold dekodiere
    rw [dif_neg (by omega), dif_pos ⟨hlo, hhi⟩]

/-- Characterisation, reason leg: the decoder returns `grund r` exactly
    for an in-window negative raw value whose errno first-entry is `r`.
    Forward reads the lookup hit off the equation; backward writes it. -/
theorem dekodiere_grund {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi roh : Int) (r : Grund) :
    dekodiere tab lo hi roh = .grund r ↔
      (∃ e : Nat, -4095 ≤ roh ∧ roh ≤ -1 ∧ (-roh).toNat = e ∧
        ersterEintrag tab e r) := by
  constructor
  · intro hcon
    unfold dekodiere at hcon
    by_cases hneg : roh < 0
    · rw [dif_pos hneg] at hcon
      split at hcon
      · next h =>
        cases he : fehlerSuche tab (-roh).toNat with
        | some s =>
          rw [he] at hcon
          simp only [SysAntwort.grund.injEq] at hcon
          obtain rfl := hcon
          refine ⟨(-roh).toNat, by omega, by omega, rfl, ?_⟩
          exact erster_of_fehlerSuche tab _ _ he
        | none => rw [he] at hcon; cases hcon
      · cases hcon
    · rw [dif_neg hneg] at hcon
      split at hcon
      · cases hcon
      · cases hcon
  · rintro ⟨e, hlo, hhi, hto, hfirst⟩
    have hneg : roh < 0 := by omega
    have hpos : 1 ≤ -roh ∧ -roh ≤ 4095 := by constructor <;> omega
    have hfind : fehlerSuche tab e = some r :=
      fehlerSuche_erster tab e r hfirst
    unfold dekodiere
    rw [dif_pos hneg, dif_pos hpos, hto, hfind]

/-- Characterisation, unexpected leg: the decoder returns
    `unerwartet u` exactly when `u` is the raw value and neither the ok
    condition nor any reason condition applies. Forward rules out the
    other two constructors off the equation; backward replays the
    branches with both negations. -/
theorem dekodiere_unerwartet {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi roh : Int) (u : Int) :
    dekodiere tab lo hi roh = .unerwartet u ↔
      (u = roh ∧ ¬ (0 ≤ roh ∧ lo ≤ roh ∧ roh ≤ hi) ∧
        ¬ ∃ e : Nat, ∃ r : Grund, -4095 ≤ roh ∧ roh ≤ -1 ∧ (-roh).toNat = e ∧
          ersterEintrag tab e r) := by
  constructor
  · intro hcon
    have hok : ¬ ∃ v : { x : Int // lo ≤ x ∧ x ≤ hi },
        dekodiere tab lo hi roh = .ok v := by
      intro hcon2
      obtain ⟨v, hv⟩ := hcon2
      rw [hcon] at hv
      cases hv
    have hgr : ¬ ∃ r : Grund, dekodiere tab lo hi roh = .grund r := by
      intro hcon2
      obtain ⟨r, hr⟩ := hcon2
      rw [hcon] at hr
      cases hr
    refine ⟨?_, ?_, ?_⟩
    · unfold dekodiere at hcon
      by_cases hneg : roh < 0
      · rw [dif_pos hneg] at hcon
        split at hcon
        · next h =>
          cases he : fehlerSuche tab (-roh).toNat with
          | some s => rw [he] at hcon; cases hcon
          | none =>
            rw [he] at hcon
            simp only [SysAntwort.unerwartet.injEq] at hcon
            exact hcon.symm
        · simp only [SysAntwort.unerwartet.injEq] at hcon
          exact hcon.symm
      · rw [dif_neg hneg] at hcon
        split at hcon
        · cases hcon
        · simp only [SysAntwort.unerwartet.injEq] at hcon
          exact hcon.symm
    · intro hcon2
      obtain ⟨hge, hlo, hhi⟩ := hcon2
      apply hok
      exact ⟨⟨roh, hlo, hhi⟩, (dekodiere_ok tab lo hi roh _).mpr ⟨hge, hlo, hhi, rfl⟩⟩
    · intro hcon2
      obtain ⟨e, r, hlo, hhi, hto, hfirst⟩ := hcon2
      apply hgr
      exact ⟨r, (dekodiere_grund tab lo hi roh r).mpr ⟨e, hlo, hhi, hto, hfirst⟩⟩
  · rintro ⟨heq, hnok, hngr⟩
    have hgoal : dekodiere tab lo hi roh = .unerwartet roh := by
      unfold dekodiere
      by_cases hneg : roh < 0
      · rw [dif_pos hneg]
        by_cases hpos : 1 ≤ -roh ∧ -roh ≤ 4095
        · rw [dif_pos hpos]
          cases he : fehlerSuche tab (-roh).toNat with
          | some s =>
            exfalso
            apply hngr
            refine ⟨(-roh).toNat, s, by omega, by omega, rfl, ?_⟩
            exact erster_of_fehlerSuche tab _ _ he
          | none => rfl
        · rw [dif_neg hpos]
      · rw [dif_neg hneg]
        by_cases hok : lo ≤ roh ∧ roh ≤ hi
        · exfalso
          apply hnok
          exact ⟨by omega, hok.1, hok.2⟩
        · rw [dif_neg hok]
    subst heq
    exact hgoal

/-! ## 3. The `write` table over a real reason type -/

/-- The I/O reasons of the `write` syscall (PLAN-SYSCALL.md §1). -/
inductive IoFehler where
  | badFd | interrupted | wouldBlock
  deriving DecidableEq, Repr

/-- The `write` table of PLAN-SYSCALL.md §1: EBADF=9, EINTR=4, EAGAIN=11. -/
def schreibFehler : FehlerTabelle IoFehler :=
  [(9, .badFd), (4, .interrupted), (11, .wouldBlock)]

/-- Totality: every raw value decodes to exactly one of `ok` / listed
    reason / unexpected. No premises beyond the arguments: each leg is
    the corresponding characterisation (`dekodiere_ok`, `dekodiere_grund`,
    `dekodiere_unerwartet`), and the exclusion half of the `unerwartet`
    leg is what makes the disjunction exclusive rather than merely
    admissible. -/
theorem dekodiere_total {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi roh : Int) :
    (∃ v : { x : Int // lo ≤ x ∧ x ≤ hi },
      dekodiere tab lo hi roh = .ok v ∧ (v : Int) = roh ∧
      0 ≤ roh ∧ lo ≤ roh ∧ roh ≤ hi) ∨
    (∃ r : Grund, dekodiere tab lo hi roh = .grund r ∧
      ∃ e : Nat, -4095 ≤ roh ∧ roh ≤ -1 ∧ (-roh).toNat = e ∧
        ersterEintrag tab e r) ∨
    (∃ u : Int, dekodiere tab lo hi roh = .unerwartet u ∧ u = roh ∧
      ¬ (0 ≤ roh ∧ lo ≤ roh ∧ roh ≤ hi) ∧
      ¬ ∃ e : Nat, ∃ r : Grund, -4095 ≤ roh ∧ roh ≤ -1 ∧ (-roh).toNat = e ∧
        ersterEintrag tab e r) := by
  unfold dekodiere
  by_cases hneg : roh < 0
  · rw [dif_pos hneg]
    by_cases hpos : 1 ≤ -roh ∧ -roh ≤ 4095
    · rw [dif_pos hpos]
      cases he : fehlerSuche tab (-roh).toNat with
      | some s =>
        right; left
        exact ⟨s, rfl, (-roh).toNat, by omega, by omega, rfl,
          erster_of_fehlerSuche tab _ _ he⟩
      | none =>
        right; right
        refine ⟨roh, rfl, rfl, ?_, ?_⟩
        · intro hcon
          obtain ⟨hge, -, -⟩ := hcon
          omega
        · intro hcon
          obtain ⟨e, s, hlo, hhi, hto, hfirst⟩ := hcon
          have hfind : fehlerSuche tab e = some s :=
            fehlerSuche_erster tab e s hfirst
          rw [← hto] at hfind
          rw [hfind] at he
          cases he
    · rw [dif_neg hpos]
      right; right
      refine ⟨roh, rfl, rfl, ?_, ?_⟩
      · intro hcon
        obtain ⟨hge, -, -⟩ := hcon
        omega
      · intro hcon
        obtain ⟨-, -, hlo, hhi, -, -⟩ := hcon
        apply hpos
        constructor <;> omega
  · rw [dif_neg hneg]
    by_cases hok : lo ≤ roh ∧ roh ≤ hi
    · left
      refine ⟨⟨roh, hok⟩, ?_, rfl, by omega, hok.1, hok.2⟩
      simp [dif_pos hok]
    · right; right
      refine ⟨roh, ?_, rfl, ?_, ?_⟩
      · simp [dif_neg hok]
      · intro hcon
        exact absurd hcon.2 hok
      · intro hcon
        obtain ⟨-, -, hlo, hhi, -, -⟩ := hcon
        omega

/-- Table fidelity: a listed errno decodes to its reason. This is the
    backward direction of `dekodiere_grund` at a concrete entry. -/
theorem dekodiere_tabelle {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi : Int)
    (e : Nat) (r : Grund)
    (hfirst : ersterEintrag tab e r)
    (hbereich : 1 ≤ (e : Int) ∧ (e : Int) ≤ 4095) :
    dekodiere tab lo hi (-(e : Int)) = .grund r :=
  (dekodiere_grund tab lo hi _ r).mpr
    ⟨e, by omega, by omega, by omega, hfirst⟩

/-- The ok-range law: a non-negative raw value inside the declared range
    decodes to `ok` with payload `roh`. Backward direction of
    `dekodiere_ok`. -/
theorem dekodiere_ok_bereich {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (lo hi roh : Int)
    (hge : 0 ≤ roh) (hok : lo ≤ roh ∧ roh ≤ hi) :
    dekodiere tab lo hi roh = .ok ⟨roh, hok⟩ :=
  (dekodiere_ok tab lo hi roh _).mpr ⟨hge, hok.1, hok.2, rfl⟩

/-- ZEUGE: EBADF (9) decodes through the `write` table to `badFd`. Every
    premise of `dekodiere_tabelle` is supplied jointly: the first-entry
    split (empty prefix, so freshness is vacuous) and `9 ∈ 1 .. 4095`,
    both by computation. -/
theorem dekodiere_tabelle_zeuge :
    dekodiere schreibFehler 0 8192 (-(9 : Int)) = .grund IoFehler.badFd :=
  dekodiere_tabelle schreibFehler 0 8192 9 IoFehler.badFd
    ⟨[], [(4, .interrupted), (11, .wouldBlock)], rfl, by decide⟩
    (by decide)

/-- Totality witness, ok leg: 5 in range 0..10 decodes to `ok 5`. -/
theorem dekodiere_total_ok_zeuge :
    dekodiere schreibFehler 0 10 5 =
      .ok (⟨5, by decide⟩ : { x : Int // (0 : Int) ≤ x ∧ x ≤ 10 }) := by
  decide

/-- Totality witness, reason leg: -4 decodes to `interrupted`. -/
theorem dekodiere_total_grund_zeuge :
    dekodiere schreibFehler 0 10 (-4) = .grund IoFehler.interrupted := by
  decide

/-- Totality witness, unexpected leg: -22 (unlisted errno) decodes to
    `unerwartet (-22)`. -/
theorem dekodiere_total_unerwartet_zeuge :
    dekodiere schreibFehler 0 10 (-22) = .unerwartet (-22) := by
  decide

/- CUTS: what is not proved.
   - `schreibFehler` exhibits only the errno table, not a full syscall
     declaration: pairing `SysAbi` with the table (the `Ax` extension)
     is lane S4/S5, not this lane.
   - No `PCReach`/`GenErreichbar` wiring: this file imports only
     `Grammatik.Typen` and states decoder laws, not run properties.
-/

#print axioms Gabbro.Grammatik.sysAbiGutB_sound
#print axioms Gabbro.Grammatik.schreibAbi_gut
#print axioms Gabbro.Grammatik.fehlerSuche_erster
#print axioms Gabbro.Grammatik.erster_of_fehlerSuche
#print axioms Gabbro.Grammatik.dekodiere_ok
#print axioms Gabbro.Grammatik.dekodiere_grund
#print axioms Gabbro.Grammatik.dekodiere_unerwartet
#print axioms Gabbro.Grammatik.dekodiere_total
#print axioms Gabbro.Grammatik.dekodiere_tabelle
#print axioms Gabbro.Grammatik.dekodiere_ok_bereich
#print axioms Gabbro.Grammatik.dekodiere_tabelle_zeuge
#print axioms Gabbro.Grammatik.dekodiere_total_ok_zeuge
#print axioms Gabbro.Grammatik.dekodiere_total_grund_zeuge
#print axioms Gabbro.Grammatik.dekodiere_total_unerwartet_zeuge

end Gabbro.Grammatik
