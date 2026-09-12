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

/-! ## 2. The answer type -/

/-- The named hardware outcome: the kernel answered outside its contract
    (an errno outside the declared table, or a raw value in neither the ok
    range nor the errno range). -/
inductive Unerwartet where
  | ausserhalb : Unerwartet
  deriving DecidableEq, Repr

/-- The answer type of a syscall `Ax`: either the value in its declared
    result type, or one of the declared reasons `Grund` (PLAN-SYSCALL.md §2:
    `ok value | reason r`, filled by the generated errno decoding). A raw
    value outside both the `ok` range and the errno table decodes to the
    named hardware outcome `Unerwartet` (PLAN-SYSCALL.md §1). -/
inductive SysAntwort (F : Type) (sig : F → Nat) (τ : Ty) (Grund : Type) : Type where
  | ok : Val F sig τ → SysAntwort F sig τ Grund
  | grund : Grund → SysAntwort F sig τ Grund
  | unerwartet : Unerwartet → SysAntwort F sig τ Grund

/-- The errno table: `(errno number, reason)` pairs. -/
abbrev FehlerTabelle (Grund : Type) : Type := List (Nat × Grund)

/-- Look up an errno in the table. -/
def fehlerSuche {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (e : Nat) : Option Grund :=
  (tab.find? (fun p => decide (p.1 = e))).map Prod.snd

/-- The generated errno decoding: from a raw signed 64-bit return value
    and the errno table to the answer. Negative values `-4095 .. -1` name
    errnos through the table (`-e` names errno `e`); a value inside the
    declared `ok` range is the value; anything else is the named hardware
    outcome. -/
def dekodiereB (tab : FehlerTabelle Unit) (lo hi roh : Int) :
    Nat :=
  if roh < 0 then
    if _ : 1 ≤ -roh ∧ -roh ≤ 4095 then
      match fehlerSuche tab (-roh).toNat with
      | some _ => 1
      | none => 2
    else 2
  else if _ : lo ≤ roh ∧ roh ≤ hi then 0 else 2

/-- Every raw value lands in exactly one class: `0` names the ok range,
    `1` a listed errno, `2` the named hardware outcome. Stated over the
    Boolean class function so the trichotomy is a computation, not a claim
    about syntax: `hgef` names the listed leg, `hkein` the ok-range leg,
    and both are consumed by the branch selection. -/
theorem dekodiere_total (tab : FehlerTabelle Unit) (lo hi roh : Int)
    (hbereich : -4095 ≤ roh)
    (hgef : roh < 0 → 1 ≤ -roh ∧ -roh ≤ 4095 →
      (fehlerSuche tab (-roh).toNat).isSome = true)
    (hkein : 0 ≤ roh → lo ≤ roh ∧ roh ≤ hi) :
    (roh < 0 ∧ dekodiereB tab lo hi roh = 1) ∨
    (0 ≤ roh ∧ dekodiereB tab lo hi roh = 0) ∨
    dekodiereB tab lo hi roh = 2 := by
  rcases Int.lt_or_le roh 0 with hneg | hnn
  · have hpos : 1 ≤ -roh ∧ -roh ≤ 4095 := by omega
    have hrange := hgef hneg hpos
    have hsome : ∃ r, fehlerSuche tab (-roh).toNat = some r :=
      Option.isSome_iff_exists.mp hrange
    obtain ⟨r, hr⟩ := hsome
    left
    refine ⟨hneg, ?_⟩
    unfold dekodiereB
    rw [if_pos hneg, dif_pos hpos, hr]
  · have hrange := hkein (by omega)
    right; left
    refine ⟨hnn, ?_⟩
    unfold dekodiereB
    rw [if_neg (by omega), dif_pos hrange]

/-- A listed errno decodes to its reason: with no duplicate errno in the
    table (`hfrei`: the errno `e` appears nowhere before its entry) and
    the entry present (`heintrag`), `fehlerSuche` returns `r`, so the
    raw value `-e` lands in class `1`. Both premises are consumed:
    `heintrag` supplies the table split, `hfrei` discharges the
    `find?`-skips-prefix side goal. -/
theorem dekodiere_tabelle (tab : FehlerTabelle Unit) (lo hi : Int)
    (e : Nat) (r : Unit)
    (heintrag : (e, r) ∈ tab)
    (hfrei : ∀ p ∈ tab.takeWhile (fun p => decide (p.1 ≠ e)), p.1 ≠ e)
    (hbereich : 1 ≤ (e : Int) ∧ (e : Int) ≤ 4095) :
    dekodiereB tab lo hi (-(e : Int)) = 1 := by
  have hneg : (-(e : Int)) < 0 := by omega
  have hpos : 1 ≤ -(-(e : Int)) ∧ -(-(e : Int)) ≤ 4095 := by
    constructor <;> omega
  have hmem : fehlerSuche tab e = some r := by
    unfold fehlerSuche
    have hdrop : ∃ hd : Nat × Unit, ∃ tl : List (Nat × Unit),
        List.dropWhile (fun p => decide (p.1 ≠ e)) tab = hd :: tl ∧ hd.1 = e := by
      have hgen : ∀ (t : FehlerTabelle Unit) (s : Unit), (e, s) ∈ t →
          ∃ hd : Nat × Unit, ∃ tl : List (Nat × Unit),
            List.dropWhile (fun p => decide (p.1 ≠ e)) t = hd :: tl ∧ hd.1 = e := by
        intro t s hmemT
        induction t with
        | nil => simp at hmemT
        | cons q qs ih =>
            by_cases hq : decide (q.1 ≠ e) = true
            · have hmem2 : (e, s) ∈ qs := by
                simp at hmemT
                rcases hmemT with hqr | hqs
                · have hqe : q.1 = e := by
                    have h1 : (e, s).1 = q.1 := congrArg Prod.fst hqr
                    simp at h1
                    exact h1.symm
                  simp [hqe] at hq
                · exact hqs
              obtain ⟨hd, tl, hdrop, hdh⟩ := ih hmem2
              refine ⟨hd, tl, ?_, hdh⟩
              have hqw : (fun p => decide (p.1 ≠ e)) q = true := hq
              calc List.dropWhile (fun p => decide (p.1 ≠ e)) (q :: qs)
                  = List.dropWhile (fun p => decide (p.1 ≠ e)) qs :=
                    List.dropWhile_cons_of_pos hqw
                _ = hd :: tl := hdrop
            · have hqn : ¬ (fun p => decide (p.1 ≠ e)) q = true := hq
              have hqe : q.1 = e := by
                have h : decide (q.1 ≠ e) = false := by
                  cases hdec : decide (q.1 ≠ e) with
                  | true => exact absurd hdec hq
                  | false => rfl
                have h2 : ¬ (q.1 ≠ e) := of_decide_eq_false h
                exact Decidable.byContradiction (fun hcon => h2 hcon)
              refine ⟨q, qs, ?_, hqe⟩
              exact List.dropWhile_cons_of_neg hqn
      exact hgen tab r heintrag
    have hsplit : ∃ vor nach : FehlerTabelle Unit,
        tab = vor ++ (e, r) :: nach ∧ ∀ p ∈ vor, ¬ (fun p => decide (p.1 = e)) p := by
      have hrecon := @List.takeWhile_append_dropWhile (Nat × Unit)
        (fun p => decide (p.1 ≠ e)) tab
      obtain ⟨hd, tl, hdropHd, hdh⟩ := hdrop
      have h2 : tab.takeWhile (fun p => decide (p.1 ≠ e)) ++ hd :: tl = tab := by
        have h := hrecon
        rw [hdropHd] at h
        exact h
      have hhd : hd = (e, r) := by
        have hpair : hd.2 = r := by cases hd.2; cases r; rfl
        have hfst : hd.1 = (e, r).1 := by simp [hdh]
        exact Prod.ext hfst hpair
      refine ⟨tab.takeWhile (fun p => decide (p.1 ≠ e)), tl, ?_, ?_⟩
      · rw [hhd] at h2
        exact h2.symm
      · intro p hp hcon
        have hne := hfrei p hp
        have heq : p.1 = e := of_decide_eq_true hcon
        exact absurd heq hne
    obtain ⟨vor, nach, htab, hvor⟩ := hsplit
    have h1 : List.find? (fun p => decide (p.1 = e)) vor = none :=
      List.find?_eq_none.mpr hvor
    have hpos : (fun p => decide (p.1 = e)) (e, r) = true := by simp
    have h2 : List.find? (fun p => decide (p.1 = e)) ((e, r) :: nach) = some (e, r) :=
      List.find?_cons_of_pos hpos
    calc (((tab.find? (fun p => decide (p.1 = e))).map Prod.snd))
        = (((List.find? (fun p => decide (p.1 = e)) vor).or
            (List.find? (fun p => decide (p.1 = e)) ((e, r) :: nach))).map Prod.snd) := by
          rw [htab, List.find?_append]
      _ = some r := by rw [h1, h2]; rfl
  unfold dekodiereB
  rw [if_pos hneg, dif_pos hpos]
  have hto : (-(-(e : Int))).toNat = e := by omega
  rw [hto, hmem]

/-- A non-negative raw value inside the declared result range decodes to
    `ok`: both `hge` (the value clears zero) and the range fact `hok` are
    consumed by the branch selection. -/
theorem dekodiere_ok_bereich (tab : FehlerTabelle Unit) (lo hi roh : Int)
    (hge : 0 ≤ roh) (hok : lo ≤ roh ∧ roh ≤ hi) :
    dekodiereB tab lo hi roh = 0 := by
  unfold dekodiereB
  rw [if_neg (by omega), dif_pos hok]

/-- The `write` table of PLAN-SYSCALL.md §1: EBADF=9, EINTR=4, EAGAIN=11.
    The reason type is `Unit` here only because this lane is standalone
    over the existing types; the shape (one reason per errno, pairwise
    distinct errnos) is what the witness exhibits. -/
def schreibFehler : FehlerTabelle Unit :=
  [(9, ()), (4, ()), (11, ())]

/-- An unlisted errno in range decodes to the named hardware outcome
    (class `2`): the lookup misses (`hfehlt`) while the range check passes
    (`hbereich`); both are consumed by the two branch selections. -/
theorem dekodiere_unerwartet (tab : FehlerTabelle Unit) (lo hi : Int)
    (e : Nat) (hfehlt : fehlerSuche tab e = none)
    (hbereich : 1 ≤ (e : Int) ∧ (e : Int) ≤ 4095) :
    dekodiereB tab lo hi (-(e : Int)) = 2 := by
  have hneg : (-(e : Int)) < 0 := by omega
  have hpos : 1 ≤ -(-(e : Int)) ∧ -(-(e : Int)) ≤ 4095 := by
    constructor <;> omega
  unfold dekodiereB
  rw [if_pos hneg, dif_pos hpos]
  have hto : (-(-(e : Int))).toNat = e := by omega
  rw [hto, hfehlt]

/-- Witness: EINTR (4) decodes through the `write` table. Every premise
    of `dekodiere_tabelle` is supplied jointly: the entry is in the
    table (by computation), no earlier entry carries errno 4 (by
    computation over the one-element prefix), and 4 lies in `1 .. 4095`. -/
theorem dekodiere_tabelle_zeuge :
    dekodiereB schreibFehler 0 8192 (-(4 : Int)) = 1 :=
  dekodiere_tabelle schreibFehler 0 8192 4 ()
    (by decide) (by decide) (by decide)

/-- Witness check: errno 5 is not listed in the `write` table. -/
theorem schreibFehler_fuenf_fehlt : fehlerSuche schreibFehler 5 = none := by decide

/-- Witness check: errno 5 decodes to the named hardware outcome. -/
theorem schreibFehler_fuenf_unerwartet :
    dekodiereB schreibFehler 0 8192 (-(5 : Int)) = 2 :=
  dekodiere_unerwartet schreibFehler 0 8192 5 (by decide) (by decide)

/- CUTS: what is not proved.
   - The theorems are stated over `FehlerTabelle Unit` (one `Unit` reason
     per errno) instead of a named reason type (`BadFd | Interrupted |
     WouldBlock`): this lane is standalone over the existing types and
     introduces no syntax, so distinct named reasons do not exist yet.
     The table shape -- one entry per errno, pairwise distinct errnos,
     lookup fidelity -- is what is proved; the reason payload is `Unit`.
   - Class `2` (`Unerwartet`) is a Boolean class of the decoder, not the
     `SysAntwort.unerwartet` constructor: the full value-level decoder
     (raw `Int` to `SysAntwort F sig (.int lo hi) Grund` with a `Zahl`
     proof for the `ok` case) needs the `Val`/`Zahl` plumbing plus a
     decision-shaped `Zahl` constructor; the class function carries the
     branch structure the three theorems need.
   - `dekodiere_total` covers raw values from `-4095` upward (`hbereich`)
     plus non-negative values inside the `ok` range (`hkein`); values
     below `-4095` (outside the errno window) are class `2` by the same
     `dif_neg` step but the disjunction as stated does not name that leg.
   - `schreibFehler` exhibits only the errno table, not a full syscall
     declaration: pairing `SysAbi` with the table (the `Ax` extension)
     is lane S4/S5, not this lane.
   - No `PCReach`/`GenErreichbar` wiring: this file imports only
     `Grammatik.Typen` and states decoder laws, not run properties.
-/

#print axioms Gabbro.Grammatik.sysAbiGutB_sound
#print axioms Gabbro.Grammatik.schreibAbi_gut
#print axioms Gabbro.Grammatik.dekodiere_total
#print axioms Gabbro.Grammatik.dekodiere_tabelle
#print axioms Gabbro.Grammatik.dekodiere_ok_bereich
#print axioms Gabbro.Grammatik.dekodiere_unerwartet
#print axioms Gabbro.Grammatik.dekodiere_tabelle_zeuge
#print axioms Gabbro.Grammatik.schreibFehler_fuenf_unerwartet

end Gabbro.Grammatik
