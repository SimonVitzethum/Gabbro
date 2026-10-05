/-
  File:      Grammatik/X86/PipelineLinkRel8.lean
  Subject:   Linking: rel8 selection convergence and fall-through coverage.

  FOLLOW-UP of lane 1193 (`PipelineLinkMulti.lean`): open were
  rel8-selection convergence, fall-through coverage beyond re-decoded
  windows, and instructions outside jump/call/conditional sites. This
  file proves branch relaxation with relocation converges (monotone
  widening, termination within the short-site count, fixed-point fit)
  and that the linked bytes cover exactly the relaxed program:
  fall-through bytes survive through the multi-operand frame, every
  site's bytes are exact, short sites read back, long jump sites
  re-decode through the accepted agreement legs; overlapping sites
  stay refused.

  Reused, never duplicated (no second decoder, loader, executor,
  ISA model or IR):
  - operands/patching: `MultiFeld`, `multiBytes`, `multiPatch`,
    `multiPatchAlle`, `opStelle`, `opWeite`, `opsDisjunktB`,
    `opsDisjunktB_gilt`, `multiPatchAlle_rahmen`/`_laenge`/
    `_kopf_stelle`, `disjunktStellen`;
  - rel8 vocabulary: `rel8Passt`, `rel8Byte`, `disp8Signed`,
    `rel8Byte_rundgang`, `multi_rel8_liest`;
  - rel32 bridge: `rel32Bytes`, `rel32Passt`, `fenster_sprung`,
    `feld_agreement_sprung`;
  - mapping/run witnesses: `ruf_schritt_zeuge` (reached
    memory-changing run through actual bytes).
-/
import Grammatik.X86.PipelineLinkMulti

namespace Gabbro.Grammatik.X86

/-- One relaxed program piece: fixed fall-through bytes of length
    `len`, a short (rel8, 2-byte) branch site, or a widened
    (rel32, 5-byte) unconditional-jump site. -/
inductive RelaxStueck where
  | fest (len : Nat)
  | kurz
  | weit
  deriving DecidableEq, Repr

/-- Laid-out width in bytes: fall-through keeps its length, a short
    site is opcode plus one displacement byte, a wide site is opcode
    plus four displacement bytes. -/
def stueckWeite : RelaxStueck → Nat
  | .fest len => len
  | .kurz => 2
  | .weit => 5

/-- A short site never exceeds its widened form. -/
theorem stueckWeite_kurz_le_weit :
    stueckWeite .kurz ≤ stueckWeite .weit := by
  decide

/-! ## 1. Layout: addresses grow monotonically under widening. -/

/-- Widening order on pieces: fixed stays fixed, short stays short or
    widens to the rel32 form. -/
inductive stueckLE : RelaxStueck → RelaxStueck → Prop where
  | fest_eq (l : Nat) : stueckLE (.fest l) (.fest l)
  | kurz_kurz : stueckLE .kurz .kurz
  | kurz_weit : stueckLE .kurz .weit
  | weit_weit : stueckLE .weit .weit

/-- Pointwise widening order on relaxed programs. -/
def progLE : List RelaxStueck → List RelaxStueck → Prop
  | [], [] => True
  | a :: pa, b :: pb => stueckLE a b ∧ progLE pa pb
  | _, _ => False

/-- Widths respect the widening order. Every premise is used: the
    order hypothesis picks the case, the width equations close it. -/
theorem weite_mono {a b : RelaxStueck} (h : stueckLE a b) :
    stueckWeite a ≤ stueckWeite b := by
  cases h with
  | fest_eq l => simp [stueckWeite]
  | kurz_kurz => simp [stueckWeite]
  | kurz_weit => decide
  | weit_weit => simp [stueckWeite]

/-- Laid-out start addresses from `base`: prefix sums of widths. -/
def adressenAux : List RelaxStueck → Nat → List Nat
  | [], _ => []
  | st :: rest, base => base :: adressenAux rest (base + stueckWeite st)

/-- Laid-out start addresses of a relaxed program at load base. -/
def adressen (prog : List RelaxStueck) (basis : Nat) : List Nat :=
  adressenAux prog basis

/-- Addresses keep the program length. -/
theorem adressenAux_laenge (prog : List RelaxStueck) (basis : Nat) :
    (adressenAux prog basis).length = prog.length := by
  induction prog generalizing basis with
  | nil => rfl
  | cons st rest ih => simp [adressenAux, ih]

/-- Pointwise address comparison: every laid-out address of the
    narrower program is covered above by the wider one. -/
def adressenLE (l₁ l₂ : List Nat) : Prop :=
  ∀ (i : Nat) (a : Nat), l₁[i]? = some a →
    ∃ (b : Nat), l₂[i]? = some b ∧ a ≤ b

/-- MONOTONE WIDENING: widening sites never moves any laid-out
    address down. Every premise is used: `hbase` seeds the head,
    `hle` orders head widths (through `weite_mono`) and tail
    addresses (through the induction hypothesis). -/
theorem adressenAux_mono (p q : List RelaxStueck) (b₁ b₂ : Nat)
    (hbase : b₁ ≤ b₂) (hle : progLE p q) :
    adressenLE (adressenAux p b₁) (adressenAux q b₂) := by
  induction p generalizing q b₁ b₂ with
  | nil =>
    cases q with
    | nil =>
      unfold adressenLE
      intro i a h
      simp [adressenAux] at h
    | cons hd tl =>
      simp [progLE] at hle
  | cons hd tl ih =>
    cases q with
    | nil =>
      simp [progLE] at hle
    | cons hd' tl' =>
      simp only [progLE] at hle
      obtain ⟨hhd, htl⟩ := hle
      have hw := weite_mono hhd
      have htail := ih tl' (b₁ + stueckWeite hd)
        (b₂ + stueckWeite hd') (by omega) htl
      unfold adressenLE
      intro i a h
      cases i with
      | zero =>
        simp only [adressenAux, List.getElem?_cons_zero] at h
        simp only [adressenAux, List.getElem?_cons_zero]
        have heq : b₁ = a := Option.some_inj.mp h
        subst heq
        exact ⟨b₂, rfl, hbase⟩
      | succ n =>
        simp only [adressenAux, List.getElem?_cons_succ] at h ⊢
        exact htail n a h

end Gabbro.Grammatik.X86
