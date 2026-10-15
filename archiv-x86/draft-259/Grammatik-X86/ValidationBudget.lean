/-
  File:      Grammatik/X86/ValidationBudget.lean
  Subject:   Fail-closed fuel/resource-limited decode and entry traversal.

  Lane 431 (Lean-first reserve): bounded validation helpers over the
  canonical decoder (`Codec.decode`) and the canonical image checks
  (`Bild.eintragEnthalten`). A timed-out or refused traversal answers
  `none`/`false`, never acceptance; an accepted prefix never bypasses
  remaining bytes or entries. No timing, cost or full-validator claim.
-/
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Bild

namespace Gabbro.Grammatik.X86

/-- Fuel-bounded decode traversal over actual canonical bytes. -/
def decodeFuel : Nat → List Byte → Option (List Decodiert × List Byte)
  | 0, _ => none
  | _ + 1, [] => some ([], [])
  | n + 1, bs =>
    match decode bs with
    | none => none
    | some (d, rest) =>
      if d.laenge + rest.length == bs.length && laengeOk d.laenge then
        match decodeFuel n rest with
        | none => none
        | some (ins, rest') => some (d :: ins, rest')
      else none

/-- Full acceptance under fuel: traversal succeeds with no rest. -/
def validAllFuel (fuel : Nat) (bs : List Byte) : Bool :=
  match decodeFuel fuel bs with
  | some (_, []) => true
  | _ => false

/-- Fuel-bounded entry check: every entry must satisfy `ok`. -/
def entriesOkFuel : Nat → List Nat → (Nat → Bool) → Bool
  | 0, [], _ => true
  | 0, _ :: _, _ => false
  | _ + 1, [], _ => true
  | n + 1, e :: es, ok => ok e && entriesOkFuel n es ok

/-! ## 1. Fail-closed fuel facts: timeout never accepts. -/

/-- Zero fuel refuses every byte list, including the empty one. -/
theorem decodeFuel_zero (bs : List Byte) :
    decodeFuel 0 bs = none := by
  cases bs <;> rfl

/-- Positive fuel accepts the empty input with no remainder. -/
theorem decodeFuel_nil_succ (n : Nat) :
    decodeFuel (n + 1) [] = some ([], []) := by
  rfl

/-- Zero fuel never validates: timeout is refusal, not acceptance. -/
theorem validAllFuel_zero (bs : List Byte) :
    validAllFuel 0 bs = false := by
  simp [validAllFuel, decodeFuel_zero]

/-- A refused first decode refuses under any positive fuel on nonempty input. -/
theorem decodeFuel_step_refusal (n : Nat) (bs : List Byte)
    (hne : bs ≠ []) (hdec : decode bs = none) :
    decodeFuel (n + 1) bs = none := by
  cases bs with
  | nil => simp at hne
  | cons _ _ =>
    simp only [decodeFuel, hdec]

/-! ## 2. Full acceptance: timeout and leftover bytes never accept. -/

/-- Fuel exhaustion refuses: `none` never validates. -/
theorem validAllFuel_none (fuel : Nat) (bs : List Byte)
    (h : decodeFuel fuel bs = none) :
    validAllFuel fuel bs = false := by
  simp [validAllFuel, h]

/-- Acceptance is full consumption: no remainder bypassed. -/
theorem validAllFuel_some_empty (fuel : Nat) (bs : List Byte)
    (ins : List Decodiert)
    (h : decodeFuel fuel bs = some (ins, [])) :
    validAllFuel fuel bs = true := by
  simp [validAllFuel, h]

/-- A leftover suffix never validates: an accepted prefix does not
    bypass remaining bytes. -/
theorem validAllFuel_rest (fuel : Nat) (bs : List Byte)
    (ins : List Decodiert) (rest : List Byte)
    (h : decodeFuel fuel bs = some (ins, rest)) (hne : rest ≠ []) :
    validAllFuel fuel bs = false := by
  unfold validAllFuel
  rw [h]
  cases rest with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- One-step unfolding of the fuel traversal on a nonempty input
    (definitional, by `rfl`): the canonical `decode` decides, the
    length/suffix check gates, and the tail runs under one less fuel. -/
theorem decodeFuel_cons_eq (n : Nat) (b : Byte) (tl : List Byte) :
    decodeFuel (n + 1) (b :: tl) =
      match decode (b :: tl) with
      | none => none
      | some (d, rest) =>
        if d.laenge + rest.length == (b :: tl).length && laengeOk d.laenge then
          match decodeFuel n rest with
          | none => none
          | some (ins, rest') => some (d :: ins, rest')
        else none := rfl

/-- BOUNDEDNESS (actually derived): a successful traversal decodes at
    most `fuel` instructions. The consumer (direct-compiler validation
    stage, DESIGN §588-599: fuel-bounded search) may budget by count. -/
theorem decodeFuel_ins_le_fuel (fuel : Nat) (bs : List Byte)
    (ins : List Decodiert) (rest : List Byte)
    (h : decodeFuel fuel bs = some (ins, rest)) :
    ins.length ≤ fuel := by
  induction fuel generalizing bs ins rest with
  | zero =>
    rw [decodeFuel_zero] at h
    cases h
  | succ n ih =>
    cases bs with
    | nil =>
      rw [decodeFuel_nil_succ] at h
      cases h
      exact Nat.zero_le _
    | cons b tl =>
      rw [decodeFuel_cons_eq] at h
      cases hdec : decode (b :: tl) with
      | none =>
        simp only [hdec] at h
        cases h
      | some pr =>
        obtain ⟨d, mid⟩ := pr
        simp only [hdec] at h
        by_cases hc : (d.laenge + mid.length == (b :: tl).length &&
          laengeOk d.laenge) = true
        · rw [if_pos hc] at h
          cases hrec : decodeFuel n mid with
          | none =>
            simp only [hrec] at h
            cases h
          | some pr2 =>
            obtain ⟨ins2, rest2⟩ := pr2
            simp only [hrec] at h
            cases h
            exact Nat.succ_le_succ (ih _ _ _ hrec)
        · rw [if_neg hc] at h
          cases h

/-- MORE FUEL PRESERVES ACCEPTANCE: a decoded traversal stays decoded
    with one more fuel unit. Raising the validation budget never revokes
    an accepted result (DESIGN §614-617: exhausted budget refuses, more
    budget keeps the valid output). -/
theorem decodeFuel_mono_succ (n : Nat) (bs : List Byte)
    (r : List Decodiert × List Byte)
    (h : decodeFuel n bs = some r) :
    decodeFuel (n + 1) bs = some r := by
  induction n generalizing bs r with
  | zero =>
    rw [decodeFuel_zero] at h
    cases h
  | succ m ih =>
    cases bs with
    | nil =>
      rw [decodeFuel_nil_succ] at h
      cases h
      rfl
    | cons b tl =>
      rw [decodeFuel_cons_eq] at h ⊢
      cases hdec : decode (b :: tl) with
      | none =>
        simp only [hdec] at h
        cases h
      | some pr =>
        obtain ⟨d, mid⟩ := pr
        simp only [hdec] at h ⊢
        by_cases hc : (d.laenge + mid.length == (b :: tl).length &&
          laengeOk d.laenge) = true
        · rw [if_pos hc] at h ⊢
          cases hrec : decodeFuel m mid with
          | none =>
            simp only [hrec] at h
            cases h
          | some pr2 =>
            obtain ⟨ins2, rest2⟩ := pr2
            simp only [hrec] at h
            cases h
            have hrec2 := ih _ _ hrec
            simp only [hrec2]
        · rw [if_neg hc] at h ⊢
          cases h

/-- Full validation is monotone in fuel: a fully accepted byte list
    stays accepted with one more fuel unit. -/
theorem validAllFuel_mono_succ (n : Nat) (bs : List Byte)
    (h : validAllFuel n bs = true) :
    validAllFuel (n + 1) bs = true := by
  unfold validAllFuel at h ⊢
  cases hfuel : decodeFuel n bs with
  | none =>
    simp only [hfuel] at h
    cases h
  | some pr =>
    obtain ⟨ins, rest⟩ := pr
    cases hrest : rest with
    | cons hd tl =>
      simp only [hfuel, hrest] at h
      cases h
    | nil =>
      have h2 : decodeFuel (n + 1) bs = some (ins, []) :=
        decodeFuel_mono_succ n bs _ (by rw [hfuel, hrest])
      simp only [h2]

/-! ## 3. Entry traversal: timeout and bypassed entries never accept. -/

/-- One-step unfolding on a nonempty entry list (definitional). -/
theorem entriesOkFuel_cons_eq (n : Nat) (e : Nat) (es : List Nat)
    (ok : Nat → Bool) :
    entriesOkFuel (n + 1) (e :: es) ok =
      (ok e && entriesOkFuel n es ok) := rfl

/-- Zero fuel refuses every nonempty entry list. -/
theorem entriesOkFuel_zero_cons (e : Nat) (es : List Nat)
    (ok : Nat → Bool) :
    entriesOkFuel 0 (e :: es) ok = false := rfl

/-- A refused head entry refuses the whole list: the head is checked,
    never bypassed. -/
theorem entriesOkFuel_head_fail (n : Nat) (e : Nat) (es : List Nat)
    (ok : Nat → Bool) (hfail : ok e = false) :
    entriesOkFuel (n + 1) (e :: es) ok = false := by
  simp [entriesOkFuel_cons_eq, hfail]

/-- An accepted list checks its head AND its tail: an accepted prefix
    does not bypass remaining entries. -/
theorem entriesOkFuel_true_head_tail (n : Nat) (e : Nat) (es : List Nat)
    (ok : Nat → Bool)
    (h : entriesOkFuel (n + 1) (e :: es) ok = true) :
    ok e = true ∧ entriesOkFuel n es ok = true := by
  rw [entriesOkFuel_cons_eq] at h
  cases he : ok e with
  | true =>
    simp only [he] at h
    exact ⟨rfl, h⟩
  | false =>
    simp [he] at h

/-- BOUNDEDNESS (actually derived): an accepted entry list holds at most
    `fuel` entries. -/
theorem entriesOkFuel_length_le (fuel : Nat) (es : List Nat)
    (ok : Nat → Bool)
    (h : entriesOkFuel fuel es ok = true) :
    es.length ≤ fuel := by
  induction fuel generalizing es with
  | zero =>
    cases es with
    | nil => exact Nat.zero_le _
    | cons e tl =>
      rw [entriesOkFuel_zero_cons] at h
      cases h
  | succ n ih =>
    cases es with
    | nil => exact Nat.zero_le _
    | cons e tl =>
      obtain ⟨_, htail⟩ :=
        entriesOkFuel_true_head_tail n e tl ok h
      exact Nat.succ_le_succ (ih _ htail)

/-- One more fuel unit preserves an accepted entry list. -/
theorem entriesOkFuel_succ_step (n : Nat) (es : List Nat)
    (ok : Nat → Bool)
    (h : entriesOkFuel n es ok = true) :
    entriesOkFuel (n + 1) es ok = true := by
  induction n generalizing es with
  | zero =>
    cases es with
    | nil => rfl
    | cons e tl =>
      rw [entriesOkFuel_zero_cons] at h
      cases h
  | succ n ih =>
    cases es with
    | nil => rfl
    | cons e tl =>
      rw [entriesOkFuel_cons_eq] at h ⊢
      obtain ⟨hhead, htail⟩ :=
        entriesOkFuel_true_head_tail n e tl ok h
      have htail2 := ih _ htail
      simp [hhead, htail2]

/-- MORE FUEL PRESERVES ACCEPTANCE for entry lists: raising the budget
    never revokes an accepted check. -/
theorem entriesOkFuel_mono (n m : Nat) (hle : n ≤ m) (es : List Nat)
    (ok : Nat → Bool)
    (h : entriesOkFuel n es ok = true) :
    entriesOkFuel m es ok = true := by
  induction hle generalizing es with
  | refl => exact h
  | step _ ih => exact entriesOkFuel_succ_step _ _ _ (ih _ h)

/-! ## 4. Image entries under fuel, over the canonical check.

    The consumer is the direct-compiler validation stage: entry vectors
    are checked with the SAME `Bild.eintragEnthalten` the image
    well-formedness uses (no second register), under an explicit fuel
    bound. Timeout refuses; an accepted prefix never bypasses entries. -/

/-- Fuel-bounded image-entry check with the canonical containment test. -/
def bildEintraegeOkFuel (bias : Nat) (secs : List Abschnitt)
    (fuel : Nat) (es : List Nat) : Bool :=
  entriesOkFuel fuel es (eintragEnthalten bias secs)

/-- Zero fuel refuses every nonempty image-entry list. -/
theorem bildEintraegeOkFuel_zero_cons (bias : Nat)
    (secs : List Abschnitt) (e : Nat) (es : List Nat) :
    bildEintraegeOkFuel bias secs 0 (e :: es) = false := rfl

/-- An accepted image-entry list checks its head AND its tail, with the
    canonical `eintragEnthalten`: remaining entries are never bypassed. -/
theorem bildEintraegeOkFuel_head_tail (bias : Nat)
    (secs : List Abschnitt) (n : Nat) (e : Nat) (es : List Nat)
    (h : bildEintraegeOkFuel bias secs (n + 1) (e :: es) = true) :
    eintragEnthalten bias secs e = true ∧
      bildEintraegeOkFuel bias secs n es = true :=
  entriesOkFuel_true_head_tail n e es _ h

/-- Every accepted image entry is canonically contained: success implies
    each listed entry lies in an executable section. -/
theorem bildEintraegeOkFuel_all (bias : Nat) (secs : List Abschnitt)
    (fuel : Nat) (es : List Nat)
    (h : bildEintraegeOkFuel bias secs fuel es = true)
    (e : Nat) (hmem : e ∈ es) :
    eintragEnthalten bias secs e = true := by
  induction fuel generalizing es with
  | zero =>
    have h' : entriesOkFuel 0 es (eintragEnthalten bias secs) = true := h
    cases es with
    | nil =>
      simp at hmem
    | cons hd tl =>
      rw [entriesOkFuel_zero_cons] at h'
      cases h'
  | succ n ih =>
    have h' : entriesOkFuel (n + 1) es (eintragEnthalten bias secs)
        = true := h
    cases es with
    | nil =>
      simp at hmem
    | cons hd tl =>
      rw [entriesOkFuel_cons_eq] at h'
      obtain ⟨hhead, htail⟩ :=
        entriesOkFuel_true_head_tail n hd tl _ h'
      cases List.mem_cons.mp hmem with
      | inl heq =>
        rw [heq]
        exact hhead
      | inr htl =>
        have htail' : bildEintraegeOkFuel bias secs n tl = true := htail
        exact ih _ htail' htl

/-! ## 5. Concrete witnesses over canonical bytes and the image.

    Positive cases decode REAL canonical bytes (`ret`, two `ret`s) and
    check the REAL witness image entries; negative cases refuse an
    unknown opcode, a fuel timeout and an outside entry. The joint
    witness ties decode acceptance and entry acceptance to a REAL
    memory-changing run from the canonical loaded image
    (`Bild.schreibLese_zeuge`: no second memory model). -/

/-- POSITIVE: one canonical `ret` byte decodes under fuel 2 with no rest. -/
theorem wit_decode_ret :
    decodeFuel 2 [natByte 195] = some ([⟨.ret, 1⟩], []) := by
  decide

/-- POSITIVE: the single `ret` byte fully validates under fuel 2. -/
theorem wit_valid_ret :
    validAllFuel 2 [natByte 195] = true := by
  decide

/-- NEGATIVE (timeout): fuel 1 refuses the one-byte program that needs
    fuel 2; timeout never accepts. -/
theorem wit_timeout_refuses :
    decodeFuel 1 [natByte 195] = none ∧
      validAllFuel 1 [natByte 195] = false := by
  refine ⟨by decide, by decide⟩

/-- NEGATIVE (unknown opcode): `0xFF` is refused under any tried fuel,
    never accepted. -/
theorem wit_unknown_refuses :
    decodeFuel 2 [natByte 255] = none ∧
      validAllFuel 2 [natByte 255] = false := by
  refine ⟨by decide, by decide⟩

/-- NO-BYPASS over real bytes: fuel 2 refuses the two-`ret` program
    (one byte would be left over), fuel 3 accepts it. -/
theorem wit_two_rets_fuel :
    validAllFuel 2 [natByte 195, natByte 195] = false ∧
      validAllFuel 3 [natByte 195, natByte 195] = true := by
  refine ⟨by decide, by decide⟩

/-- POSITIVE + NEGATIVE over the real witness image: the code entry is
    contained, an address between the sections is not. -/
theorem wit_entries_image :
    bildEintraegeOkFuel 0 [zeugenCode, zeugenDaten] 1 [0x1000] = true ∧
      bildEintraegeOkFuel 0 [zeugenCode, zeugenDaten] 1 [0x5000]
        = false := by
  refine ⟨by decide, by decide⟩

/-- JOINT NON-DEGENERATE WITNESS: canonical decode acceptance, canonical
    entry acceptance and a real memory-changing write/read over the
    canonically loaded witness image, together. -/
theorem joint_decode_entry_memory :
    decodeFuel 2 [natByte 195] = some ([⟨.ret, 1⟩], []) ∧
      bildEintraegeOkFuel 0 [zeugenCode, zeugenDaten] 1 [0x1000] = true ∧
      ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
          m.bytes a ≠ m'.bytes a := by
  refine ⟨by decide, by decide, schreibLese_zeuge⟩

/- CUTS:
    Proved here, over the ACTUAL canonical decoder (`Codec.decode`),
    the actual length gate (`laengeOk`) and the actual image entry check
    (`Bild.eintragEnthalten`): fail-closed fuel traversal (`decodeFuel`,
    `validAllFuel`, `entriesOkFuel`, `bildEintraegeOkFuel`) with
    timeout/refusal-never-accepts, accepted-prefix-never-bypasses-rest,
    actually-derived count bounds (`ins.length ≤ fuel`,
    `es.length ≤ fuel`), more-fuel-preserves-acceptance, every accepted
    image entry canonically contained, and concrete positive/negative/
    joint witnesses (canonical `ret` bytes, unknown opcode, fuel
    timeout, witness-image entries, reused loaded-memory write/read).
    NOT proved here, and not claimed:
    - No timing or cost claim: the bounds count decoded instructions and
      checked entries only. No millisecond, cycle or asymptotic claim
      (no quadratic-cost statement of any kind) is made or measured.
    - No complete source validator and no closed whole-image validation:
      control flow, relocation re-decode, permissions, ABI, entries beyond
      containment and emission correspondence stay with their owners
      (Byteschritt/Bild and the OPEN items they name).
    - No hardware claim: bytes are model `Byte` lists, memory is the
      model `Speicher` function; silicon, caches, TLBs, store buffers,
      self-modifying-code coherence, per-byte-TSO-as-multi-byte-atomicity,
      interrupts, faults, FP control/NaNs and flag undefinedness are open.
    - No OS/software contract as hardware assumption: OS and binding
      contracts are user logic, never assumed; hardware assumptions stay
      named elsewhere.
    - No desired-correctness assumption: every traversal checks the
      length/suffix equation and the length gate at runtime and refuses
      on mismatch; nothing assumes the decoder is right.
    - The arbitrary-input decoder length soundness of Byteschritt stays
      open there; this module does not need it (each step re-checks).
    - This module performs no memory-changing execution itself (pure
      `Option`/`Bool` traversals); the memory-changing conjunct of the
      joint witness is `Bild.schreibLese_zeuge`, reused, not redone.
-/

#print axioms decodeFuel_zero
#print axioms decodeFuel_nil_succ
#print axioms validAllFuel_zero
#print axioms decodeFuel_step_refusal
#print axioms validAllFuel_none
#print axioms validAllFuel_some_empty
#print axioms validAllFuel_rest
#print axioms decodeFuel_cons_eq
#print axioms decodeFuel_ins_le_fuel
#print axioms decodeFuel_mono_succ
#print axioms validAllFuel_mono_succ
#print axioms entriesOkFuel_cons_eq
#print axioms entriesOkFuel_zero_cons
#print axioms entriesOkFuel_head_fail
#print axioms entriesOkFuel_true_head_tail
#print axioms entriesOkFuel_length_le
#print axioms entriesOkFuel_succ_step
#print axioms entriesOkFuel_mono
#print axioms bildEintraegeOkFuel_zero_cons
#print axioms bildEintraegeOkFuel_head_tail
#print axioms bildEintraegeOkFuel_all
#print axioms wit_decode_ret
#print axioms wit_valid_ret
#print axioms wit_timeout_refuses
#print axioms wit_unknown_refuses
#print axioms wit_two_rets_fuel
#print axioms wit_entries_image
#print axioms joint_decode_entry_memory

end Gabbro.Grammatik.X86
