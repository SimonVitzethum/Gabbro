/-
  File:      Grammatik/X86/ConcurrentIntegerExecution.lean
  Subject:   Real selected integer bytes on shared TSO execution.

  Lane 720: width-selected (1/2/4/8-byte) integer load/store execution
  over the canonical HwMaschine (HardwareExecution660) with ordered
  byte issue, youngest-own forwarding, ordered drain and
  register/partial-register effects from the accepted scalar producer
  equations (NarrowOps, EffectiveAddress, AddressEncoding). No SC word
  effect is substituted for a buffered access; word single-event
  claims go through WortGruppe/WortGuard with cross-core interleavings.
  Missing width codec rows stay explicit pending extensions.
  Provenance: Intel SDM 325462-093US (clone-local
  .tmp/HARDWARE-REFERENCES/REFERENCES.json + intel-instruction-reference.txt
  headings, e.g. MOV/MOVZX/MOVSX/ADD/SUB/TEST/LEA); headings are
  provenance, never silicon proofs.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.NarrowOps
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.AddressEncoding
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.WordDrainInterleaving
import Grammatik.X86.NarrowCodec

namespace Gabbro.Grammatik.X86

/-- Width-selected integer memory op: load/store at an explicit width
    through base plus displacement (accepted `effAddr` address). -/
inductive ConcIntOp where
  | load (b : Breite) (dst base : Register) (disp : BitVec 32)
  | store (b : Breite) (base src : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- Address of one op from the pre-state register file: the accepted
    pilot `effAddr` (base plus sign-extended displacement). -/
def concAddr (s : Zustand) : ConcIntOp → Adresse
  | .load _ _ base disp => effAddr s base disp
  | .store _ base _ disp => effAddr s base disp

/-! ## 1. Addresses: pre-state, alias, selected-form bridge.

  The op address is the accepted pilot `effAddr` evaluated on the
  pre-state register file; it therefore inherits the accepted
  prestate-aliasing discipline, and coincides with the selected
  `adrEff` on base-plus-disp32 forms (no second address model). -/

/-- The op address reads the base register only: agreeing pre-states
    give the same address (accepted `effAddr_prestate`, lifted). -/
theorem concAddr_prestate (s1 s2 : Zustand) (op : ConcIntOp)
    (h : ∀ base : Register, s1.register base = s2.register base) :
    concAddr s1 op = concAddr s2 op := by
  cases op with
  | load b dst base disp =>
    simp only [concAddr]
    exact effAddr_prestate s1 s2 base disp (h base)
  | store b base src disp =>
    simp only [concAddr]
    exact effAddr_prestate s1 s2 base disp (h base)

/-- ALIAS: different bases may name the same address, so no
    injectivity is claimed (accepted alias shape, lifted to ops). -/
theorem concAddr_alias_beispiel :
    concAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rax 16 } (.load .b64 .rax .rax (BitVec.ofNat 32 0)) = concAddr zeugeZustand (.load .b64 .rax .rbx (BitVec.ofNat 32 16)) := by
  simp only [concAddr]
  exact effAddr_alias_beispiel

/-- BRIDGE to the selected address forms: on a base-plus-disp32 form
    the op address IS the selected `adrEff` (accepted
    `adrEff_basisForm`, symmetric). -/
theorem concAddr_basisForm (s : Zustand) (b : Breite) (dst base : Register)
    (disp : BitVec 32) (n : Adresse) :
    concAddr s (.load b dst base disp) = adrEff s n (basisForm base disp) := by
  simp only [concAddr]
  exact (adrEff_basisForm s base disp n).symm

/-- Store-side bridge: same selected form, store op. -/
theorem concAddr_store_basisForm (s : Zustand) (b : Breite)
    (base src : Register) (disp : BitVec 32) (n : Adresse) :
    concAddr s (.store b base src disp) = adrEff s n (basisForm base disp) := by
  simp only [concAddr]
  exact (adrEff_basisForm s base disp n).symm

/-! ## 2. Byte entries: width-selected little-endian issue lists.

  A store of width `b` issues exactly `b.bytes` canonical bytes,
  oldest first, byte `k` at `addrOff a k` carrying `wortByte v k`
  (the accepted little-endian byte). The 64-bit list IS the accepted
  `wortEintraege` group; narrower lists are its prefixes. -/

/-- Canonical byte-store entries of one width-selected store, oldest
    first. Never the SC word effect: consumers fold `issueByte` over
    this list on the shared TSO view. -/
def entriesOf (b : Breite) (a : Adresse) (v : Wort) : List TSOEintrag :=
  match b with
  | .b8 => [⟨addrOff a 0, wortByte v 0⟩]
  | .b16 => [⟨addrOff a 0, wortByte v 0⟩, ⟨addrOff a 1, wortByte v 1⟩]
  | .b32 => [⟨addrOff a 0, wortByte v 0⟩, ⟨addrOff a 1, wortByte v 1⟩, ⟨addrOff a 2, wortByte v 2⟩, ⟨addrOff a 3, wortByte v 3⟩]
  | .b64 => wortEintraege a v

/-- Byte count of one width, by matching (definitional). -/
def concBytes : Breite → Nat
  | .b8 => 1 | .b16 => 2 | .b32 => 4 | .b64 => 8

/-- The match agrees with the canonical `Breite.bytes`. -/
theorem concBytes_eq (b : Breite) : concBytes b = b.bytes := by
  cases b <;> decide

/-- Each list carries exactly its width in bytes. -/
theorem entriesOf_laenge (b : Breite) (a : Adresse) (v : Wort) :
    (entriesOf b a v).length = b.bytes := by
  have h : (entriesOf b a v).length = concBytes b := by
    cases b <;> rfl
  rw [h]
  exact concBytes_eq b

/-- The 64-bit list is the accepted word group. -/
theorem entriesOf_b64 (a : Adresse) (v : Wort) :
    entriesOf .b64 a v = wortEintraege a v := rfl

/-- Pinned bytes: the low byte travels at offset zero. -/
theorem entriesOf_b8_pin :
    entriesOf .b8 (BitVec.ofNat 64 8192) (BitVec.ofNat 64 0x01020304) = [⟨BitVec.ofNat 64 8192, BitVec.ofNat 8 4⟩] := by
  decide

/-- Every entry sits on the eight-footprint: narrow stores never
    leave the canonical footprint shape. -/
theorem entriesOf_in_fuss (b : Breite) (a : Adresse) (v : Wort)
    (e : TSOEintrag) (hm : e ∈ entriesOf b a v) : e.addr ∈ Fuss a := by
  cases b with
  | b8 =>
    simp only [entriesOf, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    subst hm
    exact fuss_mem_offset a 0 (by decide)
  | b16 =>
    simp only [entriesOf, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl
    · exact fuss_mem_offset a 0 (by decide)
    · exact fuss_mem_offset a 1 (by decide)
  | b32 =>
    simp only [entriesOf, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact fuss_mem_offset a 0 (by decide)
    · exact fuss_mem_offset a 1 (by decide)
    · exact fuss_mem_offset a 2 (by decide)
    · exact fuss_mem_offset a 3 (by decide)
  | b64 =>
    rw [entriesOf_b64] at hm
    exact worteintrag_in_fuss a v e hm

/-! ## 3. Admission and ordered issue.

  One access is admitted under the canonical-address check, the
  no-wrap range and the per-byte rights of its direction
  (accepted `kanonisch48`, `lesbarN`/`schreibbarN`). A store folds
  the accepted `issueByte` over `entriesOf` in order (oldest first);
  one refused byte fails the whole access before any register effect.
  Canonical memory is untouched throughout (buffer only). -/

/-- Full footprint admission: canonical address, no wrap, and the
    rights of the access direction. -/
def concAdmitted (m : Speicher) (a : Adresse) (b : Breite)
    (writes : Bool) : Bool :=
  kanonisch48 a && decide (a.toNat + b.bytes ≤ 2 ^ 64) &&
    (if writes then schreibbarN m a b.bytes else lesbarN m a b.bytes)

/-- Admission refuses a noncanonical address. -/
theorem concAdmitted_braucht_kanonisch (m : Speicher) (a : Adresse)
    (b : Breite) (writes : Bool) (h : kanonisch48 a = false) :
    concAdmitted m a b writes = false := by
  simp [concAdmitted, h]

/-- Admission refuses a wrapping footprint. -/
theorem concAdmitted_braucht_bereich (m : Speicher) (a : Adresse)
    (b : Breite) (writes : Bool)
    (h : decide (a.toNat + b.bytes ≤ 2 ^ 64) = false) :
    concAdmitted m a b writes = false := by
  simp [concAdmitted, h]

/-- Admission refuses a store without write rights. -/
theorem concAdmitted_braucht_schreibbar (m : Speicher) (a : Adresse)
    (b : Breite) (h : schreibbarN m a b.bytes = false) :
    concAdmitted m a b true = false := by
  simp [concAdmitted, h]

/-- Admission refuses a load without read rights. -/
theorem concAdmitted_braucht_lesbar (m : Speicher) (a : Adresse)
    (b : Breite) (h : lesbarN m a b.bytes = false) :
    concAdmitted m a b false = false := by
  simp [concAdmitted, h]

/-- Width-selected store issue on the shared TSO view: the admitted
    gate first, then the ordered byte fold. `none` is an explicit
    refusal (gate or one byte). -/
def concIssue (s : TSOZustand) (c : Nat) (b : Breite) (a : Adresse)
    (v : Wort) : Option TSOZustand :=
  match concAdmitted s.mem a b true with
  | false => none
  | true => issueListe s c (entriesOf b a v)

/-- A successful issue passed the admitted gate. -/
theorem concIssue_braucht_gate (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : concIssue s c b a v = some s') :
    concAdmitted s.mem a b true = true := by
  unfold concIssue at h
  cases hg : concAdmitted s.mem a b true with
  | false => simp [hg] at h
  | true => rfl

/-- A successful issue appends exactly its bytes, oldest first. -/
theorem concIssue_haengt_an (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : concIssue s c b a v = some s') :
    s'.puffer c = s.puffer c ++ entriesOf b a v := by
  unfold concIssue at h
  cases hg : concAdmitted s.mem a b true with
  | false => simp [hg] at h
  | true =>
    simp [hg] at h
    exact issueListe_haengt_an s s' c _ h

/-- A store issue changes no canonical byte (buffer only). -/
theorem concIssue_kein_speicher (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : concIssue s c b a v = some s') (x : Adresse) :
    s'.mem.bytes x = s.mem.bytes x := by
  unfold concIssue at h
  cases hg : concAdmitted s.mem a b true with
  | false => simp [hg] at h
  | true =>
    simp [hg] at h
    exact issueListe_kein_speicher s s' c _ h x

/-- A folded issue preserves all permission maps. -/
theorem issueListe_berechtigungen (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s') :
    s'.mem.lesbar = s.mem.lesbar ∧ s'.mem.schreibbar = s.mem.schreibbar ∧
      s'.mem.ausfuehrbar = s.mem.ausfuehrbar := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      have hp := issue_erhaelt_berechtigungen s s1 c e.addr e.wert h1
      have ihr := ih s1 s' h
      exact ⟨by rw [ihr.1, hp.1], by rw [ihr.2.1, hp.2.1], by rw [ihr.2.2, hp.2.2]⟩

/-- A store issue preserves all permission maps. -/
theorem concIssue_berechtigungen (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : concIssue s c b a v = some s') :
    s'.mem.lesbar = s.mem.lesbar ∧ s'.mem.schreibbar = s.mem.schreibbar ∧
      s'.mem.ausfuehrbar = s.mem.ausfuehrbar := by
  unfold concIssue at h
  cases hg : concAdmitted s.mem a b true with
  | false => simp [hg] at h
  | true =>
    simp [hg] at h
    exact issueListe_berechtigungen s s' c _ h

/-! ## 4. Forwarding-aware loads.

  Every footprint byte goes through the accepted `loadByte`
  (youngest-own forwarding, explicit refusal without read rights),
  assembled little-endian exactly like the accepted sequential reads
  (`read8`/`read16`/`read32`/`bytesWort`). The admitted gate runs
  first, on pre-state rights: a fault refuses with no state change. -/

/-- Width-selected forwarding-aware load on the shared TSO view. -/
def concLoad (s : TSOZustand) (c : Nat) (b : Breite)
    (a : Adresse) : Option Wort :=
  match concAdmitted s.mem a b false with
  | false => none
  | true =>
    match b with
    | .b8 =>
      match loadByte s c a with
      | some w0 => some (BitVec.ofNat 64 w0.toNat)
      | none => none
    | .b16 =>
      match loadByte s c a, loadByte s c (addrOff a 1) with
      | some w0, some w1 =>
        some (BitVec.ofNat 64 (w0.toNat + w1.toNat * 256))
      | _, _ => none
    | .b32 =>
      match loadByte s c a, loadByte s c (addrOff a 1),
          loadByte s c (addrOff a 2), loadByte s c (addrOff a 3) with
      | some w0, some w1, some w2, some w3 =>
        some (BitVec.ofNat 64 (w0.toNat + w1.toNat * 256 +
          w2.toNat * 65536 + w3.toNat * 16777216))
      | _, _, _, _ => none
    | .b64 =>
      match loadByte s c a, loadByte s c (addrOff a 1),
          loadByte s c (addrOff a 2), loadByte s c (addrOff a 3),
          loadByte s c (addrOff a 4), loadByte s c (addrOff a 5),
          loadByte s c (addrOff a 6), loadByte s c (addrOff a 7) with
      | some w0, some w1, some w2, some w3,
        some w4, some w5, some w6, some w7 =>
        some (BitVec.ofNat 64 (w0.toNat + w1.toNat * 256 +
          w2.toNat * 65536 + w3.toNat * 16777216 +
          w4.toNat * 4294967296 + w5.toNat * 1099511627776 +
          w6.toNat * 281474976710656 + w7.toNat * 72057594037927936))
      | _, _, _, _, _, _, _, _ => none

/-- A successful load passed the admitted gate. -/
theorem concLoad_braucht_gate (s : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : concLoad s c b a = some v) :
    concAdmitted s.mem a b false = true := by
  unfold concLoad at h
  cases hg : concAdmitted s.mem a b false with
  | false => simp [hg] at h
  | true => rfl

/-- A folded issue keeps canonical memory identically (not just
    byte-wise): the store sits in the buffer. -/
theorem issueListe_mem (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s') :
    s'.mem = s.mem := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    rfl
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      have hm1 : s1.mem = s.mem := by
        unfold issueByte at h1
        by_cases hc : s.mem.schreibbar e.addr = true
        · rw [if_pos hc] at h1
          cases h1
          rfl
        · have hc' : s.mem.schreibbar e.addr = false := by
            cases he : s.mem.schreibbar e.addr with
            | true => simp [he] at hc
            | false => rfl
          rw [if_neg (by rw [hc']; exact Bool.false_ne_true)] at h1
          cases h1
      rw [ih s1 s' h, hm1]

/-- A store issue keeps canonical memory identically. -/
theorem concIssue_mem (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (h : concIssue s c b a v = some s') :
    s'.mem = s.mem := by
  unfold concIssue at h
  cases hg : concAdmitted s.mem a b true with
  | false => simp [hg] at h
  | true =>
    simp [hg] at h
    exact issueListe_mem s s' c _ h

/-- The admitted gate is stable across a store issue (memory maps
    are untouched, address checks do not read memory). -/
theorem concAdmitted_issue_stabil (s s' : TSOZustand) (c : Nat)
    (b b2 : Breite) (a a2 : Adresse) (v : Wort) (writes : Bool)
    (h : concIssue s c b a v = some s')
    (hg : concAdmitted s.mem a2 b2 writes = true) :
    concAdmitted s'.mem a2 b2 writes = true := by
  have hm := concIssue_mem s s' c b a v h
  rw [hm]
  exact hg

/-- One admitted byte is readable: the permission fold grants every
    footprint byte below its length. -/
theorem lesbarN_byte (m : Speicher) (a : Adresse) (n k : Nat)
    (h : lesbarN m a n = true) (hk : k < n) :
    m.lesbar (addrOff a k) = true := by
  induction n generalizing k with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    have h2 : lesbarN m a n = true ∧ m.lesbar (addrOff a n) = true := by
      have e : lesbarN m a (n + 1) = (lesbarN m a n && m.lesbar (addrOff a n)) := rfl
      rw [e, Bool.and_eq_true] at h
      exact h
    by_cases hkk : k = n
    · subst hkk
      exact h2.2
    · exact ih k h2.1 (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkk)

/-- The load gate carries read rights. -/
theorem concAdmitted_lesbar (m : Speicher) (a : Adresse) (b : Breite)
    (h : concAdmitted m a b false = true) : lesbarN m a b.bytes = true := by
  have h2 := h
  unfold concAdmitted at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨_, _⟩, hrights⟩ := h2
  simpa using hrights

/-- The store gate carries write rights. -/
theorem concAdmitted_schreibbar (m : Speicher) (a : Adresse) (b : Breite)
    (h : concAdmitted m a b true = true) :
    schreibbarN m a b.bytes = true := by
  have h2 := h
  unfold concAdmitted at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨_, _⟩, hrights⟩ := h2
  simpa using hrights

/-- Buffer resolution: over the exact width-selected entry list, every
    footprint byte resolves to its canonical little-endian byte. -/
theorem neuestens_entriesOf (b : Breite) (a : Adresse) (v : Wort)
    (k : Nat) (hk : k < b.bytes) :
    neuestens (entriesOf b a v) (addrOff a k) = some (wortByte v k) := by
  cases b with
  | b8 =>
    have hb : Breite.b8.bytes = 1 := by decide
    have hk0 : k = 0 := by omega
    subst hk0
    simp [entriesOf, neuestens]
  | b16 =>
    have hb : Breite.b16.bytes = 2 := by decide
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · have d : addrOff a 1 ≠ addrOff a 0 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      simp only [entriesOf, neuestens]
      rw [if_neg d]
      rfl
    · have d : addrOff a 0 ≠ addrOff a 1 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      simp only [entriesOf, neuestens]
      rw [if_neg d]
      rfl
  | b32 =>
    have hb : Breite.b32.bytes = 4 := by decide
    have hk0123 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk0123 with rfl | rfl | rfl | rfl
    · have d1 : addrOff a 1 ≠ addrOff a 0 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d2 : addrOff a 2 ≠ addrOff a 0 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d3 : addrOff a 3 ≠ addrOff a 0 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      simp only [entriesOf, neuestens]
      rw [if_neg d3, if_neg d2, if_neg d1]
      rfl
    · have d0 : addrOff a 0 ≠ addrOff a 1 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d2 : addrOff a 2 ≠ addrOff a 1 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d3 : addrOff a 3 ≠ addrOff a 1 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      simp only [entriesOf, neuestens]
      rw [if_neg d3, if_neg d2, if_neg d0]
      rfl
    · have d0 : addrOff a 0 ≠ addrOff a 2 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d1 : addrOff a 1 ≠ addrOff a 2 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d3 : addrOff a 3 ≠ addrOff a 2 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      simp only [entriesOf, neuestens]
      rw [if_neg d3, if_neg d1, if_neg d0]
      rfl
    · have d0 : addrOff a 0 ≠ addrOff a 3 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d1 : addrOff a 1 ≠ addrOff a 3 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      have d2 : addrOff a 2 ≠ addrOff a 3 :=
        addrOff_ne8 (by decide) (by decide) (by decide)
      simp only [entriesOf, neuestens]
      rw [if_neg d2, if_neg d1, if_neg d0]
      rfl
  | b64 =>
    have hb : Breite.b64.bytes = 8 := by decide
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
        k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    have g : ∀ i j : Nat, i < 8 → j < 8 → i ≠ j →
        addrOff a i ≠ addrOff a j :=
      fun i j hi hj hij => addrOff_ne8 hi hj hij
    rcases hkk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 0 (by decide) (by decide) (by decide)),
        if_neg (g 6 0 (by decide) (by decide) (by decide)),
        if_neg (g 5 0 (by decide) (by decide) (by decide)),
        if_neg (g 4 0 (by decide) (by decide) (by decide)),
        if_neg (g 3 0 (by decide) (by decide) (by decide)),
        if_neg (g 2 0 (by decide) (by decide) (by decide)),
        if_neg (g 1 0 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 1 (by decide) (by decide) (by decide)),
        if_neg (g 6 1 (by decide) (by decide) (by decide)),
        if_neg (g 5 1 (by decide) (by decide) (by decide)),
        if_neg (g 4 1 (by decide) (by decide) (by decide)),
        if_neg (g 3 1 (by decide) (by decide) (by decide)),
        if_neg (g 2 1 (by decide) (by decide) (by decide)),
        if_neg (g 0 1 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 2 (by decide) (by decide) (by decide)),
        if_neg (g 6 2 (by decide) (by decide) (by decide)),
        if_neg (g 5 2 (by decide) (by decide) (by decide)),
        if_neg (g 4 2 (by decide) (by decide) (by decide)),
        if_neg (g 3 2 (by decide) (by decide) (by decide)),
        if_neg (g 1 2 (by decide) (by decide) (by decide)),
        if_neg (g 0 2 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 3 (by decide) (by decide) (by decide)),
        if_neg (g 6 3 (by decide) (by decide) (by decide)),
        if_neg (g 5 3 (by decide) (by decide) (by decide)),
        if_neg (g 4 3 (by decide) (by decide) (by decide)),
        if_neg (g 2 3 (by decide) (by decide) (by decide)),
        if_neg (g 1 3 (by decide) (by decide) (by decide)),
        if_neg (g 0 3 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 4 (by decide) (by decide) (by decide)),
        if_neg (g 6 4 (by decide) (by decide) (by decide)),
        if_neg (g 5 4 (by decide) (by decide) (by decide)),
        if_neg (g 3 4 (by decide) (by decide) (by decide)),
        if_neg (g 2 4 (by decide) (by decide) (by decide)),
        if_neg (g 1 4 (by decide) (by decide) (by decide)),
        if_neg (g 0 4 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 5 (by decide) (by decide) (by decide)),
        if_neg (g 6 5 (by decide) (by decide) (by decide)),
        if_neg (g 4 5 (by decide) (by decide) (by decide)),
        if_neg (g 3 5 (by decide) (by decide) (by decide)),
        if_neg (g 2 5 (by decide) (by decide) (by decide)),
        if_neg (g 1 5 (by decide) (by decide) (by decide)),
        if_neg (g 0 5 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 7 6 (by decide) (by decide) (by decide)),
        if_neg (g 5 6 (by decide) (by decide) (by decide)),
        if_neg (g 4 6 (by decide) (by decide) (by decide)),
        if_neg (g 3 6 (by decide) (by decide) (by decide)),
        if_neg (g 2 6 (by decide) (by decide) (by decide)),
        if_neg (g 1 6 (by decide) (by decide) (by decide)),
        if_neg (g 0 6 (by decide) (by decide) (by decide))]
      rfl
    · simp only [entriesOf_b64, wortEintraege, neuestens]
      rw [if_neg (g 6 7 (by decide) (by decide) (by decide)),
        if_neg (g 5 7 (by decide) (by decide) (by decide)),
        if_neg (g 4 7 (by decide) (by decide) (by decide)),
        if_neg (g 3 7 (by decide) (by decide) (by decide)),
        if_neg (g 2 7 (by decide) (by decide) (by decide)),
        if_neg (g 1 7 (by decide) (by decide) (by decide)),
        if_neg (g 0 7 (by decide) (by decide) (by decide))]
      rfl

/-- Without a pending entry the forwarding load IS the sequential
    width-indexed read: no SC effect is substituted, the buffered and
    the sequential access coincide exactly where no forwarding applies
    (accepted `load_ohne_eintrag`, per byte). -/
theorem concLoad_ohne_eintrag (s : TSOZustand) (c : Nat) (b : Breite)
    (a : Adresse)
    (hmiss : ∀ k, k < b.bytes → neuestens (s.puffer c) (addrOff a k) = none)
    (hgate : concAdmitted s.mem a b false = true) :
    concLoad s c b a = readBreite s.mem b a := by
  cases b with
  | b8 =>
    have hb : Breite.b8.bytes = 1 := by decide
    have hrd := concAdmitted_lesbar s.mem a .b8 hgate
    rw [hb] at hrd
    have hb0 : s.mem.lesbar (addrOff a 0) = true :=
      lesbarN_byte s.mem a 1 0 hrd (by decide)
    have hl0 : loadByte s c a = some (s.mem.bytes a) := by
      have h0 := load_ohne_eintrag s c (addrOff a 0) (hmiss 0 (by decide)) hb0
      rwa [addrOff_null] at h0
    simp only [concLoad, hgate, hl0, readBreite, read8]
    rw [if_pos hrd]
  | b16 =>
    have hb : Breite.b16.bytes = 2 := by decide
    have hrd := concAdmitted_lesbar s.mem a .b16 hgate
    rw [hb] at hrd
    have hb0 : s.mem.lesbar (addrOff a 0) = true :=
      lesbarN_byte s.mem a 2 0 hrd (by decide)
    have hb1 : s.mem.lesbar (addrOff a 1) = true :=
      lesbarN_byte s.mem a 2 1 hrd (by decide)
    have hl0 : loadByte s c a = some (s.mem.bytes a) := by
      have h0 := load_ohne_eintrag s c (addrOff a 0) (hmiss 0 (by decide)) hb0
      rwa [addrOff_null] at h0
    have hl1 : loadByte s c (addrOff a 1) = some (s.mem.bytes (addrOff a 1)) :=
      load_ohne_eintrag s c _ (hmiss 1 (by decide)) hb1
    simp only [concLoad, hgate, hl0, hl1, readBreite, read16]
    rw [if_pos hrd]
  | b32 =>
    have hb : Breite.b32.bytes = 4 := by decide
    have hrd := concAdmitted_lesbar s.mem a .b32 hgate
    rw [hb] at hrd
    have hb0 : s.mem.lesbar (addrOff a 0) = true :=
      lesbarN_byte s.mem a 4 0 hrd (by decide)
    have hb1 : s.mem.lesbar (addrOff a 1) = true :=
      lesbarN_byte s.mem a 4 1 hrd (by decide)
    have hb2 : s.mem.lesbar (addrOff a 2) = true :=
      lesbarN_byte s.mem a 4 2 hrd (by decide)
    have hb3 : s.mem.lesbar (addrOff a 3) = true :=
      lesbarN_byte s.mem a 4 3 hrd (by decide)
    have hl0 : loadByte s c a = some (s.mem.bytes a) := by
      have h0 := load_ohne_eintrag s c (addrOff a 0) (hmiss 0 (by decide)) hb0
      rwa [addrOff_null] at h0
    have hl1 : loadByte s c (addrOff a 1) = some (s.mem.bytes (addrOff a 1)) :=
      load_ohne_eintrag s c _ (hmiss 1 (by decide)) hb1
    have hl2 : loadByte s c (addrOff a 2) = some (s.mem.bytes (addrOff a 2)) :=
      load_ohne_eintrag s c _ (hmiss 2 (by decide)) hb2
    have hl3 : loadByte s c (addrOff a 3) = some (s.mem.bytes (addrOff a 3)) :=
      load_ohne_eintrag s c _ (hmiss 3 (by decide)) hb3
    simp only [concLoad, hgate, hl0, hl1, hl2, hl3, readBreite, read32]
    rw [if_pos hrd]
  | b64 =>
    have hb : Breite.b64.bytes = 8 := by decide
    have hrd := concAdmitted_lesbar s.mem a .b64 hgate
    rw [hb] at hrd
    have hles8 : lesbar8 s.mem a = true := by
      rwa [lesbarN_acht] at hrd
    have hb0 : s.mem.lesbar (addrOff a 0) = true :=
      lesbarN_byte s.mem a 8 0 hrd (by decide)
    have hb1 : s.mem.lesbar (addrOff a 1) = true :=
      lesbarN_byte s.mem a 8 1 hrd (by decide)
    have hb2 : s.mem.lesbar (addrOff a 2) = true :=
      lesbarN_byte s.mem a 8 2 hrd (by decide)
    have hb3 : s.mem.lesbar (addrOff a 3) = true :=
      lesbarN_byte s.mem a 8 3 hrd (by decide)
    have hb4 : s.mem.lesbar (addrOff a 4) = true :=
      lesbarN_byte s.mem a 8 4 hrd (by decide)
    have hb5 : s.mem.lesbar (addrOff a 5) = true :=
      lesbarN_byte s.mem a 8 5 hrd (by decide)
    have hb6 : s.mem.lesbar (addrOff a 6) = true :=
      lesbarN_byte s.mem a 8 6 hrd (by decide)
    have hb7 : s.mem.lesbar (addrOff a 7) = true :=
      lesbarN_byte s.mem a 8 7 hrd (by decide)
    have hl0 : loadByte s c a = some (s.mem.bytes a) := by
      have h0 := load_ohne_eintrag s c (addrOff a 0) (hmiss 0 (by decide)) hb0
      rwa [addrOff_null] at h0
    have hl1 : loadByte s c (addrOff a 1) = some (s.mem.bytes (addrOff a 1)) :=
      load_ohne_eintrag s c _ (hmiss 1 (by decide)) hb1
    have hl2 : loadByte s c (addrOff a 2) = some (s.mem.bytes (addrOff a 2)) :=
      load_ohne_eintrag s c _ (hmiss 2 (by decide)) hb2
    have hl3 : loadByte s c (addrOff a 3) = some (s.mem.bytes (addrOff a 3)) :=
      load_ohne_eintrag s c _ (hmiss 3 (by decide)) hb3
    have hl4 : loadByte s c (addrOff a 4) = some (s.mem.bytes (addrOff a 4)) :=
      load_ohne_eintrag s c _ (hmiss 4 (by decide)) hb4
    have hl5 : loadByte s c (addrOff a 5) = some (s.mem.bytes (addrOff a 5)) :=
      load_ohne_eintrag s c _ (hmiss 5 (by decide)) hb5
    have hl6 : loadByte s c (addrOff a 6) = some (s.mem.bytes (addrOff a 6)) :=
      load_ohne_eintrag s c _ (hmiss 6 (by decide)) hb6
    have hl7 : loadByte s c (addrOff a 7) = some (s.mem.bytes (addrOff a 7)) :=
      load_ohne_eintrag s c _ (hmiss 7 (by decide)) hb7
    simp only [concLoad, hgate, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7,
      readBreite, read64, bytesWort, readBytes, addrOff_null,
      show ((0 : Fin 8).val) = 0 from rfl,
      show ((1 : Fin 8).val) = 1 from rfl,
      show ((2 : Fin 8).val) = 2 from rfl,
      show ((3 : Fin 8).val) = 3 from rfl,
      show ((4 : Fin 8).val) = 4 from rfl,
      show ((5 : Fin 8).val) = 5 from rfl,
      show ((6 : Fin 8).val) = 6 from rfl,
      show ((7 : Fin 8).val) = 7 from rfl]
    rw [if_pos hles8]

/-- One forwarded byte: after a width-selected issue from an empty
    own buffer, every footprint byte loads its canonical
    little-endian byte on the issuing core. -/
theorem loadByte_nach_concIssue_leer (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort) (k : Nat) (hk : k < b.bytes)
    (hleer : s.puffer c = [])
    (hissue : concIssue s c b a v = some s')
    (hrd : lesbarN s.mem a b.bytes = true) :
    loadByte s' c (addrOff a k) = some (wortByte v k) := by
  have hbuf : s'.puffer c = entriesOf b a v := by
    have ha := concIssue_haengt_an s s' c b a v hissue
    rw [hleer, List.nil_append] at ha
    exact ha
  have hm : s'.mem = s.mem := concIssue_mem s s' c b a v hissue
  have hles : s'.mem.lesbar (addrOff a k) = true := by
    rw [hm]
    exact lesbarN_byte s.mem a b.bytes k hrd hk
  have hneu : neuestens (s'.puffer c) (addrOff a k) = some (wortByte v k) := by
    rw [hbuf]
    exact neuestens_entriesOf b a v k hk
  unfold loadByte
  rw [if_pos hles, hneu]

/-- FORWARDING: after a width-selected issue from an empty own buffer,
    the whole access loads the issued value on the issuing core --
    exactly the accepted sequential read-after-write value at every
    width (no silent narrowing, no invented byte). -/
theorem concLoad_nach_concIssue (s s' : TSOZustand) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (hleer : s.puffer c = [])
    (hissue : concIssue s c b a v = some s')
    (hgateL : concAdmitted s.mem a b false = true) :
    concLoad s' c b a =
      match b with
      | .b8 => some (BitVec.ofNat 64 (v.toNat % 256))
      | .b16 => some (BitVec.ofNat 64 (v.toNat % 65536))
      | .b32 => some (BitVec.ofNat 64 (v.toNat % 4294967296))
      | .b64 => some v := by
  have hrd := concAdmitted_lesbar s.mem a b hgateL
  have hgate' : concAdmitted s'.mem a b false = true :=
    concAdmitted_issue_stabil s s' c b b a a v false hissue hgateL
  cases b with
  | b8 =>
    have r0 := loadByte_nach_concIssue_leer s s' c .b8 a v 0
      (by decide) hleer hissue hrd
    have r0a : loadByte s' c a = some (wortByte v 0) := by
      rwa [addrOff_null] at r0
    have hg : concAdmitted s'.mem a .b8 false = true := hgate'
    simp only [concLoad, hg, r0a]
    congr 1
    apply BitVec.eq_of_toNat_eq
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  | b16 =>
    have r0 := loadByte_nach_concIssue_leer s s' c .b16 a v 0
      (by decide) hleer hissue hrd
    have r0a : loadByte s' c a = some (wortByte v 0) := by
      rwa [addrOff_null] at r0
    have r1 := loadByte_nach_concIssue_leer s s' c .b16 a v 1
      (by decide) hleer hissue hrd
    have hg : concAdmitted s'.mem a .b16 false = true := hgate'
    simp only [concLoad, hg, r0a, r1]
    congr 1
    apply BitVec.eq_of_toNat_eq
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  | b32 =>
    have r0 := loadByte_nach_concIssue_leer s s' c .b32 a v 0
      (by decide) hleer hissue hrd
    have r0a : loadByte s' c a = some (wortByte v 0) := by
      rwa [addrOff_null] at r0
    have r1 := loadByte_nach_concIssue_leer s s' c .b32 a v 1
      (by decide) hleer hissue hrd
    have r2 := loadByte_nach_concIssue_leer s s' c .b32 a v 2
      (by decide) hleer hissue hrd
    have r3 := loadByte_nach_concIssue_leer s s' c .b32 a v 3
      (by decide) hleer hissue hrd
    have hg : concAdmitted s'.mem a .b32 false = true := hgate'
    simp only [concLoad, hg, r0a, r1, r2, r3]
    congr 1
    apply BitVec.eq_of_toNat_eq
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  | b64 =>
    have r0 := loadByte_nach_concIssue_leer s s' c .b64 a v 0
      (by decide) hleer hissue hrd
    have r0a : loadByte s' c a = some (wortByte v 0) := by
      rwa [addrOff_null] at r0
    have r1 := loadByte_nach_concIssue_leer s s' c .b64 a v 1
      (by decide) hleer hissue hrd
    have r2 := loadByte_nach_concIssue_leer s s' c .b64 a v 2
      (by decide) hleer hissue hrd
    have r3 := loadByte_nach_concIssue_leer s s' c .b64 a v 3
      (by decide) hleer hissue hrd
    have r4 := loadByte_nach_concIssue_leer s s' c .b64 a v 4
      (by decide) hleer hissue hrd
    have r5 := loadByte_nach_concIssue_leer s s' c .b64 a v 5
      (by decide) hleer hissue hrd
    have r6 := loadByte_nach_concIssue_leer s s' c .b64 a v 6
      (by decide) hleer hissue hrd
    have r7 := loadByte_nach_concIssue_leer s s' c .b64 a v 7
      (by decide) hleer hissue hrd
    have hg : concAdmitted s'.mem a .b64 false = true := hgate'
    simp only [concLoad, hg, r0a, r1, r2, r3, r4, r5, r6, r7]
    congr 1
    apply BitVec.eq_of_toNat_eq
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega

/-! ## 5. Machine adapters over the canonical `HwMaschine`.

  Stores issue the pre-state source register's low bytes into the
  acting core's buffer (never the SC word effect); loads merge the
  forwarded value into the destination with the accepted
  partial-register discipline (`mergeRegNarrow`). Addresses and values
  come from the pre-state register file; flags survive every step
  (MOV/store discipline, accepted `loadNarrow_flags` /
  `storeNarrow_flags` shape); faults refuse with no successor. -/

/-- Buffer-aware integer store on the coherent machine. -/
def concStoreMaschine (m : HwMaschine) (c : Nat) (b : Breite)
    (base src : Register) (disp : BitVec 32) (len : Nat) :
    Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    let a := effAddr (projZustand m c) base disp
    match concIssue (tsoAnsicht m) c b a ((m.kerne c).register src) with
    | none => none
    | some s' => some ({ setTso m s' with kerne := fun d => if d = c then { m.kerne c with rip := ripNach (m.kerne c).rip len } else m.kerne d })

/-- A folded issue list is a reached TSO run (each byte one step). -/
theorem issueListe_erreichbar (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s') :
    TSOErreichbar s s' := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    exact .start
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      exact tsoErreichbar_trans
        (.schritt .start (.issue s s1 c e.addr e.wert h1)) (ih s1 s' h)

/-- A store keeps the flags (store discipline, no flag snapshot). -/
theorem concStoreMaschine_flags (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : concStoreMaschine m c b base src disp len = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store keeps every register (only RIP moves). -/
theorem concStoreMaschine_regs (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (q : Register)
    (h : concStoreMaschine m c b base src disp len = some m') :
    (m'.kerne c).register q = (m.kerne c).register q := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store advances RIP past its length. -/
theorem concStoreMaschine_rip (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : concStoreMaschine m c b base src disp len = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip len := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store changes no canonical byte (buffer only). -/
theorem concStoreMaschine_kein_speicher (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (x : Adresse)
    (h : concStoreMaschine m c b base src disp len = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      show s'.mem.bytes x = m.mem.bytes x
      have he := concIssue_kein_speicher (tsoAnsicht m) s' c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) hi x
      simpa [tsoAnsicht] using he

/-- A store appends exactly its bytes to the acting buffer. -/
theorem concStoreMaschine_puffer (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : concStoreMaschine m c b base src disp len = some m') :
    m'.puffer c = m.puffer c ++
      entriesOf b (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      show s'.puffer c = _
      have he := concIssue_haengt_an (tsoAnsicht m) s' c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) hi
      simpa [tsoAnsicht] using he

/-- A store preserves well-formedness (profiles untouched). -/
theorem concStoreMaschine_wf (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : concStoreMaschine m c b base src disp len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      exact hwf

/-- A store's TSO projection is reached (ordered byte steps). -/
theorem concStoreMaschine_erreichbar (m m' : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : concStoreMaschine m c b base src disp len = some m') :
    TSOErreichbar (tsoAnsicht m) (tsoAnsicht m') := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      have hg : concAdmitted (tsoAnsicht m).mem
          (effAddr (projZustand m c) base disp) b true = true :=
        concIssue_braucht_gate _ _ _ _ _ _ hi
      have hl : issueListe (tsoAnsicht m) c
          (entriesOf b (effAddr (projZustand m c) base disp)
            ((m.kerne c).register src)) = some s' := by
        have e := hi
        unfold concIssue at e
        simp [hg] at e
        exact e
      have hans : tsoAnsicht { setTso m s' with kerne := fun d => if d = c then { m.kerne c with rip := ripNach (m.kerne c).rip len } else m.kerne d } = s' := by
        cases s' with
        | mk mem puffer => rfl
      rw [hans]
      exact issueListe_erreichbar _ _ _ _ hl

/-- Buffer-aware integer load on the coherent machine. -/
def concLoadMaschine (m : HwMaschine) (c : Nat) (b : Breite)
    (dst base : Register) (disp : BitVec 32) (len : Nat) :
    Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    match concLoad (tsoAnsicht m) c b (effAddr (projZustand m c) base disp) with
    | none => none
    | some w => some ({ m with kerne := fun d => if d = c then { m.kerne c with register := regSet (m.kerne c).register dst (mergeRegNarrow b ((m.kerne c).register dst) w), rip := ripNach (m.kerne c).rip len } else m.kerne d })

/-- A load keeps the flags (MOV discipline, accepted `loadNarrow_flags`
    shape: no narrow flag snapshot is produced). -/
theorem concLoadMaschine_flags (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c b dst base disp len = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      simp

/-- A load writes the destination through the accepted architectural
    merge (`mergeRegNarrow`): 32-bit clears the upper half, 8/16-bit
    keep the unaffected bits, 64-bit is full. -/
theorem concLoadMaschine_dst (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c b dst base disp len = some m') :
    ∃ w : Wort, concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) = some w ∧
      (m'.kerne c).register dst =
        mergeRegNarrow b ((m.kerne c).register dst) w := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      exact ⟨w, rfl, by simp [regSet_gleich]⟩

/-- A load keeps every other register. -/
theorem concLoadMaschine_fremd (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (q : Register) (hq : q ≠ dst)
    (h : concLoadMaschine m c b dst base disp len = some m') :
    (m'.kerne c).register q = (m.kerne c).register q := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      simp [regSet, hq]

/-- A load advances RIP past its length. -/
theorem concLoadMaschine_rip (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c b dst base disp len = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip len := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      simp

/-- A load changes no canonical byte. -/
theorem concLoadMaschine_speicher (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (x : Adresse)
    (h : concLoadMaschine m c b dst base disp len = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      rfl

/-- A load changes no buffer. -/
theorem concLoadMaschine_puffer (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (d : Nat)
    (h : concLoadMaschine m c b dst base disp len = some m') :
    m'.puffer d = m.puffer d := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      rfl

/-- A 32-bit load clears the upper half (accepted
    `mergeRegNarrow_b32_fits`, lifted to the machine). -/
theorem concLoadMaschine_b32_clears (m m' : HwMaschine) (c : Nat)
    (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c .b32 dst base disp len = some m') :
    ((m'.kerne c).register dst).toNat < 2 ^ 32 := by
  have hd := concLoadMaschine_dst m m' c .b32 dst base disp len h
  obtain ⟨w, _, hdst⟩ := hd
  rw [hdst]
  exact mergeRegNarrow_b32_fits _ _

/-- A 64-bit load is the full forwarded word. -/
theorem concLoadMaschine_b64_full (m m' : HwMaschine) (c : Nat)
    (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c .b64 dst base disp len = some m') :
    ∃ w : Wort, concLoad (tsoAnsicht m) c .b64
        (effAddr (projZustand m c) base disp) = some w ∧
      (m'.kerne c).register dst = w := by
  have hd := concLoadMaschine_dst m m' c .b64 dst base disp len h
  obtain ⟨w, hl, hdst⟩ := hd
  exact ⟨w, hl, by rw [hdst, mergeRegNarrow_b64]⟩

/-- A load preserves well-formedness (profiles untouched). -/
theorem concLoadMaschine_wf (m m' : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c b dst base disp len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      exact hwf

/-- A bad length refuses the load on any machine. -/
theorem concLoadMaschine_laenge_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : laengeOk len = false) :
    concLoadMaschine m c b dst base disp len = none := by
  unfold concLoadMaschine
  simp [h]

/-- A bad length refuses the store on any machine. -/
theorem concStoreMaschine_laenge_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : laengeOk len = false) :
    concStoreMaschine m c b base src disp len = none := by
  unfold concStoreMaschine
  simp [h]

/-- A refused gate refuses the load: pre-fault order, no successor. -/
theorem concLoadMaschine_gate_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (dst base : Register) (disp : BitVec 32) (len : Nat)
    (hok : laengeOk len = true)
    (hgate : concLoad (tsoAnsicht m) c b
      (effAddr (projZustand m c) base disp) = none) :
    concLoadMaschine m c b dst base disp len = none := by
  unfold concLoadMaschine
  simp [hok, hgate]

/-- A refused gate refuses the store: pre-fault order, no successor. -/
theorem concStoreMaschine_gate_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (base src : Register) (disp : BitVec 32) (len : Nat)
    (hok : laengeOk len = true)
    (hgate : concIssue (tsoAnsicht m) c b
      (effAddr (projZustand m c) base disp)
      ((m.kerne c).register src) = none) :
    concStoreMaschine m c b base src disp len = none := by
  unfold concStoreMaschine
  simp [hok, hgate]

/-! ## 6. Word discipline: groups, never alignment alone.

  A 64-bit issue from an empty, foreign-free buffer establishes the
  accepted `WortGruppe` (exact eight-entry list plus foreign-footprint
  freedom over the REAL buffers). The unsplit read-back then goes
  through the accepted grouped-drain proofs -- plain and with real
  cross-core interleavings -- and LOCK stays refused on grouped states.
  Alignment alone never groups (accepted `ausrichtung_reicht_nicht`;
  byte drains are alignment-agnostic by construction). -/

/-- A folded issue touches no other core's buffer. -/
theorem issueListe_anderer_kern (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (d : Nat) (hne : d ≠ c)
    (h : issueListe s c l = some s') :
    s'.puffer d = s.puffer d := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    rfl
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      rw [ih s1 s' h]
      exact issue_anderer_kern s s1 c e.addr e.wert h1 hne

/-- A 64-bit issue from an empty, foreign-free buffer establishes the
    accepted word group: the exact eight canonical entries with no
    foreign footprint entry. -/
theorem concIssue_b64_gruppe (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hleer : s.puffer c = [])
    (hff : FremdFrei s c a)
    (hissue : concIssue s c .b64 a v = some s') :
    WortGruppe s' c a v := by
  have hg := concIssue_braucht_gate s s' c .b64 a v hissue
  have hl : issueListe s c (entriesOf .b64 a v) = some s' := by
    have e := hissue
    unfold concIssue at e
    simp [hg] at e
    exact e
  have hbuf : s'.puffer c = wortEintraege a v := by
    have ha := issueListe_haengt_an s s' c _ hl
    rw [hleer, List.nil_append, entriesOf_b64] at ha
    exact ha
  refine ⟨hbuf, ?_⟩
  intro d hne e he
  have hsame : s'.puffer d = s.puffer d :=
    issueListe_anderer_kern s s' c _ d hne hl
  rw [hsame] at he
  exact hff d hne e he

/-- GROUPED READ-BACK through our issue: an exclusion-checked drain
    from the issued group installs the whole word unsplit in canonical
    memory (accepted `wort_gruppe_liest_zurueck`, group from our
    bytes). Every premise is used. -/
theorem concWort_liest_zurueck (s s' sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hleer : s.puffer c = [])
    (hff : FremdFrei s c a)
    (hissue : concIssue s c .b64 a v = some s')
    (hles : lesbar8 s'.mem a = true)
    (hspur : DrainSpur c s' sN t) (hend : sN ∈ t)
    (hleerN : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FremdFrei x c a) :
    read64 sN.mem a = some v :=
  wort_gruppe_liest_zurueck s' sN t c a v
    (concIssue_b64_gruppe s s' c a v hleer hff hissue)
    hles hspur hend hleerN hstoer

/-- INTERLEAVED READ-BACK through our issue: the grouped word reads
    back unsplit across a drain trace with real foreign accesses,
    exclusion derived from finite per-state checks (accepted
    `verflochten_liest_zurueck`, group from our bytes). -/
theorem concWort_verflochten_liest (s s' sN : TSOZustand)
    (t : List TSOZustand) (a : Adresse) (v : Wort)
    (hleer : s.puffer 0 = [])
    (hff : FremdFrei s 0 a)
    (hissue : concIssue s 0 .b64 a v = some s')
    (hles : lesbar8 s'.mem a = true)
    (hspur : DrainSpur 0 s' sN t) (hend : sN ∈ t)
    (hleerN : sN.puffer 0 = [])
    (h1 : ∀ x ∈ t, ∀ e ∈ x.puffer 1, e.addr ∉ Fuss a)
    (hRest : ∀ x ∈ t, ∀ d : Nat, d ≠ 0 → d ≠ 1 → x.puffer d = []) :
    read64 sN.mem a = some v :=
  verflochten_liest_zurueck s' sN t a v
    (concIssue_b64_gruppe s s' 0 a v hleer hff hissue)
    hles hspur hend hleerN h1 hRest

/-- LOCK stays refused on our grouped states (accepted
    `gruppe_verweigert_lock`, group from our bytes). -/
theorem concGruppe_verweigert_lock (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v delta : Wort)
    (hleer : s.puffer c = [])
    (hff : FremdFrei s c a)
    (hissue : concIssue s c .b64 a v = some s') :
    lockSchritt (.xadd64 a delta) c s' = none :=
  gruppe_verweigert_lock s' c a v delta
    (concIssue_b64_gruppe s s' c a v hleer hff hissue)

/-- A single folded issue is a reached TSO run element: one byte is
    one `issueByte` step (accepted shape, youngest-last order). -/
theorem issueListe_einzeln (s s' : TSOZustand) (c : Nat) (e : TSOEintrag)
    (h : issueListe s c [e] = some s') :
    issueByte s c e.addr e.wert = some s' := by
  have hne : issueByte s c e.addr e.wert ≠ none := by
    intro hz
    unfold issueListe at h
    rw [hz] at h
    cases h
  cases he : issueByte s c e.addr e.wert with
  | none => exact absurd he hne
  | some s1 =>
    unfold issueListe at h
    rw [he] at h
    simp [issueListe] at h
    subst h
    rfl

/-! ## 7. Byte codec boundary: admitted rows and pending widths.

  `concDecode` admits EXACTLY the accepted byte producers for memory
  forms: the pilot `load64`/`store64` rows (accepted `decode`, via
  `roundtrip_load64`/`roundtrip_store64`) where the pilot accepts,
  and the narrow `store32` row (accepted `decodeNarrow`, via
  `roundtrip_store32` plus `narrow_pilot_verweigert`) where the pilot
  refuses. Register-only rows (`mov32rr` and the other accepted
  narrow/integer rows) are not memory accesses and refuse here; 8/16-bit
  memory rows have no accepted producer and stay an explicit PENDING
  extension -- nothing is reinvented or assumed (see `CUTS`). -/

/-- Byte decode to a width-selected memory op with its consumed
    length: pilot 64-bit rows first, the narrow 32-bit store only
    where the pilot refuses. -/
def concDecode (bs : List Byte) : Option (ConcIntOp × Nat) :=
  match decode bs with
  | some (d, _) =>
    match d.befehl with
    | .store64 base src disp => some (.store .b64 base src disp, d.laenge)
    | .load64 dst base disp => some (.load .b64 dst base disp, d.laenge)
    | _ => none
  | none =>
    match decodeNarrow bs with
    | some (n, _) =>
      match n.op with
      | .store32 base src disp => some (.store .b32 base src disp, n.laenge)
      | _ => none
    | none => none

/-- Pilot 64-bit stores decode through (accepted round trip). -/
theorem concDecode_store64 (base src : Register) (d : BitVec 32)
    (suffix : List Byte) :
    concDecode (encode (.store64 base src d) ++ suffix) =
      some ((.store .b64 base src d), (encode (.store64 base src d)).length) := by
  have h := roundtrip_store64 base src d suffix
  unfold concDecode
  rw [h]

/-- Pilot 64-bit loads decode through (accepted round trip). -/
theorem concDecode_load64 (dst base : Register) (d : BitVec 32)
    (suffix : List Byte) :
    concDecode (encode (.load64 dst base d) ++ suffix) =
      some ((.load .b64 dst base d), (encode (.load64 dst base d)).length) := by
  have h := roundtrip_load64 dst base d suffix
  unfold concDecode
  rw [h]

/-- Narrow 32-bit stores decode through where the pilot refuses
    (accepted narrow round trip plus pilot disjointness). -/
theorem concDecode_store32 (base src : Register) (d : BitVec 32)
    (suffix : List Byte) :
    concDecode (encodeNarrow (.store32 base src d) ++ suffix) =
      some ((.store .b32 base src d),
        (encodeNarrow (.store32 base src d)).length) := by
  have hp := narrow_pilot_verweigert (.store32 base src d) suffix
  have hn := roundtrip_store32 base src d suffix
  unfold concDecode
  rw [hp, hn]

/-- Register-only rows are not memory accesses: the 32-bit move
    refuses (accepted rows on both sides). -/
theorem concDecode_mov32rr_verweigert (dst src : Register)
    (suffix : List Byte) :
    concDecode (encodeNarrow (.mov32rr dst src) ++ suffix) = none := by
  have hp := narrow_pilot_verweigert (.mov32rr dst src) suffix
  have hn := roundtrip_mov32rr dst src suffix
  unfold concDecode
  rw [hp, hn]

/-- COVERAGE: every successful decode is a 64-bit pilot load/store or
    the narrow 32-bit store. In particular no 8/16-bit memory row
    decodes here: those widths have no accepted producer and stay
    PENDING (not reinvented, not assumed). -/
theorem concDecode_nur_b64_b32 (bs : List Byte) (op : ConcIntOp)
    (l : Nat) (h : concDecode bs = some (op, l)) :
    (∃ base src disp, op = .store .b64 base src disp) ∨
    (∃ dst base disp, op = .load .b64 dst base disp) ∨
    (∃ base src disp, op = .store .b32 base src disp) := by
  unfold concDecode at h
  cases hd : decode bs with
  | none =>
    simp [hd] at h
    cases hn : decodeNarrow bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, rest⟩ := p
      simp [hn] at h
      cases hop : n.op with
      | mov32rr dst src => simp [hop] at h
      | movzx8 dst src => simp [hop] at h
      | movsx8 dst src => simp [hop] at h
      | store32 base src disp =>
        simp [hop] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (Or.inr ⟨base, src, disp, rfl⟩)
  | some q =>
    obtain ⟨d, rest⟩ := q
    simp [hd] at h
    cases hb : d.befehl with
    | movImm64 dst v => simp [hb] at h
    | movReg64 dst src => simp [hb] at h
    | addReg64 dst src => simp [hb] at h
    | subReg64 dst src => simp [hb] at h
    | xorReg64 dst src => simp [hb] at h
    | cmpReg64 lhs rhs => simp [hb] at h
    | load64 dst base disp =>
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨dst, base, disp, rfl⟩)
    | store64 base src disp =>
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨base, src, disp, rfl⟩
    | jump32 disp => simp [hb] at h
    | jumpIf32 c disp => simp [hb] at h
    | call32 disp => simp [hb] at h
    | push64 src => simp [hb] at h
    | pop64 dst => simp [hb] at h
    | ret => simp [hb] at h

/-- Every decoded length passes the length guard: pilot via the
    accepted `decode_abdeckung`, narrow via `decodeNarrow_abdeckung`. -/
theorem concDecode_laenge_ok (bs : List Byte) (op : ConcIntOp)
    (l : Nat) (h : concDecode bs = some (op, l)) :
    laengeOk l = true := by
  unfold concDecode at h
  cases hd : decode bs with
  | none =>
    simp [hd] at h
    cases hn : decodeNarrow bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, rest⟩ := p
      simp [hn] at h
      cases hop : n.op with
      | mov32rr dst src => simp [hop] at h
      | movzx8 dst src => simp [hop] at h
      | movsx8 dst src => simp [hop] at h
      | store32 base src disp =>
        simp [hop] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (decodeNarrow_abdeckung bs n rest hn).2.1
  | some q =>
    obtain ⟨d, rest⟩ := q
    simp [hd] at h
    cases hb : d.befehl with
    | movImm64 dst v => simp [hb] at h
    | movReg64 dst src => simp [hb] at h
    | addReg64 dst src => simp [hb] at h
    | subReg64 dst src => simp [hb] at h
    | xorReg64 dst src => simp [hb] at h
    | cmpReg64 lhs rhs => simp [hb] at h
    | load64 dst base disp =>
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (decode_abdeckung bs d rest hd).2.1
    | store64 base src disp =>
      simp [hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (decode_abdeckung bs d rest hd).2.1
    | jump32 disp => simp [hb] at h
    | jumpIf32 c disp => simp [hb] at h
    | call32 disp => simp [hb] at h
    | push64 src => simp [hb] at h
    | pop64 dst => simp [hb] at h
    | ret => simp [hb] at h

/-- One observed byte: a successful 8-bit load observed its byte
    through the accepted `loadByte`. -/
theorem concLoad_b8_beobachtet (s : TSOZustand) (c : Nat)
    (a : Adresse) (w : Wort) (h : concLoad s c .b8 a = some w) :
    ∃ w0 : Byte, loadByte s c a = some w0 := by
  have hg := concLoad_braucht_gate s c .b8 a w h
  have e := h
  unfold concLoad at e
  simp [hg] at e
  cases he : loadByte s c a with
  | none => simp [he] at e
  | some w0 => exact ⟨w0, rfl⟩

/-- A successful 8-bit machine load observed its byte as a canonical
    `HwSchritt.lade` event (self-loop, no state change). -/
theorem concLoadMaschine_b8_lade (m m' : HwMaschine) (c : Nat)
    (dst base : Register) (disp : BitVec 32) (len : Nat)
    (h : concLoadMaschine m c .b8 dst base disp len = some m') :
    ∃ w0 : Byte,
      loadByte (tsoAnsicht m) c (effAddr (projZustand m c) base disp) =
        some w0 ∧
      HwSchritt m m
        (.leseBeob c (effAddr (projZustand m c) base disp) w0) := by
  unfold concLoadMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c .b8
        (effAddr (projZustand m c) base disp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      obtain ⟨w0, hw0⟩ := concLoad_b8_beobachtet (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) w hl
      exact ⟨w0, hw0, .lade c _ w0 hw0⟩

/-- A successful 8-bit machine store issued its byte as a canonical
    `HwSchritt.gibAus` event on the shared TSO view. -/
theorem concStoreMaschine_b8_gibAus (m m' : HwMaschine) (c : Nat)
    (base src : Register) (disp : BitVec 32) (len : Nat)
    (h : concStoreMaschine m c .b8 base src disp len = some m') :
    ∃ s' : TSOZustand,
      issueByte (tsoAnsicht m) c
        (addrOff (effAddr (projZustand m c) base disp) 0)
        (wortByte ((m.kerne c).register src) 0) = some s' ∧
      HwSchritt m (setTso m s')
        (.schreibAusgabe c
          (addrOff (effAddr (projZustand m c) base disp) 0)
          (wortByte ((m.kerne c).register src) 0)) ∧
      tsoAnsicht m' = s' := by
  unfold concStoreMaschine at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c .b8
        (effAddr (projZustand m c) base disp)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s0 =>
      simp [hi] at h
      cases h
      have hg := concIssue_braucht_gate _ _ _ _ _ _ hi
      have he2 : issueListe (tsoAnsicht m) c
          [⟨addrOff (effAddr (projZustand m c) base disp) 0,
            wortByte ((m.kerne c).register src) 0⟩] = some s0 := by
        have e := hi
        unfold concIssue at e
        simp [hg] at e
        exact e
      have h1 := issueListe_einzeln _ _ _ _ he2
      refine ⟨s0, h1, .gibAus c _ _ s0 h1, ?_⟩
      cases s0 with
      | mk mem puffer => rfl

/-- Ordered drain of the acting core's oldest entry into shared
    memory: the accepted `flushKern` on the shared TSO view, with its
    buffer head as the event. -/
def concDrain (m : HwMaschine) (c : Nat) :
    Option (HwMaschine × TSOEintrag) :=
  match flushKern (tsoAnsicht m) c with
  | none => none
  | some s' =>
    match (m.puffer c).head? with
    | none => none
    | some e => some (setTso m s', e)

/-- A drain is a canonical `HwSchritt.spüle` event and installs the
    buffer head into shared memory (accepted `flush_schreibt_kopf`). -/
theorem concDrain_spuele (m : HwMaschine) (c : Nat)
    (m' : HwMaschine) (e : TSOEintrag)
    (h : concDrain m c = some (m', e)) :
    HwSchritt m m' (.spülung c e) ∧ m'.mem.bytes e.addr = e.wert := by
  unfold concDrain at h
  cases hf : flushKern (tsoAnsicht m) c with
  | none => simp [hf] at h
  | some s' =>
    simp only [hf] at h
    obtain ⟨e', he'⟩ : ∃ e', (m.puffer c).head? = some e' := by
      cases heq : (m.puffer c).head? with
      | none => simp [heq] at h
      | some e' => exact ⟨e', rfl⟩
    simp [he'] at h
    obtain ⟨hmem, hee⟩ := h
    subst hmem
    subst hee
    refine ⟨.spüle c e' s' hf he', ?_⟩
    cases hpc : m.puffer c with
    | nil => simp [hpc] at he'
    | cons hd tl =>
      simp [hpc] at he'
      cases he'
      exact flush_schreibt_kopf (tsoAnsicht m) s' c hf e' tl hpc

/-- A drain preserves well-formedness (profiles untouched). -/
theorem concDrain_wf (m : HwMaschine) (c : Nat)
    (m' : HwMaschine) (e : TSOEintrag)
    (h : concDrain m c = some (m', e))
    (hwf : HwWf m) : HwWf m' := by
  unfold concDrain at h
  cases hf : flushKern (tsoAnsicht m) c with
  | none => simp [hf] at h
  | some s' =>
    simp only [hf] at h
    obtain ⟨e', he'⟩ : ∃ e', (m.puffer c).head? = some e' := by
      cases heq : (m.puffer c).head? with
      | none => simp [heq] at h
      | some e' => exact ⟨e', rfl⟩
    simp [he'] at h
    obtain ⟨hmem, hee⟩ := h
    subst hmem
    subst hee
    exact setTso_wf m s' hwf

/-! ## 8. Joint witness: two cores, real bytes, buffered store.

  Core 0 fetches a real narrow `store32 [rbx], rax` (7 bytes) from
  actual executable memory, issues it width-selected into its buffer
  (registers/flags/memory discipline as in §5), forwards it to its own
  load while core 1 still reads the old value, then drains it into
  shared memory where both cores observe it. Every claim below is a
  closed decidable observation (`decide`/`rfl`); refusals
  (fetch/permission/canonical/wrap/tearing/overlap) stand beside it. -/

/-- Witness value: `0x01020304` (low byte `0x04`). -/
def concWitV : Wort := BitVec.ofNat 64 0x01020304

/-- Witness data address. -/
def concWitA : Adresse := BitVec.ofNat 64 8192

/-- Witness image: narrow `store32 [rbx + 0], rax` (7 bytes). -/
def concWitBild : List Byte :=
  encodeNarrow (.store32 .rbx .rax (BitVec.ofNat 32 0))

/-- Witness code bytes: the image at 4096, zeroes elsewhere. -/
def concWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else match concWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness code permission: exactly the 7 image bytes. -/
def concWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4103)

/-- Witness data permission: eight bytes at 8192. -/
def concWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness shared memory: code is execute-only, data read/write. -/
def concWitMem : Speicher :=
  { bytes := concWitBytes, lesbar := concWitDaten,
    schreibbar := concWitDaten, ausfuehrbar := concWitCode }

/-- Witness core-0 registers: base in rbx, value in rax. -/
def concWitReg0 : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rax then concWitV
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs at 4096, core 1 idles on the
    (non-executable) data page. -/
def concWitKern : Nat → HwKern
  | 0 => ⟨concWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def concWitM0 : HwMaschine :=
  ⟨concWitMem, concWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed: full silicon admits all
    (same shape as the accepted `hwWitStart_wf`: every feature holds
    by `rfl`, so the admission premise is vacuous). -/
theorem concWitM0_wf : HwWf concWitM0 := by
  intro c f _
  cases f <;> rfl

/-- The fetched bytes decode to the 32-bit store through our codec
    boundary (accepted narrow row, pilot refuses). -/
theorem concWit_fetch_decode :
    concDecode (geholt (projZustand concWitM0 0)) =
      some ((.store .b32 .rbx .rax (BitVec.ofNat 32 0)), 7) := by
  decide

/-- Core 1 fetches nothing: its RIP points at non-executable memory. -/
theorem concWit_kern1_fetch_verweigert :
    concDecode (geholt (projZustand concWitM0 1)) = none := by
  decide

/-- The store address is the data cell, from pre-state registers. -/
theorem concWit_addr :
    effAddr (projZustand concWitM0 0) .rbx (BitVec.ofNat 32 0) =
      concWitA := by
  decide

/-- ALIAS: another base-plus-displacement names the same cell
    (`rax = 8176` with displacement `16`), so no injectivity is
    claimed for op addresses. -/
theorem concWit_alias :
    effAddr { projZustand concWitM0 0 with register := regSet (projZustand concWitM0 0).register Register.rax (BitVec.ofNat 64 8176) } .rax (BitVec.ofNat 32 16) = concWitA ∧ effAddr (projZustand concWitM0 0) .rbx (BitVec.ofNat 32 0) = concWitA := by
  decide

/-- The machine store advances RIP past the 7 fetched bytes. -/
theorem concWit_store_rip :
    (concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7).map (fun m => (m.kerne 0).rip) =
      some (BitVec.ofNat 64 4103) := by
  decide

/-- The machine store issues four buffer entries. -/
theorem concWit_store_buf :
    (concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7).map (fun m => (m.puffer 0).length) =
      some 4 := by
  decide

/-- The machine store leaves shared memory alone (buffer only). -/
theorem concWit_store_mem_still :
    (concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7).map (fun m => m.mem.bytes concWitA) =
      some (BitVec.ofNat 8 0) := by
  decide

/-- The machine store keeps the flags. -/
theorem concWit_store_flags :
    (concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7).map (fun m => (m.kerne 0).flags) =
      some zeugeFlags := by
  decide

/-- The machine store keeps the source register. -/
theorem concWit_store_rax :
    (concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7).map
      (fun m => (m.kerne 0).register .rax) = some concWitV := by
  decide

/-- The data cell starts zeroed: the run really changes memory. -/
theorem concWit_anfang_null :
    concWitMem.bytes concWitA = BitVec.ofNat 8 0 := by
  decide

/-- The machine after the store, projected to the shared TSO view. -/
def concWitM1 : Option HwMaschine :=
  concStoreMaschine concWitM0 0 .b32 .rbx .rax (BitVec.ofNat 32 0) 7

/-- The shared TSO state after the store issue. -/
def concWitT1 : Option TSOZustand := concWitM1.map tsoAnsicht

/-- Core 0 observes its ownissued value (forwarding). -/
def concWitLoadEigen : Option (Option Wort) :=
  concWitT1.map (fun s => concLoad s 0 .b32 concWitA)

/-- Core 1 observes the old value (no foreign forwarding). -/
def concWitLoadFremd : Option (Option Wort) :=
  concWitT1.map (fun s => concLoad s 1 .b32 concWitA)

/-- Core 0 drains its four entries, one flush per state. -/
def concWitT2 : Option TSOZustand :=
  concWitT1.bind (fun s => flushKern s 0)

def concWitT3 : Option TSOZustand :=
  concWitT2.bind (fun s => flushKern s 0)

def concWitT4 : Option TSOZustand :=
  concWitT3.bind (fun s => flushKern s 0)

def concWitT5 : Option TSOZustand :=
  concWitT4.bind (fun s => flushKern s 0)

/-- The shared byte after the drain. -/
def concWitNachFlush : Option (Option Byte) :=
  concWitT5.map (fun s => some (s.mem.bytes concWitA))

/-- Core 1 reads the drained value from shared memory. -/
def concWitFremdNachFlush : Option (Option Wort) :=
  concWitT5.map (fun s => concLoad s 1 .b32 concWitA)

/-- Forwarding: core 0 reads its own unflushed store. -/
theorem concWit_weiterleitung :
    concWitLoadEigen = some (some concWitV) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem concWit_fremd_alt :
    concWitLoadFremd = some (some (BitVec.ofNat 64 0)) := by
  decide

/-- The drain changes shared memory: the cell reads `0x04`. -/
theorem concWit_spuelung :
    concWitNachFlush = some (some (BitVec.ofNat 8 4)) := by
  decide

/-- After the drain core 1 observes the new value. -/
theorem concWit_fremd_neu :
    concWitFremdNachFlush = some (some concWitV) := by
  decide

/-- Dark memory: nothing readable or writable. -/
def concWitDunkel : Speicher :=
  { bytes := concWitBytes, lesbar := fun _ => false,
    schreibbar := fun _ => false, ausfuehrbar := concWitCode }

/-- Dark TSO start: dark memory, empty buffers. -/
def concWitDunkelT : TSOZustand := ⟨concWitDunkel, fun _ => []⟩

/-- PERMISSION REFUSAL: a store into dark memory is refused. -/
theorem concWit_dunkel_issue_verweigert :
    concIssue concWitDunkelT 0 .b32 concWitA concWitV = none := by
  decide

/-- PERMISSION REFUSAL: a load from dark memory is refused. -/
theorem concWit_dunkel_load_verweigert :
    concLoad concWitDunkelT 0 .b32 concWitA = none := by
  decide

/-- CANONICAL REFUSAL: the address hole admits no footprint. -/
theorem concWit_nichtkanonisch_verweigert :
    concAdmitted concWitMem (BitVec.ofNat 64 (2 ^ 47)) .b32 true =
      false := by
  decide

/-- WRAP REFUSAL: the top of the space admits no four-byte footprint. -/
theorem concWit_rand_verweigert :
    concAdmitted concWitMem (BitVec.ofNat 64 (2 ^ 64 - 2)) .b32 true =
      false := by
  decide

/-- Tearing state: two of eight bytes buffered on core 0. -/
def concWitTeil : TSOZustand :=
  ⟨concWitMem, fun d =>
    if d = 0 then (wortEintraege concWitA concWitV).take 2 else []⟩

/-- TEARING REFUSAL: two buffered bytes are no word group. -/
theorem concWitTeil_keine_gruppe :
    ¬ WortGruppe concWitTeil 0 concWitA concWitV := by
  apply hwTeilwort_keine_gruppe
  decide

/-- Overlap state: a full group on core 0, a foreign entry inside
    its footprint on core 1. -/
def concWitOverlap : TSOZustand :=
  ⟨concWitMem, fun d =>
    if d = 0 then wortEintraege concWitA concWitV
    else if d = 1 then [⟨addrOff concWitA 1, BitVec.ofNat 8 9⟩] else []⟩

/-- OVERLAP REFUSAL: the foreign footprint entry breaks the group. -/
theorem concWitOverlap_keine_gruppe :
    ¬ WortGruppe concWitOverlap 0 concWitA concWitV :=
  hwGruppe_verweigert_bei_fremdeintrag concWitOverlap 0 concWitA concWitV
    1 (by decide) ⟨addrOff concWitA 1, BitVec.ofNat 8 9⟩ (by decide)
    (fuss_mem_offset concWitA 1 (by decide))

/-- THE JOINT WITNESS: a reached two-core run that fetches real
    bytes, decodes through the codec boundary, issues a
    width-selected store (registers/flags/memory discipline),
    forwards it to the issuer, hides it from the foreign core,
    drains it into shared memory (0 becomes `0x04`, observed from
    both cores) -- beside the fetch/permission/canonical/wrap/
    tearing/overlap refusals and the address alias. Non-degenerate:
    the drain observably changes shared memory. -/
theorem concWit_zeuge :
    concDecode (geholt (projZustand concWitM0 0)) =
        some ((.store .b32 .rbx .rax (BitVec.ofNat 32 0)), 7) ∧
      effAddr (projZustand concWitM0 0) .rbx (BitVec.ofNat 32 0) =
        concWitA ∧
      concWitLoadEigen = some (some concWitV) ∧
      concWitLoadFremd = some (some (BitVec.ofNat 64 0)) ∧
      concWitMem.bytes concWitA = BitVec.ofNat 8 0 ∧
      concWitNachFlush = some (some (BitVec.ofNat 8 4)) ∧
      concWitFremdNachFlush = some (some concWitV) ∧
      concDecode (geholt (projZustand concWitM0 1)) = none ∧
      ¬ WortGruppe concWitTeil 0 concWitA concWitV ∧
      ¬ WortGruppe concWitOverlap 0 concWitA concWitV ∧
      concIssue concWitDunkelT 0 .b32 concWitA concWitV = none ∧
      concLoad concWitDunkelT 0 .b32 concWitA = none ∧
      concAdmitted concWitMem (BitVec.ofNat 64 (2 ^ 47)) .b32 true =
        false ∧
      concAdmitted concWitMem (BitVec.ofNat 64 (2 ^ 64 - 2)) .b32 true =
        false ∧
      (effAddr { projZustand concWitM0 0 with register := regSet (projZustand concWitM0 0).register Register.rax (BitVec.ofNat 64 8176) } .rax (BitVec.ofNat 32 16) = concWitA ∧ effAddr (projZustand concWitM0 0) .rbx (BitVec.ofNat 32 0) = concWitA) ∧
      (∃ m1 : HwMaschine,
        concStoreMaschine concWitM0 0 .b32 .rbx .rax
            (BitVec.ofNat 32 0) 7 = some m1 ∧
        TSOErreichbar (tsoAnsicht concWitM0) (tsoAnsicht m1) ∧
        (m1.puffer 0).length = 4 ∧
        (m1.kerne 0).rip = BitVec.ofNat 64 4103) := by
  refine ⟨concWit_fetch_decode, concWit_addr, concWit_weiterleitung,
    concWit_fremd_alt, concWit_anfang_null, concWit_spuelung,
    concWit_fremd_neu, concWit_kern1_fetch_verweigert,
    concWitTeil_keine_gruppe, concWitOverlap_keine_gruppe,
    concWit_dunkel_issue_verweigert, concWit_dunkel_load_verweigert,
    concWit_nichtkanonisch_verweigert, concWit_rand_verweigert,
    concWit_alias, ?_⟩
  cases he : concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7 with
  | none =>
    have hc := concWit_store_rip
    simp [he] at hc
  | some m1 =>
    refine ⟨m1, rfl, ?_, ?_, ?_⟩
    · exact concStoreMaschine_erreichbar concWitM0 m1 0 .b32 .rbx .rax
        (BitVec.ofNat 32 0) 7 he
    · have hp := concStoreMaschine_puffer concWitM0 m1 0 .b32 .rbx .rax
        (BitVec.ofNat 32 0) 7 he
      have h0 : concWitM0.puffer 0 = [] := rfl
      have hbytes : Breite.b32.bytes = 4 := by decide
      rw [hp, h0, List.nil_append, entriesOf_laenge, hbytes]
    · have hr := concStoreMaschine_rip concWitM0 m1 0 .b32 .rbx .rax
        (BitVec.ofNat 32 0) 7 he
      exact hr

/- CUTS:
   Proved here, layering over (never editing) the canonical machine:
   - §1 width-selected ops with the accepted pilot address
     (`concAddr_prestate`, alias, `adrEff` bridge via `basisForm`).
   - §2 canonical little-endian byte entries (`entriesOf_laenge`,
     `entriesOf_b64`, `entriesOf_in_fuss`, `entriesOf_b8_pin`).
   - §3 admission (canonical address, no wrap, per-direction rights)
     with ordered `issueByte` folds: buffer append, no canonical
     change (byte-wise and identical), permission preservation,
     gate stability, reached TSO runs, other-core buffers untouched.
   - §4 forwarding-aware loads assembled exactly like the accepted
     sequential reads: gate, byte readability, buffer resolution
     (`neuestens_entriesOf`), no-pending bridge
     (`concLoad_ohne_eintrag`: buffered = sequential where nothing
     forwards), whole-access forwarding to the accepted
     read-after-write values (`concLoad_nach_concIssue`).
   - §5 buffer-aware machine adapters with register/partial-register
     effects from the accepted equations (`mergeRegNarrow`,
     `regSet`): flags/registers/RIP/memory/buffer/well-formedness
     preservation, 32-bit clearing, 64-bit full value, pre-fault
     refusals, single-byte `HwSchritt` correspondence (load
     observation, store issue), ordered drain (`concDrain`) as
     `HwSchritt.spüle` installing the buffer head.
   - §6 word discipline through the accepted grouping proofs:
     our 64-bit issue establishes `WortGruppe`
     (`concIssue_b64_gruppe`), plain and interleaved read-back
     (`concWort_liest_zurueck`, `concWort_verflochten_liest`), LOCK
     refusal on grouped states. Alignment alone never groups
     (byte drains are alignment-agnostic; see
     `ausrichtung_reicht_nicht`, cited not redone).
   - §7 byte codec boundary: pilot 64-bit load/store and the narrow
     32-bit store decode through their accepted round trips;
     register-only rows refuse; coverage
     (`concDecode_nur_b64_b32`) shows every success is one of those
     three -- 8/16-bit memory rows have no accepted producer and stay
     PENDING, not reinvented or assumed. Decoded lengths pass
     `laengeOk` on both paths.
   - §8 joint two-core witness (`concWit_zeuge`): fetched narrow
     `store32` bytes decode through our boundary, issue
     width-selected with register/flag/memory discipline, forward to
     the issuer, hide from the foreign core, drain observably into
     shared memory (0 becomes `0x04`, both cores observe) -- beside
     fetch/permission/canonical/wrap/tearing/overlap refusals and
     the address alias. Non-degenerate: the drain observably changes
     shared memory.
   NOT proved here, and not claimed:
   - No silicon correspondence: encodings are the accepted canonical
     subsets with self-consistency only. Manual provenance
     (Intel SDM 325462-093US, clone-local
     `.tmp/HARDWARE-REFERENCES/REFERENCES.json` and
     `intel-instruction-reference.txt` headings MOV/MOVZX/MOVSX/
     ADD/SUB/TEST/LEA) is provenance, never a silicon proof.
   - No 8/16-bit (and no 32-bit load) byte codec: `concDecode`
     refuses everything outside the three admitted rows
     (`concDecode_nur_b64_b32`); each new row needs its own
     encoding, coverage and execution proof.
   - No multi-byte hardware atomicity: byte drains pass through
     visible intermediate states (`paket_reisst`,
     `wort_fuss_reisst`, `verflochten_erster_schritt_reisst`,
     cited); `WortGruppe` is a software observation discipline.
   - No source correspondence, no per-access W/GX simulation, no
     ABI/loader/entry/budget/cost claim; `verweigert`/`none` is the
     absence of a transition, never a halt claim.
   - Consumer interface: `concStoreMaschine`/`concLoadMaschine`
     (+ preservation/frame theorems), `concDrain`,
     `concIssue_b64_gruppe`, `concWort_liest_zurueck`,
     `concWort_verflochten_liest`, `concDecode`
     (+ `concDecode_nur_b64_b32`, `concDecode_laenge_ok`),
     `concWit_zeuge`.
-/

#print axioms concAddr_prestate
#print axioms concAddr_alias_beispiel
#print axioms concAddr_basisForm
#print axioms concAddr_store_basisForm
#print axioms entriesOf_laenge
#print axioms entriesOf_b64
#print axioms entriesOf_b8_pin
#print axioms entriesOf_in_fuss
#print axioms concAdmitted_braucht_kanonisch
#print axioms concAdmitted_braucht_schreibbar
#print axioms concAdmitted_lesbar
#print axioms concIssue_haengt_an
#print axioms concIssue_kein_speicher
#print axioms concIssue_berechtigungen
#print axioms concIssue_mem
#print axioms issueListe_erreichbar
#print axioms issueListe_anderer_kern
#print axioms neuestens_entriesOf
#print axioms concLoad_braucht_gate
#print axioms concLoad_ohne_eintrag
#print axioms concLoad_nach_concIssue
#print axioms loadByte_nach_concIssue_leer
#print axioms concStoreMaschine_flags
#print axioms concStoreMaschine_regs
#print axioms concStoreMaschine_rip
#print axioms concStoreMaschine_kein_speicher
#print axioms concStoreMaschine_puffer
#print axioms concStoreMaschine_wf
#print axioms concStoreMaschine_erreichbar
#print axioms concLoadMaschine_flags
#print axioms concLoadMaschine_dst
#print axioms concLoadMaschine_fremd
#print axioms concLoadMaschine_b32_clears
#print axioms concLoadMaschine_b64_full
#print axioms concLoadMaschine_wf
#print axioms concLoadMaschine_b8_lade
#print axioms concStoreMaschine_b8_gibAus
#print axioms concDrain_spuele
#print axioms concDrain_wf
#print axioms concIssue_b64_gruppe
#print axioms concWort_liest_zurueck
#print axioms concWort_verflochten_liest
#print axioms concGruppe_verweigert_lock
#print axioms concDecode_store64
#print axioms concDecode_load64
#print axioms concDecode_store32
#print axioms concDecode_mov32rr_verweigert
#print axioms concDecode_nur_b64_b32
#print axioms concDecode_laenge_ok
#print axioms concWitM0_wf
#print axioms concWit_fetch_decode
#print axioms concWit_kern1_fetch_verweigert
#print axioms concWit_alias
#print axioms concWit_weiterleitung
#print axioms concWit_fremd_alt
#print axioms concWit_spuelung
#print axioms concWit_fremd_neu
#print axioms concWitTeil_keine_gruppe
#print axioms concWitOverlap_keine_gruppe
#print axioms concWit_zeuge

end Gabbro.Grammatik.X86
