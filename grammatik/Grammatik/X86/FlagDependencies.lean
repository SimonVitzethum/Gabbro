/-
  File:      Grammatik/X86/FlagDependencies.lean
  Subject:   Flag dependencies across actual decoded control flow.

  Lane 601 (connection): reusable finite condition-dependency check over the
  canonical `Flags` / `bedingung` / `Codec.decode` path and the actual
  subsequent `jumpIf32` (`Ausfuehrung.schritt`) or accepted ControlCodec
  byte step (`cmovSchrittBytes` / `setccSchrittBytes`). Read sets are
  derived from the actual `Bedingung` value, never from an assumed
  branch-equivalence or liveness result. No new machine, no new decoder,
  no source claim; consumer connection for InstructionSelection600.
-/
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.ControlCodec
import Grammatik.X86.DecodingCoverage

namespace Gabbro.Grammatik.X86

/-- Finite flag names read by a decoded branch or conditional select.
    AF is absent by construction: `bedingung` never reads it. -/
inductive FlagName where
  | cf | pf | zf | sf | of_
  deriving DecidableEq, Repr, Inhabited

/-- Read set derived from the actual condition value: exactly the flags
    `bedingung` inspects for that condition (Intel mapping in `Wort.lean`:
    `o`/`no` read OF, `b`/`ae` read CF, `e`/`ne` read ZF, `be`/`a` combine
    CF and ZF, `s`/`ns` read SF, `p`/`np` read PF, `l`/`ge` combine SF and
    OF, `le`/`g` combine ZF, SF and OF). -/
def liestFlag : Bedingung → FlagName → Bool
  | .o, .of_ => true | .no, .of_ => true
  | .b, .cf => true | .ae, .cf => true
  | .e, .zf => true | .ne, .zf => true
  | .be, .cf => true | .be, .zf => true
  | .a, .cf => true | .a, .zf => true
  | .s, .sf => true | .ns, .sf => true
  | .p, .pf => true | .np, .pf => true
  | .l, .sf => true | .l, .of_ => true
  | .ge, .sf => true | .ge, .of_ => true
  | .le, .zf => true | .le, .sf => true | .le, .of_ => true
  | .g, .zf => true | .g, .sf => true | .g, .of_ => true
  | _, _ => false

/-- Project one named flag out of a snapshot. AF is excluded by
    construction: no condition reads it. -/
def flagWert : FlagName → Flags → Bool
  | .cf, f => f.cf
  | .pf, f => f.pf
  | .zf, f => f.zf
  | .sf, f => f.sf
  | .of_, f => f.of

/-- Agreement on exactly the flags the decoded condition reads.
    Unneeded flags may differ arbitrarily; AF is never constrained. -/
def stimmtUebberein (c : Bedingung) (f g : Flags) : Prop :=
  ∀ n, liestFlag c n = true → flagWert n f = flagWert n g

/-! ## 2. Agreement on the read flags fixes the condition value.

    One case per condition; each case extracts exactly the read-flag
    equations from `stimmtUebberein` and rewrites the `bedingung` value. -/

/-- Agreement on the read flags implies the same condition value, for
    every one of the 16 conditions. Read sets come from `liestFlag`
    above, never from an assumed liveness result. -/
theorem bedingung_stabil (c : Bedingung) (f g : Flags)
    (h : stimmtUebberein c f g) :
    bedingung c f = bedingung c g := by
  cases c with
  | o => exact h .of_ rfl
  | no =>
    have hof : f.of = g.of := h .of_ rfl
    simp only [bedingung, hof]
  | b => exact h .cf rfl
  | ae =>
    have hcf : f.cf = g.cf := h .cf rfl
    simp only [bedingung, hcf]
  | e => exact h .zf rfl
  | ne =>
    have hzf : f.zf = g.zf := h .zf rfl
    simp only [bedingung, hzf]
  | be =>
    have hcf : f.cf = g.cf := h .cf rfl
    have hzf : f.zf = g.zf := h .zf rfl
    simp only [bedingung, hcf, hzf]
  | a =>
    have hcf : f.cf = g.cf := h .cf rfl
    have hzf : f.zf = g.zf := h .zf rfl
    simp only [bedingung, hcf, hzf]
  | s => exact h .sf rfl
  | ns =>
    have hsf : f.sf = g.sf := h .sf rfl
    simp only [bedingung, hsf]
  | p => exact h .pf rfl
  | np =>
    have hpf : f.pf = g.pf := h .pf rfl
    simp only [bedingung, hpf]
  | l =>
    have hsf : f.sf = g.sf := h .sf rfl
    have hof : f.of = g.of := h .of_ rfl
    simp only [bedingung, hsf, hof]
  | ge =>
    have hsf : f.sf = g.sf := h .sf rfl
    have hof : f.of = g.of := h .of_ rfl
    simp only [bedingung, hsf, hof]
  | le =>
    have hzf : f.zf = g.zf := h .zf rfl
    have hsf : f.sf = g.sf := h .sf rfl
    have hof : f.of = g.of := h .of_ rfl
    simp only [bedingung, hzf, hsf, hof]
  | g =>
    have hzf : f.zf = g.zf := h .zf rfl
    have hsf : f.sf = g.sf := h .sf rfl
    have hof : f.of = g.of := h .of_ rfl
    simp only [bedingung, hzf, hsf, hof]

/-! ## 3. Executed control successor of a decoded conditional jump.

    `jccZiel` is the value `schritt` writes to `rip` for `jumpIf32`
    (post-decode address plus the sign-extended displacement exactly when
    the condition holds). Stability follows from `bedingung_stabil`. -/

/-- Executed control successor of a decoded conditional jump over a flag
    snapshot: the post-decode RIP, plus the sign-extended displacement
    exactly when the condition holds. This is the `rip` value the accepted
    `schritt_jumpIf32_genommen` / `schritt_jumpIf32_nicht` equations write. -/
def jccZiel (f : Flags) (rip : Adresse) (len : Nat) (c : Bedingung)
    (d : BitVec 32) : Adresse :=
  if bedingung c f then ripNach rip len + dispWort d else ripNach rip len

/-- The executed control successor depends only on the flags the decoded
    condition reads: agreement there gives the same successor address. -/
theorem jccZiel_stabil (c : Bedingung) (f g : Flags) (rip : Adresse)
    (len : Nat) (d : BitVec 32) (h : stimmtUebberein c f g) :
    jccZiel f rip len c d = jccZiel g rip len c d := by
  unfold jccZiel
  rw [bedingung_stabil c f g h]

/-! ## 4. The decoded length of a conditional jump is actual data.

    A successful `Codec.decode` of a `jumpIf32` shape consumes exactly its
    six canonical bytes. This ties the length the step runs at to decoding,
    never to an emitter note, and makes the decode premise of the main
    stability theorem load-bearing (it supplies `laengeOk`). Proved through
    the accepted coverage shape `decktAb` (`DecodingCoverage.decode_abdeckung`):
    no decoder arm is inverted here a second time. -/

/-- A successful decode of a conditional-jump shape fixes the consumed
    length at six actual bytes: the accepted coverage shape `decktAb`
    admits `jumpIf32` at exactly length 6, and every other disjunct is a
    constructor clash. -/
theorem decodeJumpIf_laenge (c : Bedingung) (d : BitVec 32) (len : Nat)
    (pfx rest : List Byte)
    (hdec : decode pfx = some ((⟨.jumpIf32 c d, len⟩ : Decodiert), rest)) :
    len = 6 := by
  obtain ⟨_, _, hdeckt, _⟩ := decode_abdeckung pfx _ rest hdec
  simp only [decktAb] at hdeckt
  rcases hdeckt with ⟨hbeq, _⟩ | ⟨_, hbeq, _⟩ | ⟨_, hbeq, _⟩ |
    ⟨_, _, hbeq, _⟩ | ⟨_, _, hbeq, _⟩ | ⟨_, _, _, hbeq, _⟩ |
    ⟨_, hbeq, _⟩ | ⟨_, _, _, hlen⟩
  · simp at hbeq
  · simp at hbeq
  · simp at hbeq
  · simp at hbeq
  · simp at hbeq
  · simp at hbeq
  · simp at hbeq
  · exact hlen

/-! ## 5. Same read flags, same executed successor on actual decoded bytes.

    The main consumer theorem: where the canonical decoder produces a
    conditional jump, two states that agree on the flags the decoded
    condition actually reads take the same `schritt` successor RIP. The
    decoded triple `(c, d, len)` comes from `decode`; the read set comes
    from `liestFlag`; the step is the accepted `schritt`. -/

/-- Agreement on the flags read by an actually decoded conditional jump
    implies the same executed control successor. Every premise is used:
    `hdec` fixes the decoded length (hence `laengeOk`), `hrip` aligns the
    fetch addresses, `hfl` is the read-set agreement, `hF`/`hG` are the two
    accepted steps. -/
theorem jccSchritt_stabil (pfx rest : List Byte) (c : Bedingung)
    (d : BitVec 32) (len : Nat) (sF sG sF' sG' : Zustand)
    (hdec : decode pfx = some ((⟨.jumpIf32 c d, len⟩ : Decodiert), rest))
    (hrip : sF.rip = sG.rip)
    (hfl : stimmtUebberein c sF.flags sG.flags)
    (hF : schritt (⟨.jumpIf32 c d, len⟩ : Decodiert) sF = some sF')
    (hG : schritt (⟨.jumpIf32 c d, len⟩ : Decodiert) sG = some sG') :
    sF'.rip = sG'.rip := by
  have hlen : len = 6 := decodeJumpIf_laenge c d len pfx rest hdec
  have hok : laengeOk len = true := by rw [hlen]; decide
  have hbed : bedingung c sF.flags = bedingung c sG.flags :=
    bedingung_stabil c sF.flags sG.flags hfl
  by_cases ht : bedingung c sF.flags = true
  · have htG : bedingung c sG.flags = true := by rw [← hbed]; exact ht
    have eF := schritt_jumpIf32_genommen
      (⟨.jumpIf32 c d, len⟩ : Decodiert) sF c d hok rfl ht
    have eG := schritt_jumpIf32_genommen
      (⟨.jumpIf32 c d, len⟩ : Decodiert) sG c d hok rfl htG
    rw [hF] at eF
    rw [hG] at eG
    cases eF
    cases eG
    show ripNach sF.rip len + dispWort d = ripNach sG.rip len + dispWort d
    rw [hrip]
  · have hf : bedingung c sF.flags = false := by
      revert ht
      cases bedingung c sF.flags <;> simp_all
    have hfG : bedingung c sG.flags = false := by rw [← hbed]; exact hf
    have eF := schritt_jumpIf32_nicht
      (⟨.jumpIf32 c d, len⟩ : Decodiert) sF c d hok rfl hf
    have eG := schritt_jumpIf32_nicht
      (⟨.jumpIf32 c d, len⟩ : Decodiert) sG c d hok rfl hfG
    rw [hF] at eF
    rw [hG] at eG
    cases eF
    cases eG
    show ripNach sF.rip len = ripNach sG.rip len
    rw [hrip]

/-! ## 6. Conditional-select byte steps read the same condition.

    The accepted ControlCodec byte steps (`cmovSchrittBytes`,
    `setccSchrittBytes`) apply the accepted evaluators over the pre-state
    flags. Agreement on the read flags therefore gives the same selected
    value: same moved word for CMOVcc, same selected low byte for SETcc.
    This is the second consumer arm (beside `jumpIf32`) for
    InstructionSelection600. -/

/-- CMOVcc byte-step stability: two states that agree on the flags the
    decoded condition reads select the same destination word. Every
    premise is used: `hok` runs both byte steps, `hfl` aligns the
    conditions, `hregs` aligns the moved and kept words, `hF`/`hG` are
    the two accepted steps. -/
theorem cmovBytes_stabil (len : Nat) (sF sG sF' sG' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hfl : stimmtUebberein c sF.flags sG.flags)
    (hregs : ∀ q, sF.register q = sG.register q)
    (hF : cmovSchrittBytes len sF dst src c = some sF')
    (hG : cmovSchrittBytes len sG dst src c = some sG') :
    sF'.register dst = sG'.register dst := by
  unfold cmovSchrittBytes at hF hG
  rw [hok] at hF hG
  cases hF
  cases hG
  show (cmovAnwenden sF dst src c).register dst =
    (cmovAnwenden sG dst src c).register dst
  by_cases hbed : bedingung c sF.flags = true
  · have hbedG : bedingung c sG.flags = true := by
      have h := bedingung_stabil c sF.flags sG.flags hfl
      rw [hbed] at h
      exact h.symm
    have eF := cmovAnwenden_genommen_wert sF dst src c hbed
    have eG := cmovAnwenden_genommen_wert sG dst src c hbedG
    rw [eF, eG]
    exact hregs src
  · have hfalse : bedingung c sF.flags = false := by
      revert hbed
      cases bedingung c sF.flags <;> simp_all
    have hfalseG : bedingung c sG.flags = false := by
      have h := bedingung_stabil c sF.flags sG.flags hfl
      rw [hfalse] at h
      exact h.symm
    have eF := cmovAnwenden_nicht_wert sF dst src c hfalse
    have eG := cmovAnwenden_nicht_wert sG dst src c hfalseG
    rw [eF, eG]
    exact hregs dst

/-- SETcc byte-step stability: two states that agree on the flags the
    decoded condition reads select the same destination low byte. Reuses
    the accepted value equation `setccSchrittBytes_wert` on both sides. -/
theorem setccBytes_stabil (len : Nat) (sF sG sF' sG' : Zustand)
    (dst : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hfl : stimmtUebberein c sF.flags sG.flags)
    (hregs : sF.register dst = sG.register dst)
    (hF : setccSchrittBytes len sF dst c = some sF')
    (hG : setccSchrittBytes len sG dst c = some sG') :
    sF'.register dst = sG'.register dst := by
  have eF := setccSchrittBytes_wert len sF sF' dst c hok hF
  have eG := setccSchrittBytes_wert len sG sG' dst c hok hG
  have hcc : setCCByte c sF.flags = setCCByte c sG.flags := by
    unfold setCCByte
    rw [bedingung_stabil c sF.flags sG.flags hfl]
  rw [eF, eG, hregs, hcc]

/-! ## 7. Unneeded flags may change: AF never matters, named groups only
    read their own flags.

    `bedingung` never inspects AF, so AF may change arbitrarily under every
    condition. The pins cover overflow (OF), carry (CF), sign (SF), zero
    (ZF) and parity (PF): each condition ignores every flag outside its
    `liestFlag` set on concrete snapshots. -/

/-- AF irrelevance: the auxiliary flag may change arbitrarily without
    changing any condition value, since no `bedingung` arm reads it. -/
theorem bedingung_af_frei (c : Bedingung) (f : Flags) (a b : Option Bool) :
    bedingung c { f with af := a } = bedingung c { f with af := b } := by
  cases c <;> rfl

/-- PIN: overflow reads OF alone; flipping CF keeps the value. -/
theorem pin_o_ignoriert_cf :
    bedingung .o ⟨true, false, none, false, false, true⟩ =
      bedingung .o ⟨false, false, none, false, false, true⟩ := by
  decide

/-- PIN: carry reads CF alone; flipping OF keeps the value. -/
theorem pin_b_ignoriert_of :
    bedingung .b ⟨false, false, none, false, false, true⟩ =
      bedingung .b ⟨false, false, none, false, false, false⟩ := by
  decide

/-- PIN: zero reads ZF alone; flipping CF, PF, SF and OF keeps the value. -/
theorem pin_e_ignoriert_rest :
    bedingung .e ⟨true, true, none, false, true, true⟩ =
      bedingung .e ⟨false, false, none, false, false, false⟩ := by
  decide

/-- PIN: signed less-than combines SF and OF; equal signs with clear
    zero differ from the taken shape. -/
theorem pin_l_kombiniert :
    bedingung .l ⟨false, false, none, false, true, false⟩ = true ∧
      bedingung .l ⟨false, false, none, false, true, true⟩ = false := by
  decide

/-- PIN: signed greater combines ZF, SF and OF; a set zero flag refuses
    even with equal signs. -/
theorem pin_g_braucht_null :
    bedingung .g ⟨false, false, none, true, false, false⟩ = false ∧
      bedingung .g ⟨false, false, none, false, false, false⟩ = true := by
  decide

/-- PIN: parity reads PF alone; flipping SF and CF keeps the value. -/
theorem pin_p_ignoriert_sf_cf :
    bedingung .p ⟨true, true, none, false, true, false⟩ =
      bedingung .p ⟨false, true, none, false, false, false⟩ := by
  decide

/-! ## 8. Joint witnesses, refusals, CUTS.

    `jccSchritt_stabil_zeuge` instantiates ALL premises of the main
    theorem jointly (decoded canonical bytes, two flag snapshots agreeing
    on ZF but differing elsewhere, both accepted steps) and pairs the
    shared successor with a realistic preceding arithmetic run that
    observably changes memory, plus a planted truncation refusal.
    `mov_xor_wechsel_zeuge` is the negative witness: replacing MOV by
    XOR-zero changes the following condition exactly because flags are
    live there. -/

/-- Companion snapshot: same ZF as `zeugeGleich`, every other flag
    flipped (CF/SF/OF set, PF clear, AF undefined). -/
def sAnder : Zustand :=
  { register := zeugeReg, flags := ⟨true, false, none, true, true, true⟩,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness register file for the realistic run: `rbx` holds 42, the
    stack top sits at 8192, everything else is zero. -/
def witArith : Register → Wort :=
  fun q => if q = Register.rbx then BitVec.ofNat 64 42
    else if q = Register.rsp then BitVec.ofNat 64 8192
    else BitVec.ofNat 64 0

/-- Witness start state for the realistic run. -/
def witStart : Zustand :=
  { register := witArith, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Realistic preceding program at canonical decoded lengths: set `rax`
    to 42, store it through the stack pointer (memory observably changes
    from 0 to 42), then subtract the equal `rbx` so the zero flag the
    following branch reads is set by actual arithmetic. -/
def progVor : List Decodiert :=
  [{ befehl := Befehl.movImm64 Register.rax (BitVec.ofNat 64 42), laenge := 10 }, { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 8 }, { befehl := Befehl.subReg64 Register.rax Register.rbx, laenge := 3 }]

/-- Witness register file for the MOV/XOR contrast: `rax = rbx = 5`,
    the stack top at 8192. -/
def witMovReg : Register → Wort :=
  fun q => if q = Register.rax then BitVec.ofNat 64 5
    else if q = Register.rbx then BitVec.ofNat 64 5
    else if q = Register.rsp then BitVec.ofNat 64 8192
    else BitVec.ofNat 64 0

/-- Witness start state for the MOV/XOR contrast (zero flag clear). -/
def witMovStart : Zustand :=
  { register := witMovReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- JOINT witness for `jccSchritt_stabil`: the canonical `je +16` bytes
    decode at actual length 6, both accepted steps run (ZF set in both
    snapshots, all other flags differing), the successors agree, the
    preceding arithmetic run stores 42 observably and sets ZF, and the
    truncated prefix is refused. -/
theorem jccSchritt_stabil_zeuge :
    ∃ (sF' sG' : Zustand),
      decode (encode (.jumpIf32 .e (BitVec.ofNat 32 16))) =
        some ((⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert), []) ∧
      schritt (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert)
        zeugeGleich = some sF' ∧
      schritt (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert)
        sAnder = some sG' ∧
      sF'.rip = sG'.rip ∧
      (lauf progVor witStart).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (natByte 42) ∧
      (lauf progVor witStart).map (fun s => s.flags.zf) = some true ∧
      decode ((encode (.jumpIf32 .e (BitVec.ofNat 32 16))).take 5) =
        none := by
  have hok : laengeOk 6 = true := by decide
  have hbedF : bedingung .e zeugeGleich.flags = true := by decide
  have hbedG : bedingung .e sAnder.flags = true := by decide
  have hfl : stimmtUebberein .e zeugeGleich.flags sAnder.flags := by
    intro n hn
    cases n with
    | cf => exact absurd hn (by decide)
    | pf => exact absurd hn (by decide)
    | zf => rfl
    | sf => exact absurd hn (by decide)
    | of_ => exact absurd hn (by decide)
  have hF := schritt_jumpIf32_genommen
    (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert)
    zeugeGleich .e _ hok rfl hbedF
  have hG := schritt_jumpIf32_genommen
    (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert)
    sAnder .e _ hok rfl hbedG
  have hdec : decode (encode (.jumpIf32 .e (BitVec.ofNat 32 16))) =
      some ((⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert), []) := by
    have h := roundtrip_jumpIf32 .e (BitVec.ofNat 32 16) []
    rw [List.append_nil] at h
    have hlen : (encode (.jumpIf32 .e (BitVec.ofNat 32 16))).length = 6 :=
      rfl
    rw [hlen] at h
    exact h
  refine ⟨_, _, hdec, hF, hG, ?_, by decide, by decide, by decide⟩
  exact jccSchritt_stabil _ [] .e _ 6 zeugeGleich sAnder _ _ hdec rfl hfl
    hF hG

/-- NEGATIVE witness: XOR-zero in place of MOV changes the following
    `je` exactly because flags are live there. MOV preserves ZF (clear),
    so the branch falls through to 4105; XOR of equal words sets ZF, so
    the same branch is taken to 4121. -/
theorem mov_xor_wechsel_zeuge :
    ((schritt (⟨.movReg64 .rax .rbx, 3⟩ : Decodiert) witMovStart).map
      (fun s => s.flags.zf) = some false) ∧
    ((schritt (⟨.xorReg64 .rax .rbx, 3⟩ : Decodiert) witMovStart).map
      (fun s => s.flags.zf) = some true) ∧
    (((schritt (⟨.movReg64 .rax .rbx, 3⟩ : Decodiert) witMovStart).bind
      (schritt (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert))).map
      (fun s => s.rip) = some (BitVec.ofNat 64 4105)) ∧
    (((schritt (⟨.xorReg64 .rax .rbx, 3⟩ : Decodiert) witMovStart).bind
      (schritt (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert))).map
      (fun s => s.rip) = some (BitVec.ofNat 64 4121)) ∧
    bedingung .e (xor64 5 5).2 = true ∧
    bedingung .e zeugeFlags = false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- REFUSAL: a conditional jump at a bad decode length refuses on every
    state (the accepted length refusal, used by both consumer arms). -/
theorem jccLaenge_verweigert (s : Zustand) (c : Bedingung)
    (d : BitVec 32) :
    schritt (⟨.jumpIf32 c d, 0⟩ : Decodiert) s = none := by
  have h0 : laengeOk 0 = false := by decide
  exact schritt_laenge_verweigert _ s h0

/-- REFUSAL: five of the six canonical `je` bytes do not decode. -/
theorem jccKurz_verweigert :
    decode ((encode (.jumpIf32 .e (BitVec.ofNat 32 16))).take 5) = none := by
  decide

/- CUTS:
    Proved here (all over the REUSED canonical `Flags`/`bedingung`,
    `Codec.decode`, accepted `Ausfuehrung.schritt` equations and accepted
    ControlCodec byte steps -- no new machine, decoder, or interpreter):
    - finite read sets (`liestFlag`) derived from the actual `Bedingung`
      value, covering overflow (OF), carry (CF), sign (SF), zero (ZF) and
      parity (PF) conditions with their combinations; AF absent by
      construction;
    - `bedingung_stabil`: agreement on the read flags fixes the condition
      value for all 16 conditions;
    - `jccZiel`/`jccZiel_stabil`: the executed control successor depends
      only on the read flags;
    - `decodeJumpIf_laenge`: a successful decode of a `jumpIf32` shape
      consumes exactly six actual bytes (through the accepted coverage
      shape `decktAb`, no second inversion of the decoder);
    - `jccSchritt_stabil`: agreement on the read flags of an actually
      decoded conditional jump implies the same executed `schritt`
      successor RIP (taken and untaken);
    - `cmovBytes_stabil` / `setccBytes_stabil`: the same agreement gives
      the same selected word / low byte through the accepted ControlCodec
      byte steps;
    - `bedingung_af_frei` plus concrete group pins: unneeded flags may
      change, AF always may;
    - joint non-degenerate witness (`jccSchritt_stabil_zeuge`: decoded
      bytes, two agreeing snapshots, a memory-changing arithmetic run
      with ZF set by `sub`, planted truncation refusal) and negative
      witness (`mov_xor_wechsel_zeuge`: XOR-zero replacing MOV flips a
      live `je`);
    - invalid byte/length refusals (`jccLaenge_verweigert`,
      `jccKurz_verweigert`).
    NOT proved here, and not claimed:
    - No hardware correspondence: `bedingung` read sets follow the Intel
      manual as modelled in `Wort.lean`, checked here only as
      self-consistency, not silicon.
    - No liveness/available-flags analysis and no optimiser claim: the
      read sets are per-condition facts, never a program-wide liveness
      result; nothing here selects instructions (consumer connection for
      InstructionSelection600 only).
    - No TSO/GX, concurrency, cost, time or termination claim; every
      fact is sequential over one `Speicher`.
    - No source, checker, Spec or goal claim; no new `Befehl`
      constructor and no new decoder arm.
-/

#print axioms bedingung_stabil
#print axioms jccZiel_stabil
#print axioms decodeJumpIf_laenge
#print axioms jccSchritt_stabil
#print axioms cmovBytes_stabil
#print axioms setccBytes_stabil
#print axioms bedingung_af_frei
#print axioms jccSchritt_stabil_zeuge
#print axioms mov_xor_wechsel_zeuge
#print axioms jccLaenge_verweigert
#print axioms jccKurz_verweigert

end Gabbro.Grammatik.X86
