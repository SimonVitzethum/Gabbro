/-
  File:      Grammatik/X86/ISAExecution.lean
  Subject:   Fetch-decode-execute of the unified instruction set from actual
             executable memory, and the layout theorem: a program laid out
             by `encodeI` runs under `byteschrittI` exactly as `laufI`.

  Mirrors `Byteschritt.lean` one to one and REUSES its fetch (`geholt`,
  `holeFetchAux`, `ausfuehrbarN`, `geholt_nur_ausfuehrbar`), its outcome type
  `ByteAusgang` and its runtime consistency check (consumed length + rest =
  fetched window, `laengeOk`, execute permission of the consumed prefix).
  Only the decoder (`decodeI`) and the step (`stepI`) are the unified ones
  from `ISA.lean`. Memory facts reuse `Speicher.lean` (`write64`,
  `write32`, `writeBytesN_miss`, `schreibbarN`).

  Main results:
    `byteschrittI_erweitert`   every pilot byte step is a unified byte step;
    `byteschrittI_kanonisch`   one canonical instruction in the fetch window
                               steps exactly as `stepI` (the analogue of
                               `Byteschritt.kanonisch_schritt_ueberein`);
    `laufBytesI_spur`          a TRACE theorem (control flow allowed): if the
                               i-th executed instruction's canonical bytes sit
                               at the RIP where it executes, the byte run IS
                               `laufI`;
    `laufBytesI_layout`        the LAYOUT theorem: a straight-line program laid
                               out contiguously by `encodeI` at RIP, in
                               executable memory under W^X, runs under
                               `byteschrittI` exactly as `laufI` on the list,
                               outcome for outcome (success AND refusal).
-/
import Grammatik.X86.ISA
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-! ## 1. Fetch, decode, step. -/

/-- Fetch and decode with the unified decoder; the SAME checks as
    `fetchDekodiert` (nothing decoded is trusted without them). -/
def fetchDekodiertI (s : Zustand) : Option (InstrDecoded × List Byte) :=
  match decodeI (geholt s) with
  | none => none
  | some (d, rest) =>
    if d.laenge + rest.length == (geholt s).length &&
        laengeOk d.laenge && ausfuehrbarN s.speicher s.rip d.laenge
    then some (d, rest)
    else none

/-- One unified byte step from actual memory: fetch, `decodeI`, `stepI`.
    Takes ONLY the state; refusal is `verweigert` (no halt claim). -/
def byteschrittI (s : Zustand) : ByteAusgang :=
  match fetchDekodiertI s with
  | none => .verweigert
  | some (d, _) =>
    match stepI d s with
    | none => .verweigert
    | some s' => .weiter s'

/-- Bounded unified byte run (same shape as `laufBytes`). -/
def laufBytesI : Nat → Zustand → ByteAusgang
  | 0, s => .weiter s
  | n+1, s =>
    match byteschrittI s with
    | .verweigert => .verweigert
    | .weiter s' => laufBytesI n s'

/-- Outcome of an abstract run as a byte-step outcome. -/
def ausgangVon : Option Zustand → ByteAusgang
  | some s => .weiter s
  | none => .verweigert

/-! ## 2. The pilot byte machine embeds. -/

/-- Pilot fetches are unified fetches of the lifted instruction. -/
theorem fetchDekodiertI_pilot (s : Zustand) (d : Decodiert) (rest : List Byte)
    (h : fetchDekodiert s = some (d, rest)) :
    fetchDekodiertI s = some (liftPilot d, rest) := by
  obtain ⟨hdec, hlen, hok, hexe⟩ := fetchDekodiert_entspricht s d rest h
  have hF : decF .pilot (geholt s) = some (liftPilot d, rest) := by
    simp only [decF, hdec, liftPilot]
  have hI := decodeI_von_fam .pilot (geholt s) _ hF
  unfold fetchDekodiertI
  rw [hI]
  dsimp only
  have hbeq : (d.laenge + rest.length == (geholt s).length) = true := by
    rw [beq_iff_eq]
    exact hlen
  rw [if_pos (by simp only [liftPilot] at *; simp [hbeq, hok, hexe])]

/-- EMBEDDING: every successful pilot byte step is a unified byte step with
    the same successor. -/
theorem byteschrittI_erweitert (s s' : Zustand)
    (h : byteschritt s = .weiter s') : byteschrittI s = .weiter s' := by
  unfold byteschritt at h
  cases hf : fetchDekodiert s with
  | none => rw [hf] at h; cases h
  | some p =>
    obtain ⟨d, rest⟩ := p
    rw [hf] at h
    dsimp only at h
    have hI := fetchDekodiertI_pilot s d rest hf
    unfold byteschrittI
    rw [hI]
    dsimp only
    show (match schritt ⟨d.befehl, d.laenge⟩ s with
      | none => ByteAusgang.verweigert | some s' => .weiter s') = _
    exact h

/-! ## 3. Window lemmas. -/

/-- A window that starts with `bs` grants execute permission to `bs`. -/
theorem geholt_praefix_ausfuehrbar (s : Zustand) (bs suf : List Byte)
    (hw : geholt s = bs ++ suf) :
    ausfuehrbarN s.speicher s.rip bs.length = true := by
  have key : ∀ n, n ≤ (geholt s).length →
      ausfuehrbarN s.speicher s.rip n = true := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [ausfuehrbarN, Bool.and_eq_true]
      exact ⟨ih (by omega), geholt_nur_ausfuehrbar s n (by omega)⟩
  apply key
  rw [hw, List.length_append]
  omega

/-- CANONICAL STEP: one canonical unified instruction at the front of the
    fetch window is fetched as itself and steps exactly as `stepI`. -/
theorem byteschrittI_kanonisch (i : Instr) (hk : kanonischI i = true)
    (s : Zustand) (suffix : List Byte)
    (hwin : geholt s = encodeI i ++ suffix) :
    fetchDekodiertI s = some (canonI i, suffix) ∧
      byteschrittI s = ausgangVon (stepI (canonI i) s) := by
  have hrt := decodeI_encodeI i hk suffix
  rw [← hwin] at hrt
  have hexe := geholt_praefix_ausfuehrbar s _ _ hwin
  have hok := laengeOk_encodeI i
  have hbeq : ((encodeI i).length + suffix.length == (geholt s).length) = true := by
    rw [beq_iff_eq, hwin, List.length_append]
  have hf : fetchDekodiertI s = some (canonI i, suffix) := by
    unfold fetchDekodiertI
    rw [hrt]
    dsimp only
    rw [if_pos (by simp only [canonI]; simp [hbeq, hok, hexe])]
  refine ⟨hf, ?_⟩
  unfold byteschrittI
  rw [hf]
  dsimp only
  cases stepI (canonI i) s <;> rfl

/-! ## 4. Trace theorem: the byte run IS the unified run. -/

/-- The trace premise: at every reached state the instruction to execute
    next is canonical and its bytes open the fetch window. Control flow is
    allowed: the bytes are wherever RIP points. -/
def SpurAn : List Instr → Zustand → Prop
  | [], _ => True
  | i :: is, s =>
    kanonischI i = true ∧ (∃ suf, geholt s = encodeI i ++ suf) ∧
      ∀ s1, stepI (canonI i) s = some s1 → SpurAn is s1

/-- TRACE THEOREM: under the trace premise, `n` unified byte steps from
    actual memory produce exactly the outcome of `laufI` on the canonical
    instruction list -- the same successor, or a refusal exactly when
    `laufI` refuses. -/
theorem laufBytesI_spur (is : List Instr) (s : Zustand) (h : SpurAn is s) :
    laufBytesI is.length s = ausgangVon (laufI (is.map canonI) s) := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨hk, ⟨suf, hw⟩, hnext⟩ := h
    have hstep := (byteschrittI_kanonisch i hk s suf hw).2
    simp only [List.length_cons, List.map_cons, laufBytesI, laufI, hstep]
    cases hs : stepI (canonI i) s with
    | none => rfl
    | some s1 => exact ih s1 (hnext s1 hs)

/-! ## 5. Layout theorem: a laid-out straight-line program. -/

/-- The bytes of a program laid out back to back. -/
def progBytes : List Instr → List Byte
  | [] => []
  | i :: is => encodeI i ++ progBytes is

/-- `bs` sits at `a`: every byte executable and equal to the list entry. -/
def CodeAt (m : Speicher) (a : Adresse) (bs : List Byte) : Prop :=
  ∀ i, i < bs.length →
    m.ausfuehrbar (addrOff a i) = true ∧ m.bytes (addrOff a i) = bs.getD i 0

/-- W^X: no executable byte is writable. -/
def WX (m : Speicher) : Prop :=
  ∀ x, m.ausfuehrbar x = true → m.schreibbar x = false

/-- Fall-through instructions: everything except the pilot control forms. -/
def faelltDurchI : Instr → Bool
  | .pilot (.jump32 _) => false
  | .pilot (.jumpIf32 _ _) => false
  | .pilot (.call32 _) => false
  | .pilot .ret => false
  | _ => true

/-- Memory protection of one step: permissions unchanged, and no
    non-writable byte changes. -/
def Schutz (m m' : Speicher) : Prop :=
  m'.ausfuehrbar = m.ausfuehrbar ∧ m'.schreibbar = m.schreibbar ∧
    ∀ x, m.schreibbar x = false → m'.bytes x = m.bytes x

theorem Schutz_refl (m : Speicher) : Schutz m m :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem schreibbarN_an (m : Speicher) (a : Adresse) (n k : Nat)
    (h : schreibbarN m a n = true) (hk : k < n) :
    m.schreibbar (addrOff a k) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [schreibbarN, Bool.and_eq_true] at h
    by_cases hkn : k < n
    · exact ih h.1 hkn
    · have : k = n := by omega
      subst this
      exact h.2

theorem writeBytesN_geschuetzt (m : Speicher) (a : Adresse) (v : Wort) (n : Nat)
    (x : Adresse) (hw : schreibbarN m a n = true) (hx : m.schreibbar x = false) :
    writeBytesN m a v n x = m.bytes x := by
  apply writeBytesN_miss
  intro k hk hxa
  have := schreibbarN_an m a n k hw hk
  rw [← hxa, hx] at this
  cases this

theorem write64_schutz (m : Speicher) (a : Adresse) (v : Wort) (m' : Speicher)
    (h : write64 m a v = some m') : Schutz m m' := by
  unfold write64 at h
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at h
    cases h
    exact ⟨rfl, rfl, fun x hx =>
      writeBytesN_geschuetzt m a v 8 x (by rw [schreibbarN_acht]; exact hc) hx⟩
  · rw [if_neg hc] at h
    cases h

theorem write32_schutz (m : Speicher) (a : Adresse) (v : Wort) (m' : Speicher)
    (h : write32 m a v = some m') : Schutz m m' := by
  unfold write32 at h
  by_cases hc : schreibbarN m a 4 = true
  · rw [if_pos hc] at h
    cases h
    exact ⟨rfl, rfl, fun x hx => writeBytesN_geschuetzt m a v 4 x hc hx⟩
  · rw [if_neg hc] at h
    cases h

/-- STEP FRAME of the pilot family: memory protected; fall-through forms
    advance RIP by the decoded length. -/
theorem schritt_rahmenI (b : Befehl) (l : Nat) (s s1 : Zustand)
    (h : schritt ⟨b, l⟩ s = some s1) :
    Schutz s.speicher s1.speicher ∧
      (faelltDurchI (.pilot b) = true → s1.rip = ripNach s.rip l) := by
  unfold schritt at h
  split at h
  · cases h
  · cases b with
    | movImm64 dst v => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | movReg64 dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | addReg64 dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | subReg64 dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | xorReg64 dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | cmpReg64 lhs rhs => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | load64 dst base disp =>
      dsimp only at h
      split at h
      · cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
      · cases h
    | store64 base src disp =>
      dsimp only at h
      split at h
      · rename_i m hm
        cases h
        exact ⟨write64_schutz _ _ _ _ hm, fun _ => rfl⟩
      · cases h
    | jump32 disp =>
      cases h
      exact ⟨Schutz_refl _, fun hf => absurd hf Bool.false_ne_true⟩
    | jumpIf32 c disp =>
      cases h
      exact ⟨Schutz_refl _, fun hf => absurd hf Bool.false_ne_true⟩
    | call32 disp =>
      dsimp only at h
      split at h
      · rename_i m hm
        cases h
        exact ⟨write64_schutz _ _ _ _ hm, fun hf => absurd hf Bool.false_ne_true⟩
      · cases h
    | push64 src =>
      dsimp only at h
      split at h
      · rename_i m hm
        cases h
        exact ⟨write64_schutz _ _ _ _ hm, fun _ => rfl⟩
      · cases h
    | pop64 dst =>
      dsimp only at h
      split at h
      · cases h
        split
        · exact ⟨Schutz_refl _, fun _ => rfl⟩
        · exact ⟨Schutz_refl _, fun _ => rfl⟩
      · cases h
    | ret =>
      dsimp only at h
      split at h
      · cases h
        exact ⟨Schutz_refl _, fun hf => absurd hf Bool.false_ne_true⟩
      · cases h

/-- STEP FRAME of the unified step: every family protects memory, and every
    fall-through instruction advances RIP by its decoded length. -/
theorem stepI_rahmen (i : Instr) (l : Nat) (s s1 : Zustand)
    (h : stepI ⟨i, l⟩ s = some s1) :
    Schutz s.speicher s1.speicher ∧
      (faelltDurchI i = true → s1.rip = ripNach s.rip l) := by
  cases i with
  | pilot b => exact schritt_rahmenI b l s s1 h
  | muldiv b =>
    rw [stepI_muldiv] at h
    unfold MulDivErgebnis.nachfolger at h
    split at h
    · rename_i s' hs
      cases h
      unfold mulDivSchritt at hs
      split at hs
      · cases hs
      · cases b with
        | mulRax src => cases hs; exact ⟨Schutz_refl _, fun _ => rfl⟩
        | imul2 dst src => cases hs; exact ⟨Schutz_refl _, fun _ => rfl⟩
        | divRax src =>
          dsimp only at hs
          split at hs
          · cases hs; exact ⟨Schutz_refl _, fun _ => rfl⟩
          · cases hs
        | idivRax src =>
          dsimp only at hs
          split at hs
          · cases hs; exact ⟨Schutz_refl _, fun _ => rfl⟩
          · cases hs
    · cases h
  | shift f =>
    rw [stepI_shift] at h
    refine ⟨?_, fun _ => shiftSchritt_rip _ s s1 h⟩
    rw [shiftSchritt_speicher _ s s1 h]
    exact Schutz_refl _
  | narrow o =>
    rw [stepI_narrow] at h
    unfold stepNarrow at h
    split at h
    · cases h
    · cases o with
      | mov32rr dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
      | movzx8 dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
      | movsx8 dst src => cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
      | store32 base src disp =>
        dsimp only at h
        split at h
        · rename_i s' hs
          cases h
          unfold storeNarrow at hs
          split at hs
          · rename_i m hm
            cases hs
            exact ⟨write32_schutz _ _ _ _ hm, fun _ => rfl⟩
          · cases hs
        · cases h
  | cond c =>
    cases c with
    | setcc c dst =>
      rw [stepI_setcc] at h
      unfold setccSchrittBytes at h
      split at h
      · cases h
      · cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩
    | cmov c dst src =>
      rw [stepI_cmov] at h
      unfold cmovSchrittBytes at h
      split at h
      · cases h
      · cases h; exact ⟨Schutz_refl _, fun _ => rfl⟩

/-! ### Code placement lemmas. -/

theorem addrOff_ripNach (a : Adresse) (l i : Nat) :
    addrOff (ripNach a l) i = addrOff a (l + i) := by
  unfold addrOff ripNach
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem holeFetchAux_codeAt (m : Speicher) (a : Adresse) (bs : List Byte)
    (off n : Nat)
    (h : ∀ i, i < bs.length →
      m.ausfuehrbar (addrOff a (off + i)) = true ∧
        m.bytes (addrOff a (off + i)) = bs.getD i 0)
    (hn : bs.length ≤ n) :
    ∃ suf, holeFetchAux m a off n = bs ++ suf := by
  induction bs generalizing off n with
  | nil => exact ⟨holeFetchAux m a off n, rfl⟩
  | cons b bs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero, List.getD_cons_zero] at h0
      obtain ⟨suf, hsuf⟩ := ih (off + 1) n (fun i hi => by
        have hx := h (i + 1) (by simp; omega)
        rw [show off + (i + 1) = off + 1 + i by omega] at hx
        simpa using hx) (by simp at hn; omega)
      refine ⟨suf, ?_⟩
      have hkopf : holeFetchAux m a off (n + 1) =
          m.bytes (addrOff a off) :: holeFetchAux m a (off + 1) n := by
        simp only [holeFetchAux, h0.1, if_true]
      rw [hkopf, h0.2, hsuf]
      rfl

theorem geholt_codeAt (s : Zustand) (bs : List Byte)
    (h : CodeAt s.speicher s.rip bs) (hn : bs.length ≤ 15) :
    ∃ suf, geholt s = bs ++ suf := by
  unfold geholt
  exact holeFetchAux_codeAt s.speicher s.rip bs 0 fetchCap
    (fun i hi => by rw [Nat.zero_add]; exact h i hi) hn

theorem codeAt_links (m : Speicher) (a : Adresse) (xs ys : List Byte)
    (h : CodeAt m a (xs ++ ys)) : CodeAt m a xs := by
  intro i hi
  have := h i (by rw [List.length_append]; omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    ← List.getD_eq_getElem?_getD] at this
  exact this

theorem codeAt_rechts (m : Speicher) (a : Adresse) (xs ys : List Byte)
    (h : CodeAt m a (xs ++ ys)) : CodeAt m (ripNach a xs.length) ys := by
  intro i hi
  have := h (xs.length + i) (by rw [List.length_append]; omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show xs.length + i - xs.length = i by omega,
    ← List.getD_eq_getElem?_getD] at this
  rw [addrOff_ripNach]
  exact this

theorem codeAt_schutz (m m' : Speicher) (a : Adresse) (bs : List Byte)
    (hwx : WX m) (hs : Schutz m m') (h : CodeAt m a bs) : CodeAt m' a bs := by
  intro i hi
  obtain ⟨hx, hb⟩ := h i hi
  obtain ⟨hperm, _, hbytes⟩ := hs
  refine ⟨by rw [hperm]; exact hx, ?_⟩
  rw [hbytes _ (hwx _ hx)]
  exact hb

theorem wx_schutz (m m' : Speicher) (hwx : WX m) (hs : Schutz m m') : WX m' := by
  intro x hx
  obtain ⟨hperm, hschr, _⟩ := hs
  rw [hschr]
  rw [hperm] at hx
  exact hwx x hx

/-- A laid-out straight-line program satisfies the trace premise. -/
theorem spurAn_layout (is : List Instr) (s : Zustand)
    (hk : ∀ i ∈ is, kanonischI i = true)
    (hf : ∀ i ∈ is, faelltDurchI i = true)
    (hwx : WX s.speicher) (hcode : CodeAt s.speicher s.rip (progBytes is)) :
    SpurAn is s := by
  induction is generalizing s with
  | nil => trivial
  | cons i rest ih =>
    simp only [progBytes] at hcode
    refine ⟨hk i (by simp), geholt_codeAt s _ (codeAt_links _ _ _ _ hcode)
      (encodeI_len i).2, ?_⟩
    intro s1 hs1
    obtain ⟨hschutz, hrip⟩ := stepI_rahmen i _ s s1 hs1
    have hr : s1.rip = ripNach s.rip (encodeI i).length := hrip (hf i (by simp))
    apply ih s1 (fun j hj => hk j (by simp [hj])) (fun j hj => hf j (by simp [hj]))
      (wx_schutz _ _ hwx hschutz)
    rw [hr]
    exact codeAt_schutz _ _ _ _ hwx hschutz (codeAt_rechts _ _ _ _ hcode)

/-- LAYOUT THEOREM: a straight-line program of canonical unified
    instructions, laid out back to back by `encodeI` at RIP in executable
    memory under W^X, runs under `byteschrittI` from actual memory exactly
    as `laufI` runs the instruction list: the same final state, and a
    refusal exactly when `laufI` refuses. Stores in the run cannot reach the
    code because W^X makes code non-writable and every family step only
    writes writable bytes (`stepI_rahmen`). -/
theorem laufBytesI_layout (is : List Instr) (s : Zustand)
    (hk : ∀ i ∈ is, kanonischI i = true)
    (hf : ∀ i ∈ is, faelltDurchI i = true)
    (hwx : WX s.speicher) (hcode : CodeAt s.speicher s.rip (progBytes is)) :
    laufBytesI is.length s = ausgangVon (laufI (is.map canonI) s) :=
  laufBytesI_spur is s (spurAn_layout is s hk hf hwx hcode)

/- CUTS (what is NOT proved here):
   - `laufBytesI_layout` covers STRAIGHT-LINE programs (`faelltDurchI`:
     no pilot jump/branch/call/ret). Programs with control flow are covered
     by the trace theorem `laufBytesI_spur`, whose premise `SpurAn` (the
     executed instruction's bytes open the window at the reached RIP) is
     NOT derived from a layout here; a branch-target layout theorem is open.
   - Code integrity comes from W^X (`WX`) at the start state plus
     `stepI_rahmen` (every family writes only writable bytes and keeps all
     permissions). Self-modifying code is not modelled beyond that: a
     writable executable byte is excluded by the premise, not handled.
   - The 64-bit address space wraps (`addrOff` is modular); the layout
     theorem needs no no-wrap premise because fetch and placement are both
     stated with `addrOff`, but it says nothing about where a wrapped
     program physically sits.
   - `ausgangVon none = verweigert` merges every refusal: a mul/div #DE
     trap, a failed memory access and a bad decode all become `verweigert`
     (see `ISA.stepIE` for the trap distinction).
   - No hardware, TSO, concurrency, timing or source-correspondence claim.
-/

#print axioms fetchDekodiertI_pilot
#print axioms byteschrittI_erweitert
#print axioms geholt_praefix_ausfuehrbar
#print axioms byteschrittI_kanonisch
#print axioms laufBytesI_spur
#print axioms Schutz_refl
#print axioms schreibbarN_an
#print axioms writeBytesN_geschuetzt
#print axioms write64_schutz
#print axioms write32_schutz
#print axioms schritt_rahmenI
#print axioms stepI_rahmen
#print axioms addrOff_ripNach
#print axioms holeFetchAux_codeAt
#print axioms geholt_codeAt
#print axioms codeAt_links
#print axioms codeAt_rechts
#print axioms codeAt_schutz
#print axioms wx_schutz
#print axioms spurAn_layout
#print axioms laufBytesI_layout

end Gabbro.Grammatik.X86
