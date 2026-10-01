/-
  Byte fetch and single-step from actual executable memory (lane 319).

  Couples permission-checked fetch from actual instruction memory to the
  existing byte decoder (`Codec.decode`) and instruction step
  (`Ausfuehrung.schritt`). Fetch reads the bytes at `Zustand.rip` from the
  state's ACTUAL `Speicher.bytes`, gated on EXECUTE permission only (never
  data-read permission), and decodes them with the independent decoder.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86

/-- Fetch cap: at most 15 bytes, the x86 maximum instruction length. -/
def fetchCap : Nat := 15

/-- Execute permission for the first `n` bytes at `a`. Fetch checks
    execute permission ONLY; data-read permission (`lesbar`) is never
    consulted here. -/
def ausfuehrbarN : Speicher → Adresse → Nat → Bool
  | _, _, 0 => true
  | m, a, n+1 => ausfuehrbarN m a n && m.ausfuehrbar (addrOff a n)

/-- Actual byte fetch: the executable prefix of memory at `a`, capped at
    `cap` bytes. Stops before the first non-executable byte, so a short
    instruction never requires execute access beyond its own bytes, and
    fetch never over-reads past an executable boundary. -/
def holeFetchAux (m : Speicher) (a : Adresse) (off : Nat) : Nat → List Byte
  | 0 => []
  | n+1 =>
    if m.ausfuehrbar (addrOff a off) then
      m.bytes (addrOff a off) :: holeFetchAux m a (off + 1) n
    else []

/-- The fetched window of a state: actual bytes at `rip`, executable
    prefix only, capped at 15. -/
def geholt (s : Zustand) : List Byte :=
  holeFetchAux s.speicher s.rip 0 fetchCap

/-- Fetch and decode: decode the ACTUAL fetched bytes with the
    independent decoder, then check consumed-length/remaining-suffix
    consistency (`laenge + rest = fetched`), decode-length validity and
    execute permission of the consumed prefix. Truncated, non-canonical,
    inaccessible or length-inconsistent inputs refuse with `none`. The
    decoded value is never trusted without this check. -/
def fetchDekodiert (s : Zustand) : Option (Decodiert × List Byte) :=
  match decode (geholt s) with
  | none => none
  | some (d, rest) =>
    if d.laenge + rest.length == (geholt s).length &&
        laengeOk d.laenge && ausfuehrbarN s.speicher s.rip d.laenge
    then some (d, rest)
    else none

/-- Byte-step outcome: success carries the successor state, refusal is
    explicit. There is deliberately NO halt/termination constructor:
    `verweigert` means no successful transition, never normal program
    termination; termination (empty caller on `ret`, thread end) is OPEN. -/
inductive ByteAusgang where
  | weiter : Zustand → ByteAusgang
  | verweigert : ByteAusgang

/-- One byte step from actual memory: fetch, decode, then the existing
    `schritt`. Takes ONLY the state: no caller-supplied decoded value
    ever becomes a trusted fetch, so a forged `Decodiert` cannot inject
    an instruction. Any fetch or step failure is `verweigert`. -/
def byteschritt (s : Zustand) : ByteAusgang :=
  match fetchDekodiert s with
  | none => .verweigert
  | some (d, _) =>
    match schritt d s with
    | none => .verweigert
    | some s' => .weiter s'

/-! ## Fetch bounds: the window never exceeds its cap. -/

/-- Fetch never exceeds its cap: the fetched list is at most `cap` long. -/
theorem holeFetchAux_laenge_le (m : Speicher) (a : Adresse) (off cap : Nat) :
    (holeFetchAux m a off cap).length ≤ cap := by
  induction cap generalizing off with
  | zero => simp [holeFetchAux]
  | succ n ih =>
    simp only [holeFetchAux]
    split
    · simp only [List.length_cons]
      have h := ih (off + 1)
      omega
    · simp

/-- The state window holds at most 15 bytes. -/
theorem geholt_laenge_le (s : Zustand) :
    (geholt s).length ≤ fetchCap := by
  unfold geholt
  exact holeFetchAux_laenge_le s.speicher s.rip 0 fetchCap

/-- Execute permission is prefix-closed: a granted `n`-prefix grants
    every shorter prefix. -/
theorem ausfuehrbarN_vorsilbe (m : Speicher) (a : Adresse) (k n : Nat)
    (hle : k ≤ n) (h : ausfuehrbarN m a n = true) :
    ausfuehrbarN m a k = true := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := Nat.le_zero.mp hle
    subst hk
    rfl
  | succ n ih =>
    by_cases hk : k ≤ n
    · have hn : ausfuehrbarN m a n = true := by
        simp only [ausfuehrbarN, Bool.and_eq_true] at h
        exact h.1
      exact ih k hk hn
    · have hk2 : k = n + 1 := by omega
      subst hk2
      exact h

/-- Every fetched byte sits at an executable address: position `i` of the
    fetch is `m.bytes (addrOff a (off + i))` under execute permission. -/
theorem holeFetchAux_ausfuehrbar (m : Speicher) (a : Adresse) (off cap i : Nat)
    (h : i < (holeFetchAux m a off cap).length) :
    m.ausfuehrbar (addrOff a (off + i)) = true := by
  induction cap generalizing off i with
  | zero => simp [holeFetchAux] at h
  | succ n ih =>
    simp only [holeFetchAux] at h
    by_cases hc : m.ausfuehrbar (addrOff a off) = true
    · rw [if_pos hc] at h
      simp only [List.length_cons] at h
      cases i with
      | zero =>
        simpa using hc
      | succ j =>
        have hj : j < (holeFetchAux m a (off + 1) n).length := by omega
        have hjx := ih (off + 1) j hj
        have he : off + 1 + j = off + (j + 1) := by omega
        rw [he] at hjx
        exact hjx
    · rw [if_neg hc] at h
      simp at h

/-- Every byte of the state window sits at an executable address. -/
theorem geholt_nur_ausfuehrbar (s : Zustand) (i : Nat)
    (h : i < (geholt s).length) :
    s.speicher.ausfuehrbar (addrOff s.rip i) = true := by
  have hx := holeFetchAux_ausfuehrbar s.speicher s.rip 0 fetchCap i
    (by simpa [geholt] using h)
  simpa using hx

/-! ## Generic correspondence: fetch to decoder, byte step to `schritt`. -/

/-- FETCH-TO-DECODER: a successful fetch decodes the actual fetched bytes
    and carries its checked facts: consumed length plus remaining suffix
    is the fetched window, the length is valid, and the consumed prefix
    is executable. -/
theorem fetchDekodiert_entspricht (s : Zustand) (d : Decodiert)
    (rest : List Byte) (h : fetchDekodiert s = some (d, rest)) :
    decode (geholt s) = some (d, rest) ∧
      d.laenge + rest.length = (geholt s).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN s.speicher s.rip d.laenge = true := by
  unfold fetchDekodiert at h
  generalize hg : decode (geholt s) = g at h ⊢
  cases g with
  | none =>
    simp at h
  | some pr =>
    obtain ⟨d', rest'⟩ := pr
    dsimp only at h
    by_cases hc : (d'.laenge + rest'.length == (geholt s).length &&
      laengeOk d'.laenge && ausfuehrbarN s.speicher s.rip d'.laenge) = true
    · rw [if_pos hc] at h
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hlen, hok⟩, hexe⟩ := hc
      refine ⟨rfl, ?_, hok, hexe⟩
      rw [beq_iff_eq] at hlen
      exact hlen
    · rw [if_neg hc] at h
      cases h

/-- BYTE-STEP-TO-SCHRITT (success): the byte step runs the existing
    `schritt` on the fetched instruction. -/
theorem byteschritt_weiter (s s' : Zustand) (d : Decodiert)
    (rest : List Byte) (hf : fetchDekodiert s = some (d, rest))
    (hs : schritt d s = some s') :
    byteschritt s = .weiter s' := by
  unfold byteschritt
  simp only [hf, hs]

/-- BYTE-STEP-TO-SCHRITT (fetch refusal): no fetch means no transition.
    This `verweigert` is the absence of a transition, never a claim of
    normal program termination. -/
theorem byteschritt_verweigert_ohne_fetch (s : Zustand)
    (hf : fetchDekodiert s = none) :
    byteschritt s = .verweigert := by
  unfold byteschritt
  simp only [hf]

/-- BYTE-STEP-TO-SCHRITT (step refusal): a fetched instruction whose
    `schritt` fails (bad length, failed memory access) is no transition. -/
theorem byteschritt_verweigert_ohne_schritt (s : Zustand) (d : Decodiert)
    (rest : List Byte) (hf : fetchDekodiert s = some (d, rest))
    (hs : schritt d s = none) :
    byteschritt s = .verweigert := by
  unfold byteschritt
  simp only [hf, hs]

/-- A successful fetch uses only executable bytes within its stated
    prefix: the consumed prefix is executable, it fits the fetched
    window, and the window fits the 15-byte cap. Fetch never demands
    execute access beyond the consumed prefix. -/
theorem fetch_nutzt_nur_praefix (s : Zustand) (d : Decodiert)
    (rest : List Byte) (hf : fetchDekodiert s = some (d, rest)) :
    ausfuehrbarN s.speicher s.rip d.laenge = true ∧
      d.laenge ≤ (geholt s).length ∧ (geholt s).length ≤ fetchCap := by
  obtain ⟨_, hlen, _, hexe⟩ := fetchDekodiert_entspricht s d rest hf
  refine ⟨hexe, by omega, geholt_laenge_le s⟩

/-! ## Canonical agreement for arbitrary admitted instructions. -/

/-- CANONICAL AGREEMENT: for an ARBITRARY admitted instruction, fetching
    its canonical encoding from actual executable memory agrees with the
    existing `schritt`. Proved from the round-trip instances, so the open
    arbitrary-input decoder length soundness is not needed here. -/
theorem kanonisch_schritt_ueberein (b : Befehl) (s : Zustand)
    (suffix : List Byte) (hwin : geholt s = encode b ++ suffix)
    (hexe : ausfuehrbarN s.speicher s.rip (encode b).length = true) :
    fetchDekodiert s = some (⟨b, (encode b).length⟩, suffix) ∧
      byteschritt s = match schritt ⟨b, (encode b).length⟩ s with
        | none => .verweigert
        | some s' => .weiter s' := by
  have hrt := roundtrip b suffix
  rw [← hwin] at hrt
  have hlen := encode_len b
  have hok : laengeOk (encode b).length = true := by
    simp only [laengeOk, decide_eq_true_eq]
    exact hlen
  have hlen_eq : (encode b).length + suffix.length = (geholt s).length := by
    rw [hwin, List.length_append]
  have hbeq : ((encode b).length + suffix.length == (geholt s).length) = true := by
    rw [beq_iff_eq]
    exact hlen_eq
  have hf : fetchDekodiert s = some (⟨b, (encode b).length⟩, suffix) := by
    unfold fetchDekodiert
    rw [hrt]
    dsimp only
    rw [if_pos (by simp [hbeq, hok, hexe])]
  refine ⟨hf, ?_⟩
  unfold byteschritt
  simp only [hf]

/-! ## Witness observations: projections and a bounded byte run. -/

/-- Observe the RIP of a byte-step outcome (`none` on refusal). -/
def ausgangRip : ByteAusgang → Option Adresse
  | .weiter s => some s.rip
  | .verweigert => none

/-- Observe one memory byte of a byte-step outcome (`none` on refusal). -/
def ausgangByte (a : Adresse) : ByteAusgang → Option Byte
  | .weiter s => some (s.speicher.bytes a)
  | .verweigert => none

/-- Observe one register of a byte-step outcome (`none` on refusal). -/
def ausgangReg (r : Register) : ByteAusgang → Option Wort
  | .weiter s => some (s.register r)
  | .verweigert => none

/-- Bounded byte run: `n` byte steps from a state; refusal aborts loudly.
    A witness runner only: fuel exhaustion answers `weiter`, so no
    termination claim is made here. -/
def laufBytes : Nat → Zustand → ByteAusgang
  | 0, s => .weiter s
  | n+1, s =>
    match byteschritt s with
    | .verweigert => .verweigert
    | .weiter s' => laufBytes n s'

/-! ## Witness memory: a MOV/STORE/LOAD chain in actual bytes. -/

/-- Witness program bytes from 4096: `mov rax, 42` (10) ++
    `store [rbx], rax` (7) ++ `load rcx, [rbx]` (7), consecutive. -/
def ketteProg : List Byte :=
  [natByte 72, natByte 184, natByte 42, natByte 0, natByte 0,
   natByte 0, natByte 0, natByte 0, natByte 0, natByte 0,
   natByte 72, natByte 137, natByte 131, natByte 0, natByte 0,
   natByte 0, natByte 0,
   natByte 72, natByte 139, natByte 139, natByte 0, natByte 0,
   natByte 0, natByte 0]

/-- The same layout with the first opcode byte forged (REX.X set):
    non-canonical, so fetch must refuse it. -/
def ketteProgFalsch : List Byte :=
  natByte 74 :: ketteProg.drop 1

/-- Program bytes over addresses from `basis`; zero elsewhere. -/
def bytesAusProg (prog : List Byte) (basis : Nat) (a : Adresse) : Byte :=
  if a.toNat < basis then BitVec.ofNat 8 0
  else prog.getD (a.toNat - basis) (BitVec.ofNat 8 0)

/-- Code window executable: 4096..4128 (covers every 15-byte fetch). -/
def ketteExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4128)

/-- Data cell readable and writable: 8192..8200. Code is deliberately
    NOT data-readable: fetch needs execute, never read, permission. -/
def ketteDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness memory: the chain program at 4096, the data cell at 8192. -/
def ketteSpeicher : Speicher :=
  { bytes := bytesAusProg ketteProg 4096
    lesbar := ketteDaten
    schreibbar := ketteDaten
    ausfuehrbar := ketteExec }

/-- Witness registers: `rbx` names the data cell, everything else zero. -/
def ketteReg : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0

/-- Witness flags: nothing set. -/
def witnessFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Witness start state: chain at 4096, data cell at 8192. -/
def ketteStart : Zustand :=
  { register := ketteReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher := ketteSpeicher }

/-- MEMORY-CHANGING actual-byte witness: the MOV/STORE/LOAD chain fetched
    from real bytes at `rip` moves 42 into `rcx` and observably changes
    the data cell from zero to 42. Code needs no data-read permission:
    fetch checks execute only. -/
theorem kette_mov_store_load :
    ausgangReg .rcx (laufBytes 3 ketteStart) = some 42 ∧
      ausgangByte (BitVec.ofNat 64 8192) (laufBytes 2 ketteStart) =
        some (natByte 42) ∧
      ketteStart.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      ketteStart.speicher.lesbar (BitVec.ofNat 64 4096) = false := by
  decide

/-- Witness start with the forged first opcode byte at the executed rip. -/
def ketteStartFalsch : Zustand :=
  { ketteStart with
    speicher := { ketteSpeicher with
      bytes := bytesAusProg ketteProgFalsch 4096 } }

/-- ALTERED-OPCODE REFUSAL: forging one executed opcode byte (REX.X set)
    turns the stepping instruction into a refusal, while the intact bytes
    step past the 10-byte `mov` to 4106. The changed byte governs the
    executed instruction; no separate unexecuted buffer is checked. -/
theorem opcode_geaendert_verweigert :
    ausgangRip (byteschritt ketteStartFalsch) = none ∧
    ausgangRip (byteschritt ketteStart) = some (BitVec.ofNat 64 4106) := by
  decide

/-- Truncated witness: a `jump32` opcode with only its first byte
    executable; the displacement is cut off by the permission boundary. -/
def stumpfStart : Zustand :=
  { register := ketteReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := fun a =>
          if a.toNat = 4096 then natByte 233 else BitVec.ofNat 8 0
        lesbar := fun _ => true
        schreibbar := fun _ => true
        ausfuehrbar := fun a => decide (a.toNat = 4096) } }

/-- TRUNCATED-PREFIX REFUSAL: the cut-off jump has no transition. -/
theorem praefix_abgeschnitten_verweigert :
    ausgangRip (byteschritt stumpfStart) = none := by
  decide

/-- Execute-denied witness: a `ret` byte that is data-readable but not
    executable. -/
def ohneExecStart : Zustand :=
  { register := ketteReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := fun a =>
          if a.toNat = 4096 then natByte 195 else BitVec.ofNat 8 0
        lesbar := fun _ => true
        schreibbar := fun _ => true
        ausfuehrbar := fun _ => false } }

/-- EXECUTE-DENIED REFUSAL: readability without executability admits no
    fetch. Execute permission is distinct from data-read permission. -/
theorem ohne_exec_verweigert :
    ausgangRip (byteschritt ohneExecStart) = none ∧
    ohneExecStart.speicher.lesbar (BitVec.ofNat 64 4096) = true := by
  decide

/-- Boundary witness: a valid `ret` whose following bytes are
    non-executable; the stack top holds return address `0x3000`. -/
def retRandStart : Zustand :=
  { register := fun q =>
      if q = Register.rsp then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := fun a =>
          if a.toNat = 4096 then natByte 195
          else if a.toNat = 8192 then natByte 0
          else if a.toNat = 8193 then natByte 48
          else BitVec.ofNat 8 0
        lesbar := ketteDaten
        schreibbar := ketteDaten
        ausfuehrbar := fun a => decide (a.toNat = 4096) } }

/-- RET AT THE BOUNDARY: fetch takes only the one executable `ret` byte
    and steps to the popped address; it never over-reads into the
    non-executable suffix. -/
theorem ret_an_grenze_ohne_ueberlesen :
    ausgangRip (byteschritt retRandStart) = some (BitVec.ofNat 64 12288) := by
  decide

/-- Jump witness with a variable first displacement byte: `jump32` from
    4096, post-decode address 4101, target 4101 plus the displacement. -/
def sprungStart (d0 : Byte) : Zustand :=
  { register := ketteReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := fun a =>
          if a.toNat = 4096 then natByte 233
          else if a.toNat = 4097 then d0
          else if a.toNat = 4098 then natByte 0
          else if a.toNat = 4099 then natByte 0
          else if a.toNat = 4100 then natByte 0
          else BitVec.ofNat 8 0
        lesbar := fun _ => false
        schreibbar := fun _ => false
        ausfuehrbar := ketteExec } }

/-- CHANGED BYTE, CHANGED TARGET: one forged displacement byte moves the
    executed jump from 4117 to 4118. Needs no data permission at all. -/
theorem sprungziel_folgt_byte :
    ausgangRip (byteschritt (sprungStart (natByte 16))) =
      some (BitVec.ofNat 64 4117) ∧
    ausgangRip (byteschritt (sprungStart (natByte 17))) =
      some (BitVec.ofNat 64 4118) := by
  decide

/- CUTS:
    Proved here: executable-prefix fetch of actual memory bytes capped at
    15 (`holeFetchAux`/`geholt` with length and per-byte execute facts),
    fetch-to-decoder correspondence with runtime length/suffix/permission
    checks (`fetchDekodiert_entspricht`), byte-step-to-`schritt`
    correspondence (`byteschritt_weiter`, both `verweigert` directions),
    prefix-only execute use (`fetch_nutzt_nur_praefix`,
    `geholt_nur_ausfuehrbar`), canonical agreement for an arbitrary
    admitted instruction from round-trip instances
    (`kanonisch_schritt_ueberein`), and concrete actual-byte witnesses: a
    memory-changing MOV/STORE/LOAD chain, altered-opcode refusal, a
    changed displacement moving the jump target, truncated-prefix refusal,
    execute-denied refusal with readability held, and a valid RET at an
    executable boundary with non-executable suffix.
    NOT proved here, and not claimed:
    - No physical hardware claim: fetch runs over the model `Speicher`
      function, not silicon; caches, TLBs, store buffers and
      self-modifying-code coherence are OPEN (TSO-bridge lane business).
    - No whole-source or whole-binary theorem: no source correspondence,
      no image coverage, no multi-step control-flow validation, no entry,
      ABI, relocation or cost claim.
    - No termination claim: `verweigert` is the absence of a successful
      transition, never normal program termination; `ret` with an empty
      caller and thread end are OPEN, and `laufBytes` fuel exhaustion
      answers `weiter`, not halt.
    - Arbitrary-input decoder length soundness is OPEN: the statement
      `forall bs d rest, decode bs = some (d, rest) ->
        d.laenge + rest.length = bs.length /\ 1 <= d.laenge /\ d.laenge <= 15`
      is not proved here (it needs case analysis over every decoder path
      on arbitrary byte lists; lane 279 left exactly this open). Fetch
      does not depend on it: `fetchDekodiert` checks the equation at
      runtime and refuses on mismatch, and canonical instances go through
      the round-trip theorems.
    - No concurrency, aligned-atomic/LOCK, interrupt, entry, ABI,
      relocation or source-cost claim; no second decoder, ISA, word/memory
      or instruction semantics beyond the reused 272/279/271 definitions.
    - No new hardware or software assumptions: the only gate is the
      checked execute permission of the consumed prefix.
-/

#print axioms holeFetchAux_laenge_le
#print axioms geholt_laenge_le
#print axioms ausfuehrbarN_vorsilbe
#print axioms holeFetchAux_ausfuehrbar
#print axioms geholt_nur_ausfuehrbar
#print axioms fetchDekodiert_entspricht
#print axioms byteschritt_weiter
#print axioms byteschritt_verweigert_ohne_fetch
#print axioms byteschritt_verweigert_ohne_schritt
#print axioms fetch_nutzt_nur_praefix
#print axioms kanonisch_schritt_ueberein
#print axioms kette_mov_store_load
#print axioms opcode_geaendert_verweigert
#print axioms praefix_abgeschnitten_verweigert
#print axioms ohne_exec_verweigert
#print axioms ret_an_grenze_ohne_ueberlesen
#print axioms sprungziel_folgt_byte

end Gabbro.Grammatik.X86
