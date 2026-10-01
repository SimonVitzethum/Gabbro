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

end Gabbro.Grammatik.X86
