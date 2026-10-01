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

end Gabbro.Grammatik.X86
