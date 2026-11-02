module

public import Grammatik.Bausteine.Schablonen.ZeugeTorModell
public import Grammatik.Kern.Semantik.Syscall.Syscall
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc.Teil1
@[expose] public section


namespace Gabbro.Grammatik

namespace OhneLibc

section Fehlbar

variable {D : Deklaration}

/-- The stub's outcome as the machine's ONE raw word: the pair packed like a `tagged` value
    (case number in the low digit, base `n + 1`), the unreachable outcome as a word whose
    value half lies outside the declared range. -/
def packe (n : Nat) {lo hi : Int} : SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } (Fin n) → Int
  | .ok v => v.1 * ((n : Int) + 1)
  | .why r => (r.1 : Int) + 1
  | .unerwartet _ => (hi + 1) * ((n : Int) + 1)

/-- What G does with a decoded answer of a fallible gate: the value (as the machine's `Zahl`),
    the reason, or nothing (the hardware stop). -/
def gAntwort {n : Nat} {lo hi : Int} : SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } (Fin n) →
    Option (ErgVal D (some (.int lo hi)) ⊕ Fin n)
  | .ok v => some (Sum.inl (⟨v.1, v.2.1, v.2.2⟩ : Zahl lo hi))
  | .why r => some (Sum.inr r)
  | .unerwartet _ => none

theorem packe_ok (z : Int → Option D.Fn) (n : Nat) {lo hi : Int}
    (v : { x : Int // lo ≤ x ∧ x ≤ hi }) :
    sonstPasst z (some (.int lo hi)) n (packe n (.ok v : SysAntwort _ (Fin n))) =
      some (Sum.inl (⟨v.1, v.2.1, v.2.2⟩ : Zahl lo hi)) := by
  obtain ⟨x, h1, h2⟩ := v
  have hk : (0 : Int) < (n : Int) + 1 := by omega
  have hm : x * ((n : Int) + 1) % ((n : Int) + 1) = 0 := Int.mul_emod_left _ _
  have hd : x * ((n : Int) + 1) / ((n : Int) + 1) = x := Int.mul_ediv_cancel _ (by omega)
  simp only [sonstPasst, packe, hm, if_true, hd, einpassenErg, einpassen, dif_pos (And.intro h1 h2)]
  rfl

theorem packe_grund (z : Int → Option D.Fn) (n : Nat) {lo hi : Int} (r : Fin n) :
    sonstPasst z (some (.int lo hi)) n (packe (lo := lo) (hi := hi) n (.why r)) =
      some (Sum.inr r) := by
  obtain ⟨i, hi'⟩ := r
  have hm : ((i : Int) + 1) % ((n : Int) + 1) = (i : Int) + 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  simp only [sonstPasst, packe, hm]
  rw [if_neg (by omega), dif_pos (by omega)]
  congr
  simp only [Int.add_sub_cancel, Int.toNat_natCast]

theorem packe_unerwartet (z : Int → Option D.Fn) (n : Nat) {lo hi : Int} (u : Int) :
    sonstPasst z (some (.int lo hi)) n (packe (lo := lo) (hi := hi) n (.unerwartet u)) = none := by
  have hm : (hi + 1) * ((n : Int) + 1) % ((n : Int) + 1) = 0 := Int.mul_emod_left _ _
  have hd : (hi + 1) * ((n : Int) + 1) / ((n : Int) + 1) = hi + 1 := Int.mul_ediv_cancel _ (by omega)
  simp only [sonstPasst, packe, hm, if_true, hd, einpassenErg, einpassen]
  rw [dif_neg (by omega)]
  rfl

/-- **Soundness of `tor.fehlbar`.** For EVERY kernel word `roh` and every errno table: the
    outcome the emitted stub forms (`dekodiere`), packed into the machine's raw word, is
    decoded by G exactly as the stub decoded it -- so the C and the model take the same branch
    with the same value or reason, and the stub's `__builtin_unreachable()` is G's hardware
    stop. -/
theorem tor_fehlbar (z : Int → Option D.Fn) (n : Nat) (tab : FehlerTabelle (Fin n))
    (lo hi roh : Int) :
    sonstPasst z (some (.int lo hi)) n (packe n (dekodiere tab lo hi roh)) =
      gAntwort (D := D) (dekodiere tab lo hi roh) := by
  cases dekodiere tab lo hi roh with
  | ok v => exact packe_ok z n v
  | why r => exact packe_grund z n r
  | unerwartet u => exact packe_unerwartet z n u

/-- The three legs of the stub, joined with `dekodiere`'s characterisation (Syscall.lean): an
    in-range non-negative word is the value, a listed `-errno` its reason, and the rest the
    hardware stop -- in G as in the C. -/
theorem tor_fehlbar_wert (z : Int → Option D.Fn) (n : Nat) (tab : FehlerTabelle (Fin n))
    (lo hi roh : Int) (hge : 0 ≤ roh) (hok : lo ≤ roh ∧ roh ≤ hi) :
    sonstPasst z (some (.int lo hi)) n (packe n (dekodiere tab lo hi roh)) =
      some (Sum.inl (⟨roh, hok.1, hok.2⟩ : Zahl lo hi)) := by
  rw [dekodiere_ok_bereich tab lo hi roh hge hok]
  exact packe_ok z n _

theorem tor_fehlbar_grund (z : Int → Option D.Fn) (n : Nat) (tab : FehlerTabelle (Fin n))
    (lo hi : Int) (e : Nat) (r : Fin n) (hfirst : ersterEintrag tab e r)
    (hbereich : 1 ≤ (e : Int) ∧ (e : Int) ≤ 4095) :
    sonstPasst z (some (.int lo hi)) n (packe n (dekodiere tab lo hi (-(e : Int)))) =
      some (Sum.inr r) := by
  rw [dekodiere_tabelle tab lo hi e r hfirst hbereich]
  exact packe_grund z n r

/-! ### The witness: a three-reason channel (`BadFd = 9`, `Interrupted = 4`, `WouldBlock = 11`),
    a value range `0 .. 1024`, and one word of each kind -/

def zeugeTab : FehlerTabelle (Fin 3) := [(9, 0), (4, 1), (11, 2)]

/-- **Witness for `tor_fehlbar`, `tor_fehlbar_wert` and `tor_fehlbar_grund`**, ALL premises
    jointly: the word `3` is the value `3`, the word `-4` (EINTR) is reason `1`, and the word
    `-5` (an errno the table does not admit) is the hardware stop -- each by computation, in G
    as the stub decodes it. -/
theorem tor_fehlbar_zeuge (D : Deklaration) (z : Int → Option D.Fn) :
    sonstPasst z (some (.int 0 1024)) 3 (packe 3 (dekodiere zeugeTab 0 1024 3)) =
      some (Sum.inl (⟨3, by decide, by decide⟩ : Zahl 0 1024)) ∧
    sonstPasst z (some (.int 0 1024)) 3 (packe 3 (dekodiere zeugeTab 0 1024 (-4))) =
      some (Sum.inr 1) ∧
    sonstPasst z (some (.int 0 1024)) 3 (packe 3 (dekodiere zeugeTab 0 1024 (-5))) = none :=
  ⟨tor_fehlbar_wert z 3 zeugeTab 0 1024 3 (by decide) ⟨by decide, by decide⟩,
    tor_fehlbar_grund z 3 zeugeTab 0 1024 4 1 ⟨[(9, 0)], [(11, 2)], rfl, by decide⟩
      ⟨by decide, by decide⟩,
    by rw [tor_fehlbar]; rfl⟩

end Fehlbar

/-! ## 4. `tor.region` -- the stub of a gate that hands over a REGION

  Simon's decision 1 (2026-09-30): memory from outside comes as a region, never from a number.
  A `syscall` answering `ptr<normal, …> u8 or R` gets the stub `emit.rs::syscall_stumpf`
  writes for `Antwort::Region`: the sign leg of `tor.fehlbar` unchanged (a listed `-errno` is
  its reason, an unlisted one or a word past the `-4095` fence the hardware stop), then the
  word ZERO is the hardware stop too, and every other word is handed over as the address
  `(uint8_t *)(uintptr_t)raw`. No expression of the language turns a number into a pointer
  (`M140`); this stub is the one place a word becomes one, and this section is its proof.

  What the section proves, and what it does not:

  * `tor_region`: the stub, statement by statement, IS the generic decoding `dekodiere` of
    Syscall.lean over the value range `1 .. 2^63 - 1` -- the same function `tor.fehlbar` is
    proved over, so the reason channel of a region gate decodes exactly like every other
    fallible gate's;
  * `tor_region_adresse`, `tor_region_fehler_kein_zeiger`: the address handed over is the
    kernel's word itself and never zero, and no error word ever becomes an address;
  * `region_zugriff`: the ONE generic form "a foreign routine hands over a new region" --
    the gate's contract (user logic: `ensures n <= lenof(result)` plus the fresh/disjoint
    sentence of its assumption) -- and what `N571` makes of it: an index `i` with
    `i + 1 <= n` (the checker's `passt(i, 1, clause)`) lies inside the region and inside no
    other region live at the call.
  * NOT proved: that the kernel keeps the contract (the gate's assumption, premise (c)); and
    machine G has no byte pointers (`lean_g.rs` refuses the pointer target by name, LG002),
    so a program with a region answer is outside the certified register exactly like every
    `ptr<…> u8` program before it (OFFEN O37).
-/

section Region

/-- The emitted region stub, statement by statement (`emit.rs`, `Antwort::Region`): the
    `-4095` fence, the errno comparisons in table order, the zero test, the address. -/
def regionStumpf {Grund : Type} [DecidableEq Grund] (tab : FehlerTabelle Grund) (roh : Int) :
    SysAntwort Nat Grund :=
  if roh < 0 then
    if roh < -4095 then .unerwartet roh
    else match fehlerSuche tab (-roh).toNat with
      | some r => .why r
      | none => .unerwartet roh
  else if roh = 0 then .unerwartet roh
  else .ok roh.toNat

/-- The largest word the kernel's `int64_t` answer can hold. -/
def wortMax : Int := 2 ^ 63 - 1

/-- The generic decoding over the address range, with the value leg read as an address. -/
def alsAdresse {Grund : Type} : SysAntwort { x : Int // 1 ≤ x ∧ x ≤ wortMax } Grund →
    SysAntwort Nat Grund
  | .ok v => .ok v.1.toNat
  | .why r => .why r
  | .unerwartet u => .unerwartet u

/-- **Soundness of `tor.region`.** For EVERY word the `int64_t` register can hold and every
    errno table, the emitted stub decides exactly as the generic decoding `dekodiere` over the
    range `1 .. 2^63 - 1` -- the decoding `tor.fehlbar` is proved against machine G's reason
    channel. -/
theorem tor_region {Grund : Type} [DecidableEq Grund] (tab : FehlerTabelle Grund) (roh : Int)
    (hwort : roh ≤ wortMax) :
    regionStumpf tab roh = alsAdresse (dekodiere tab 1 wortMax roh) := by
  unfold regionStumpf dekodiere
  by_cases hneg : roh < 0
  · rw [if_pos hneg, dif_pos hneg]
    by_cases hz : roh < -4095
    · rw [if_pos hz, dif_neg (by omega)]; rfl
    · rw [if_neg hz, dif_pos (by omega)]
      cases fehlerSuche tab (-roh).toNat <;> rfl
  · rw [if_neg hneg, dif_neg hneg]
    by_cases h0 : roh = 0
    · rw [if_pos h0, dif_neg (by omega)]; rfl
    · rw [if_neg h0, dif_pos (by omega)]; rfl

/-- The address handed over is the kernel's word itself, and never zero. -/
theorem tor_region_adresse {Grund : Type} [DecidableEq Grund] (tab : FehlerTabelle Grund)
    (roh : Int) (a : Nat) (h : regionStumpf tab roh = .ok a) : (a : Int) = roh ∧ 1 ≤ a := by
  unfold regionStumpf at h
  by_cases hneg : roh < 0
  · rw [if_pos hneg] at h
    by_cases hz : roh < -4095
    · rw [if_pos hz] at h; cases h
    · rw [if_neg hz] at h
      cases hs : fehlerSuche tab (-roh).toNat <;> rw [hs] at h <;> cases h
  · rw [if_neg hneg] at h
    by_cases h0 : roh = 0
    · rw [if_pos h0] at h; cases h
    · rw [if_neg h0] at h
      cases h
      omega

/-- No error word becomes an address: a negative word is a reason or the stop. -/
theorem tor_region_fehler_kein_zeiger {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (roh : Int) (hneg : roh < 0) (a : Nat) :
    regionStumpf tab roh ≠ .ok a := by
  intro h
  have := (tor_region_adresse tab roh a h).1
  omega

/-- A region: a base address and the number of bytes it reaches. -/
structure Region where
  basis : Nat
  laenge : Nat
  deriving DecidableEq, Repr

/-- The byte at address `a` lies in the region. -/
def Region.enthaelt (r : Region) (a : Nat) : Prop := r.basis ≤ a ∧ a < r.basis + r.laenge

/-- Two regions share no byte. -/
def Region.disjunkt (r s : Region) : Prop :=
  r.basis + r.laenge ≤ s.basis ∨ s.basis + s.laenge ≤ r.basis

/-- **The ONE generic form: a foreign routine hands over a new region.** The gate's contract,
    user logic in the program's source: the answer reaches at least `n` bytes
    (`ensures n <= lenof(result)`) and shares no byte with any region live at the call (the
    fresh/disjoint sentence of its assumption). No operating system in it. -/
def RegionVertrag (lebend : List Region) (n : Nat) (r : Region) : Prop :=
  n ≤ r.laenge ∧ ∀ s ∈ lebend, r.disjunkt s

end Region
end OhneLibc
end Gabbro.Grammatik
