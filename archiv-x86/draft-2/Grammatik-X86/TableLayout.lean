/-
  File:      Grammatik/X86/TableLayout.lean
  Subject:   Computed table/global layout for direct x86-64 validation (lane 345, C1).

  Computed extents, widths and alignments for source tables plus carrier
  enumeration, all decided from the source `UProg` itself; any Rust layout
  hint is re-decided, never a premise. Over the canonical `Typen`/`Speicher`
  vocabulary with `Bild.Abschnitt` mapping and `Regionen` allocation facts.
  No source admission is tightened; full source-to-byte correspondence stays OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Bild
import Grammatik.X86.Regionen
import Grammatik.Parser.UebersetzeAllg

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Byte width of one field slot in the computed layout: 8 bytes per field. -/
def feldWeite : Nat := 8

/-- Computed byte width of one source field type in this layout.

    One word (8 bytes) per numeric slot, one byte per `bool` slot.
    This is a layout choice proved of the computed function, not a C
    `sizeof` fact and not a hardware claim. -/
def typWeite : Gabbro.Grammatik.Ty → Nat
  | .bool => 1
  | _ => 8

/-- Width of one table row: sum of its fields' computed widths. -/
def zeilenWeite (tab : UTab) : Nat :=
  tab.felder.foldl (fun acc p => acc + if tab.bools.contains p.1 then 1 else 8) 0

/-- Byte extent of one table: row count times row width (`count ≤ 0` gives 0). -/
def tabUmfang (tab : UTab) : Nat :=
  tab.count.toNat * zeilenWeite tab

/-- One computed table placement: source table index plus target extent. -/
structure TabLayout where
  tab : Nat
  basis : Nat
  len : Nat
  ausr : Nat
  deriving DecidableEq, Repr

/-- Place a table list contiguously from a cursor, aligning each base up. -/
def legeTabellen : List UTab → Nat → Nat → Nat → List TabLayout
  | [], _, _, _ => []
  | tab :: rest, idx, cursor, ausr =>
    match ausricht cursor ausr with
    | none => []
    | some start =>
      { tab := idx, basis := start, len := tabUmfang tab, ausr := ausr } ::
        legeTabellen rest (idx + 1) (start + tabUmfang tab) ausr

/-- Computed layout of a source unit from a base and an alignment. -/
def layoutFuer (u : UProg) (basis ausr : Nat) : List TabLayout :=
  legeTabellen u.tabellen 0 basis ausr

/-- One entry as a target region (readable/writable data, never executable). -/
def alsRegion (e : TabLayout) : Region :=
  { basis := e.basis, len := e.len, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- Decided entry check: nonempty extent, declared alignment, no 64-bit wrap. -/
def eintragOk (e : TabLayout) : Bool :=
  decide (0 < e.len ∧ 0 < e.ausr ∧ e.basis % e.ausr = 0 ∧ e.basis + e.len ≤ 2 ^ 64)

/-- Pairwise disjointness of the placed extents. -/
def paarOk : List TabLayout → Bool
  | [] => true
  | e :: rest =>
    rest.all (fun t => regionDisjunkt (alsRegion e) (alsRegion t)) && paarOk rest

/-- The full layout check: every entry plus pairwise disjointness. -/
def layoutOk (es : List TabLayout) : Bool :=
  es.all eintragOk && paarOk es

/-- One entry as a data image section (BSS-style: no file bytes). -/
def abschnittVon (e : TabLayout) : Abschnitt :=
  { dateiOff := 0, dateiLen := 0, vaddr := e.basis, memLen := e.len,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := e.ausr }

/-- A Rust layout hint is accepted only if it equals the recomputation. -/
def hinweisOk (u : UProg) (basis ausr : Nat) (hinweis : List TabLayout) : Bool :=
  decide (hinweis = layoutFuer u basis ausr) && layoutOk hinweis

/-- Carrier enumeration: one `(table, row, field)` per slot, from the source. -/
def slotAufz (u : UProg) : List (Nat × Nat × Nat) :=
  u.tabellen.toArray.toList.zipIdx.flatMap fun ⟨tab, ti⟩ =>
    List.range tab.count.toNat |>.flatMap fun row =>
      List.range tab.felder.length |>.map fun fi => (ti, row, fi)

/-- A checked hint equals the recomputation and passes the layout check. -/
theorem hinweisOk_layoutOk (u : UProg) (basis ausr : Nat)
    (hinweis : List TabLayout)
    (h : hinweisOk u basis ausr hinweis = true) :
    hinweis = layoutFuer u basis ausr ∧ layoutOk hinweis = true := by
  unfold hinweisOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨of_decide_eq_true h1, h2⟩

/-- An accepted entry maps to an image section whose declared alignment holds. -/
theorem abschnittVon_ausr (e : TabLayout)
    (h : eintragOk e = true) :
    ausrOk 0 (abschnittVon e) = true := by
  unfold eintragOk at h
  unfold abschnittVon ausrOk
  simp only [decide_eq_true_eq] at h ⊢
  obtain ⟨_, hausr, hmod, _⟩ := h
  refine ⟨hausr, ?_⟩
  simpa using hmod

/-! ## Witness unit: one table with a writing function. -/

/-- Witness table: two rows, one numeric field `x in 0 .. 100`. -/
def zeugenTab : UTab :=
  { name := "konto", count := 2, felder := [("x", (0, 100))], bools := [] }

/-- Witness function: writes table `konto`, straight-line shape. -/
def zeugenFn : UFn :=
  { name := "setze", params := [], parten := [], ergebnis := none,
    held := [], schreibt := ["konto"], sichert := [], saetze := [],
    rueck := URet.keine }

/-- Witness unit: non-empty, with a table some function writes. -/
def zeugenU : UProg :=
  { tabellen := [zeugenTab], sperren := [], fns := [zeugenFn] }

/-- The witness function really writes the witness table. -/
theorem zeugenU_schreibt :
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] := by
  decide

/-- The computed witness layout is the one 16-byte extent at 4096. -/
theorem zeugenLayout_wert :
    layoutFuer zeugenU 4096 8 =
      [{ tab := 0, basis := 4096, len := 16, ausr := 8 }] := by
  decide

/-- The computed witness layout is accepted. -/
theorem zeugenLayout_ok :
    layoutOk (layoutFuer zeugenU 4096 8) = true := by
  decide

/-- The witness carrier enumeration is nonempty. -/
theorem zeugenSlot_ne : slotAufz zeugenU ≠ [] := by
  decide

/-! ## Refusals: overlap and unaligned `aligned N` placement. -/

/-- OVERLAP REFUSAL: extents `[4096, 4112)` and `[4104, 4120)` share bytes. -/
theorem ueberlapp_verweigert :
    layoutOk [{ tab := 0, basis := 4096, len := 16, ausr := 8 },
      { tab := 1, basis := 4104, len := 16, ausr := 8 }] = false := by
  decide

/-- ALIGNMENT REFUSAL: base 4104 against a declared `aligned 4096`. -/
theorem unausgerichtet_verweigert :
    layoutOk [{ tab := 0, basis := 4104, len := 16, ausr := 4096 }] = false := by
  decide

/-! ## Joint witness: layout, enumeration, writer and a memory change. -/

/-- Witness memory: zero bytes, fully readable/writable, never executable. -/
def zeugenMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- JOINT WITNESS: the computed layout is accepted, the carrier
    enumeration is nonempty, some function writes the table, the layout
    base lies in its own extent, and a nonzero word is stored, read back
    and observably changes the byte at the layout base. -/
theorem layout_zeuge :
    layoutOk (layoutFuer zeugenU 4096 8) = true ∧
    slotAufz zeugenU ≠ [] ∧
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    inRegion (alsRegion { tab := 0, basis := 4096, len := 16, ausr := 8 }) 4096 = true ∧
    ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenLayout_ok, zeugenSlot_ne, zeugenU_schreibt, by decide, ?_⟩
  have hwr_perm : schreibbar8 zeugenMem (natAdresse 4096) = true := by decide
  have hrd_perm : lesbar8 zeugenMem (natAdresse 4096) = true := by decide
  have hwr : write64 zeugenMem (natAdresse 4096) 42 =
      some { zeugenMem with
        bytes := writeBytes zeugenMem (natAdresse 4096) 42 } := by
    unfold write64
    rw [if_pos hwr_perm]
  refine ⟨zeugenMem, _, natAdresse 4096, 42, by decide, hwr,
    read64_nach_write64 _ _ _ _ hwr hrd_perm, ?_⟩
  have hhit := writeBytesN_hit zeugenMem (natAdresse 4096) 42 8 0
    (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hnull : zeugenMem.bytes (natAdresse 4096) = BitVec.ofNat 8 0 := rfl
  show zeugenMem.bytes (natAdresse 4096) ≠
    writeBytesN zeugenMem (natAdresse 4096) 42 8 (natAdresse 4096)
  rw [hnull, hhit]
  decide

/- CUTS:
   - No source-to-target correspondence: nothing here claims the computed
     extents are the lowering of any source access, duty, cost, lock or
     template. Per-access refinement into W/GX is OPEN (TSO bridge lane).
   - No validator soundness: `layoutOk`/`hinweisOk` are decided admission
     predicates over extents, not a `valX86_sound` proof. The consumer side
     (shared IR 287, validator skeleton C5) is WAITING, not invented here.
   - No hardware claim: refusal is validator/profile admission, never an
     invented hardware fault. Actual x86 allows many unaligned ordinary
     accesses; declared alignment is imposed only where the layout demands
     it, and the checked content is bytes/permissions, not timing.
   - No width correspondence: `typWeite` (bool 1 byte, else one word) is a
     layout choice proved of the computed function, not a C `sizeof` fact;
     the source range-to-byte bridge (QUELLBRUECKE §3.1 follow-up) is OPEN.
   - No OS/loader assumption: `abschnittVon` maps extents to BSS-style data
     sections purely; the loader contract and entry predicates (C4) are OPEN.
   - Empty tables (`count ≤ 0`) have extent 0 and are refused by `eintragOk`;
     globals/statics/arenas/gates have no layout form here (QUELLBRUECKE
     §3 gaps 2/4/6 stay OPEN).
-/

#print axioms feldWeite
#print axioms typWeite
#print axioms zeilenWeite
#print axioms tabUmfang
#print axioms legeTabellen
#print axioms layoutFuer
#print axioms hinweisOk_layoutOk
#print axioms abschnittVon_ausr
#print axioms zeugenU_schreibt
#print axioms zeugenLayout_wert
#print axioms zeugenLayout_ok
#print axioms zeugenSlot_ne
#print axioms ueberlapp_verweigert
#print axioms unausgerichtet_verweigert
#print axioms layout_zeuge

end Gabbro.Grammatik.X86
