module

public import Core.Katalog.Seiten
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Reserviert

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # A translation served by the cache view keeps its frame reserved

`MmuSicht.tlb` is the MMU's cache view: core, space and page to the entry that core holds cached.
`TranslationCache.sicht` reads that view out of the finite cell list. A translation the cache
answers therefore uses one of the frame's cells. `TlbGedeckt` explains that cell by an active table
entry or a pending token, and `nicht_unreserviert` turns the cover into a refusal of every region
operation on the frame. This connects the cache invariant to the address the MMU actually returns.

The statement is over the cache view alone (`tables := fun _ _ => none`): a translation served by a
table entry on a cache miss needs a separate table invariant, which `TlbGedeckt` does not carry. -/

/-- The entry a core caches for a space and a page, if any. Several cells for one page may coexist;
    the first one answers, and the cover invariant holds of every cell, so the choice is immaterial. -/
def TranslationCache.sicht (cache : TranslationCache) (core space page : Nat) : Option Seiteneintrag :=
  (cache.zellen.find? (fun zelle =>
    zelle.kern == core && zelle.raum == space && zelle.seite == page)).map TlbZelle.eintrag

/-- A successful translation over the cache view returns an address in a reserved frame: the access
    at `phys` is not `unreserved`, so no region operation can hand that frame out again. -/
theorem uebersetze_sicher {frame : MemFrame} (inv : frame.TlbGedeckt)
    (z : ZielDaten) (core space addr : Nat) (right : Speicherdienst) {phys gen : Nat}
    (h : uebersetze z { tables := fun _ _ => none, tlb := frame.tlb.sicht } core space addr right =
      .ok (phys, gen)) :
    frame.unreserved z.seitengranule ⟨phys, phys + 1⟩ = false := by
  have gpos : 0 < z.seitengranule := by
    rw [ZielDaten.seitengranule]
    exact Nat.two_pow_pos z.pageShift
  unfold Katalog.uebersetze at h
  by_cases hv : z.virtuell addr
  · simp only [hv, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h
    generalize hs : frame.tlb.sicht core space (addr / z.seitengranule) = found at h
    cases found with
    | none =>
        cases h
    | some entry =>
        by_cases hbig : entry.frame * z.seitengranule + addr % z.seitengranule ≥
            2 ^ z.physicalBits
        · simp only [Option.orElse_some, hbig, ↓reduceIte] at h
          cases h
        · simp only [Option.orElse_some, hbig, ↓reduceIte] at h
          by_cases hright : right ∈ entry.rights
          · simp only [hright, ↓reduceIte] at h
            have hphys : phys = entry.frame * z.seitengranule + addr % z.seitengranule := by
              exact (congrArg Prod.fst (Except.ok.inj h)).symm
            unfold TranslationCache.sicht at hs
            generalize hfind : frame.tlb.zellen.find? (fun zelle =>
                zelle.kern == core && zelle.raum == space && zelle.seite == addr / z.seitengranule) =
              foundCell at hs
            cases foundCell with
            | none =>
                cases hs
            | some zelle =>
                simp only [Option.map_some] at hs
                cases hs
                have mem : zelle ∈ frame.tlb.zellen := List.mem_of_find?_eq_some hfind
                apply inv.nicht_unreserviert z.seitengranule mem ⟨phys, phys + 1⟩
                change ¬ (phys + 1 ≤ zelle.eintrag.frame * z.seitengranule ∨
                  (zelle.eintrag.frame + 1) * z.seitengranule ≤ phys)
                intro sep
                rcases sep with before | after
                · have low : zelle.eintrag.frame * z.seitengranule ≤ phys := by
                    rw [hphys]
                    exact Nat.le_add_right _ _
                  omega
                · have high : phys < (zelle.eintrag.frame + 1) * z.seitengranule := by
                    rw [hphys]
                    rw [Nat.add_mul]
                    simp only [Nat.one_mul]
                    have rlt : addr % z.seitengranule < z.seitengranule := Nat.mod_lt _ gpos
                    omega
                  omega
          · simp only [hright, ↓reduceIte] at h
            cases h
  · simp only [hv, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h
    cases h

end Gabbro.Core.Ast.LowLevel
