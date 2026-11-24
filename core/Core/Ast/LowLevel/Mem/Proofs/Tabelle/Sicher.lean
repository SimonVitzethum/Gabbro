module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.ErhaltungLauf
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Rechte

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # A translation served from tables or cache keeps its frame reserved

A successful translation over the frame's full MMU view (`MemFrame.mmuSicht`: installed tables plus
cached translations) returns an address in a reserved frame and a covered right. A cache hit behaves
like the cache-only view (`uebersetze_sicher`, `gecachte_rechte_gedeckt`): the frame is reserved
through the covering table entry or pending token, and the right is a table right unless a staged
narrowing is pending. A table hit serves the installed entry itself: its frame is reserved and its
right is a table right. A stale cache hit after `unmap` (table miss) is justified by the pending
`unmap` token, which owns frames and belongs to the space. -/

private theorem sicht_mem {frame : MemFrame} {core space page : Nat} {entry : Seiteneintrag}
    (hit : frame.tlb.sicht core space page = some entry) :
    ∃ zelle ∈ frame.tlb.zellen, zelle.kern = core ∧ zelle.raum = space ∧
      zelle.seite = page ∧ zelle.eintrag = entry := by
  unfold TranslationCache.sicht at hit
  generalize hfind : frame.tlb.zellen.find? (fun zelle =>
      zelle.kern == core && zelle.raum == space && zelle.seite == page) = found at hit
  cases found with
  | none =>
    simp only [Option.map_none] at hit
    cases hit
  | some zelle =>
    simp only [Option.map_some, Option.some.injEq] at hit
    subst hit
    have mem := List.mem_of_find?_eq_some hfind
    have pred := List.find?_some hfind
    simp only [Bool.and_eq_true] at pred
    obtain ⟨⟨hkern, hraum⟩, hseite⟩ := pred
    exact ⟨zelle, mem, beq_iff_eq.mp hkern, beq_iff_eq.mp hraum, beq_iff_eq.mp hseite, rfl⟩

/-- A successful translation over the full view keeps its frame reserved and its right covered:
    the right is an installed table right, a pending narrowing covers the page, or a pending
    `unmap` token owns the page. -/
theorem uebersetze_sicher_voll {frame : MemFrame}
    (coverTlb : frame.TlbGedeckt) (coverRechte : frame.TlbRechteGedeckt)
    (coverTab : frame.TabellenGedeckt)
    (z : ZielDaten) (core space addr : Nat) (right : Speicherdienst)
    {phys gen : Nat}
    (h : uebersetze z { tables := frame.tabellenSicht, tlb := frame.tlb.sicht }
      core space addr right = .ok (phys, gen)) :
    frame.unreserved z.seitengranule ⟨phys, phys + 1⟩ = false ∧
      ((∃ entry, frame.tabellenSicht space (addr / z.seitengranule) = some entry ∧
        right ∈ entry.rights ∧
        entry.frame * z.seitengranule + addr % z.seitengranule = phys) ∨
        frame.VerengtBei space (addr / z.seitengranule) ∨
        (∃ space0 token, frame.spaces[space]? = some space0 ∧ token ∈ space0.ausstehend ∧
          token.contains (addr / z.seitengranule) ∧ token.nurRechte = false ∧
          token.raum = space)) := by
  have gpos : 0 < z.seitengranule := by
    rw [ZielDaten.seitengranule]
    exact Nat.two_pow_pos z.pageShift
  have hmod : addr % z.seitengranule < z.seitengranule := Nat.mod_lt _ gpos
  unfold Katalog.uebersetze at h
  by_cases hv : z.virtuell addr
  · simp only [hv, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h
    generalize hs : frame.tlb.sicht core space (addr / z.seitengranule) = found at h
    cases found with
    | some centry =>
      obtain ⟨zelle, mem, hkern, hraum, hseite, hentry⟩ := sicht_mem hs
      by_cases hbig : centry.frame * z.seitengranule + addr % z.seitengranule ≥
          2 ^ z.physicalBits
      · simp only [Option.orElse_some, hbig, ↓reduceIte] at h
        cases h
      · simp only [Option.orElse_some, hbig, ↓reduceIte] at h
        by_cases hright : right ∈ centry.rights
        · simp only [hright, ↓reduceIte] at h
          have hphys : phys = centry.frame * z.seitengranule + addr % z.seitengranule := by
            exact (congrArg Prod.fst (Except.ok.inj h)).symm
          have hres : frame.unreserved z.seitengranule ⟨phys, phys + 1⟩ = false := by
            apply coverTlb.nicht_unreserviert z.seitengranule mem ⟨phys, phys + 1⟩
            change ¬ (phys + 1 ≤ zelle.eintrag.frame * z.seitengranule ∨
              (zelle.eintrag.frame + 1) * z.seitengranule ≤ phys)
            intro sep
            rw [hentry] at sep
            rcases sep with before | after
            · have low : centry.frame * z.seitengranule ≤ phys := by
                rw [hphys]
                exact Nat.le_add_right _ _
              omega
            · have high : phys < (centry.frame + 1) * z.seitengranule := by
                rw [hphys]
                rw [Nat.add_mul]
                simp only [Nat.one_mul]
                omega
              omega
          refine ⟨hres, ?rights⟩
          obtain ⟨space0, found0, covered0⟩ := coverTlb zelle mem
          have hfound0 : frame.spaces[space]? = some space0 := by
            rw [← hraum]
            exact found0
          rcases coverRechte zelle mem space0 found0 with okRights | pending
          · rcases covered0 with ⟨entry0, he0, hframe0⟩ | ⟨token, tmem, hdeck⟩
            · left
              have htab : frame.tabellenSicht space (addr / z.seitengranule) =
                  some entry0 := by
                rw [MemFrame.tabellenSicht_abbildung hfound0]
                rw [← hseite]
                exact he0
              refine ⟨entry0, htab, ?hright, ?hphys⟩
              · have hright' : right ∈ zelle.eintrag.rights := by
                  rw [hentry]
                  exact hright
                exact okRights entry0 he0 hframe0 right hright'
              · rw [hphys]
                have hframeEq : entry0.frame = centry.frame := by
                  rw [hframe0]
                  rw [hentry]
                rw [hframeEq]
            · right
              right
              obtain ⟨hspaces, _⟩ := coverTab
              have htab := hspaces space space0 hfound0
              obtain ⟨_, hflags, _⟩ := htab
              have hflag := hflags token tmem
              have hcont : token.contains (addr / z.seitengranule) := by
                rw [← hseite]
                exact hdeck.1
              exact ⟨space0, token, hfound0, tmem, hcont, hflag.1, hflag.2⟩
          · right
            left
            have hpend : frame.VerengtBei zelle.raum zelle.seite := pending
            rw [hraum, hseite] at hpend
            exact hpend
        · simp only [hright, ↓reduceIte] at h
          cases h
    | none =>
      simp only [Option.orElse_none] at h
      generalize ht : frame.tabellenSicht space (addr / z.seitengranule) = tfound at h
      cases tfound with
      | none =>
        cases h
      | some tentry =>
        obtain ⟨space0, found0, habb⟩ := MemFrame.tabellenSicht_hit ht
        by_cases hbig : tentry.frame * z.seitengranule + addr % z.seitengranule ≥
            2 ^ z.physicalBits
        · simp only [hbig, ↓reduceIte] at h
          cases h
        · simp only [hbig, ↓reduceIte] at h
          by_cases hright : right ∈ tentry.rights
          · simp only [hright, ↓reduceIte] at h
            have hphys : phys =
                tentry.frame * z.seitengranule + addr % z.seitengranule := by
              exact (congrArg Prod.fst (Except.ok.inj h)).symm
            have hres : frame.unreserved z.seitengranule ⟨phys, phys + 1⟩ = false :=
              Adressraum.eintrag_reserviert found0 habb hphys hmod
            refine ⟨hres, ?rightsTab⟩
            left
            refine ⟨tentry, ht, hright, ?hphysEq⟩
            exact hphys.symm
          · simp only [hright, ↓reduceIte] at h
            cases h
  · simp only [hv, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h
    cases h

end Gabbro.Core.Ast.LowLevel
