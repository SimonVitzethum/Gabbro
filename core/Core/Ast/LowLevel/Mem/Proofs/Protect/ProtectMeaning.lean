module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

open Text Katalog Maschine

def narrowRights (space : Adressraum) (base pages : Nat) (rights : List Speicherdienst) : Adressraum :=
  { space with entries := space.entries.map fun (page, entry) =>
      if pageRange base pages page then (page, { entry with rights }) else (page, entry) }

theorem abbildung_narrow (space : Adressraum) (base pages : Nat) (rights : List Speicherdienst) :
    ∀ pg, pageRange base pages pg →
      (narrowRights space base pages rights).abbildung pg =
        (space.abbildung pg).map (fun entry => { entry with rights }) := by
  intro pg covered
  simp only [narrowRights, Adressraum.abbildung, List.find?_map]
  have hcomp : ((fun e : Nat × Seiteneintrag => e.1 == pg) ∘
      (fun pair : Nat × Seiteneintrag =>
        if pageRange base pages pair.1 then (pair.1, { pair.2 with rights }) else (pair.1, pair.2))) =
      (fun e : Nat × Seiteneintrag => e.1 == pg) := by
    funext e
    cases e with
    | mk page entry =>
        by_cases h : pageRange base pages page <;> simp only [Function.comp_apply, h, ite_true, ite_false]
  rw [hcomp]
  cases hfind : space.entries.find? (fun e => e.1 == pg) with
  | none => rfl
  | some pair =>
      cases pair with
      | mk page entry =>
          have hpg : (page == pg) = true := by
            exact List.find?_some (p := fun e : Nat × Seiteneintrag => e.1 == pg) hfind
          have hpage : page = pg := beq_iff_eq.mp hpg
          have hcover : pageRange base pages page := hpage.symm ▸ covered
          simp only [hcover, if_true, Option.map_some, Prod.snd]

theorem protect_meaning : ProtectMeaningAussage := by
  intro target s c sp virt pages rights space found
  let base := virt / target.seitengranule
  have hslt : sp < (s.lokal c).spaces.length := by
    by_contra hnot
    have hnone : (s.lokal c).spaces[sp]? = none :=
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hnot)
    rw [hnone] at found
    cases found
  constructor
  · intro hpos
    rcases hpos with ⟨hrights, hvalid, hall⟩
    have hcond : rights ≠ [] ∧ validVirtualRange target virt pages ∧
        ((List.range pages).all fun i =>
          (space.abbildung (base + i)).any fun entry => rights.all (· ∈ entry.rights)) := by
      refine ⟨hrights, hvalid, ?_⟩
      apply List.all_eq_true.mpr
      intro i hi
      have hi' : i < pages := List.mem_range.mp hi
      obtain ⟨entry, hmap, hrightsok⟩ := hall i hi'
      rw [hmap]
      simp only [Option.any_some]
      apply List.all_eq_true.mpr
      intro r hr
      rw [decide_eq_true_eq]
      exact hrightsok r hr
    let narrowed := narrowRights space base pages rights
    let next : MemFrame := { s.lokal c with
      result := some .«protected»
      spaces := (s.lokal c).spaces.set sp narrowed
      tlb := (s.lokal c).tlb.invalidate sp base pages }
    refine ⟨next, narrowed, ?_, ?_, ?_, ?_, ?_⟩
    · change (MemInstruction.protectSpace sp virt pages rights).evaluate target s c = some next
      simp only [base] at hcond ⊢
      simp only [MemInstruction.evaluate, found, Option.bind_eq_bind, Option.bind_some,
        if_pos hcond, Option.pure_def]
      rfl
    · change next.spaces[sp]? = some narrowed
      simp only [next, List.getElem?_set, beq_self_eq_true, hslt, if_true]
    · rfl
    · intro pg entry hcover hmap
      change narrowed.abbildung pg = some { entry with rights }
      rw [abbildung_narrow space base pages rights pg hcover, hmap]
      rfl
    · exact TranslationCache.frei_invalidate _ _ _ _
  · intro hneg
    rcases hneg with ⟨i, hi, entry, hmap, right, hrin, hrout⟩
    have hnot : ¬ (rights ≠ [] ∧ validVirtualRange target virt pages ∧
        ((List.range pages).all fun i =>
          (space.abbildung (base + i)).any fun entry => rights.all (· ∈ entry.rights))) := by
      rintro ⟨_, _, hall⟩
      have hi_mem : i ∈ List.range pages := List.mem_range.mpr hi
      have hi_true := (List.all_eq_true.mp hall) i hi_mem
      have hany : (space.abbildung (base + i)).any
          (fun entry => rights.all (· ∈ entry.rights)) = true := hi_true
      rw [hmap] at hany
      simp only [Option.any_some] at hany
      have hall_rights := (List.all_eq_true.mp hany) right hrin
      exact hrout (decide_eq_true_eq.mp hall_rights)
    simp only [base] at hnot ⊢
    simp only [MemInstruction.evaluate, found, Option.bind_eq_bind, Option.bind_some, if_neg hnot]

end Gabbro.Core.Ast.LowLevel
