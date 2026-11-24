module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Deckung
public import Core.Ast.LowLevel.Mem.Proofs.Protect.ProtectMeaning

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # Table updates keep every cached translation covered

`map` adds entries outside every cached page, `protect` keeps every frame, and `unmap` moves the
cover of a cached page from the cleared table entry to the pending token. -/

theorem abbildung_append_fern (space : Adressraum) (new : List (Nat × Seiteneintrag)) (pg : Nat)
    (fern : ∀ e ∈ new, e.1 ≠ pg) :
    ({ space with entries := space.entries ++ new } : Adressraum).abbildung pg =
      space.abbildung pg := by
  have hnone : new.find? (fun e => e.1 == pg) = none :=
    List.find?_eq_none.mpr fun e he hbeq => fern e he (beq_iff_eq.mp hbeq)
  show ((space.entries ++ new).find? (fun e => e.1 == pg)).map Prod.snd =
    (space.entries.find? (fun e => e.1 == pg)).map Prod.snd
  rw [List.find?_append, hnone, Option.or_none]

private theorem find_filter_fern (l : List (Nat × Seiteneintrag)) (q : Nat × Seiteneintrag → Bool)
    (pg : Nat) (keep : ∀ e : Nat × Seiteneintrag, e.1 = pg → q e = true) :
    (l.filter q).find? (fun e => e.1 == pg) = l.find? (fun e => e.1 == pg) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hk : x.1 = pg
    · have hq := keep x hk
      have hp : (x.1 == pg) = true := beq_iff_eq.mpr hk
      simp only [List.filter_cons, hq, if_true, List.find?_cons, hp]
    · have nk : (x.1 == pg) = false := by
        cases h : (x.1 == pg) with
        | false => rfl
        | true => exact (hk (beq_iff_eq.mp h)).elim
      cases hq : q x with
      | true => simp only [List.filter_cons, hq, if_true, List.find?_cons, nk, ih]
      | false =>
        simp only [List.filter_cons, hq, Bool.false_eq_true, if_false, List.find?_cons, nk, ih]

theorem abbildung_filter_fern (space space' : Adressraum) (q : Nat × Seiteneintrag → Bool)
    (pg : Nat) (entries : space'.entries = space.entries.filter q)
    (keep : ∀ e : Nat × Seiteneintrag, e.1 = pg → q e = true) :
    space'.abbildung pg = space.abbildung pg := by
  unfold Adressraum.abbildung
  rw [entries, find_filter_fern space.entries q pg keep]

theorem abbildung_narrow_frame (space : Adressraum) (base pages : Nat)
    (rights : List Speicherdienst) (pg : Nat) (entry : Seiteneintrag)
    (found : space.abbildung pg = some entry) :
    ∃ entry', (narrowRights space base pages rights).abbildung pg = some entry' ∧
      entry'.frame = entry.frame := by
  have hcomp : ((fun e : Nat × Seiteneintrag => e.1 == pg) ∘
      (fun pair : Nat × Seiteneintrag =>
        if pageRange base pages pair.1 then (pair.1, { pair.2 with rights }) else (pair.1, pair.2))) =
      (fun e : Nat × Seiteneintrag => e.1 == pg) := by
    funext e
    cases e with
    | mk page entry =>
        by_cases h : pageRange base pages page <;>
          simp only [Function.comp_apply, h, ite_true, ite_false]
  simp only [narrowRights, Adressraum.abbildung, List.find?_map, hcomp]
  unfold Adressraum.abbildung at found
  cases hfind : space.entries.find? (fun e => e.1 == pg) with
  | none => simp only [hfind, Option.map_none] at found <;> cases found
  | some pair =>
    obtain ⟨page, entry0⟩ := pair
    simp only [hfind, Option.map_some, Option.some.injEq] at found
    by_cases h : pageRange base pages page
    · exact ⟨{ entry0 with rights }, by simp only [Option.map_some, h, if_true], by
        subst found; rfl⟩
    · exact ⟨entry0, by simp only [Option.map_some, h, if_false], by subst found; rfl⟩

theorem tlbGedeckt_protectSpace (target : ZielDaten) (sp virt pages : Nat)
    (rights : List Speicherdienst) (s : MemState) (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.protectSpace sp virt pages rights).evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      intro zelle mem
      have mem' := (List.mem_filter.mp mem).1
      obtain ⟨space0, found0, covered0⟩ := inv zelle mem'
      by_cases same : zelle.raum = sp
      · have unique : space0 = space := by
          rw [same] at found0
          exact Option.some.inj (found0.symm.trans hs)
        rw [unique] at covered0
        have lt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
        refine ⟨?w, ?hw, ?hd⟩
        case hw =>
          rw [same]
          exact List.getElem?_set_self lt
        case hd =>
          refine Adressraum.deckt_mit (space := space) (fun entry found => ?_)
            (fun token tmem own => ⟨token, tmem, own⟩) covered0
          exact abbildung_narrow_frame space (virt / target.seitengranule) pages rights _ entry found
      · exact ⟨space0, MemFrame.TlbGedeckt.set_fern same found0, covered0⟩
    · cases h

theorem tlbGedeckt_mapSpace (target : ZielDaten) (sp virt slot : Nat)
    (rights : List Speicherdienst) (s : MemState) (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.mapSpace sp virt slot rights).evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    cases hr : heldMemRegion target s c slot with
    | none => simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> cases h
    | some region =>
      simp only [hs, hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i cond
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        have hnone : ∀ i < (region.extent.bis - region.extent.von) / target.seitengranule,
            space.abbildung (virt / target.seitengranule + i) = none := by
          intro i hi
          have hiMem : i ∈ List.range ((region.extent.bis - region.extent.von) / target.seitengranule) :=
            List.mem_range.mpr hi
          have hiT := (List.all_eq_true.mp cond.2.2.2.1) i hiMem
          cases hfind : space.abbildung (virt / target.seitengranule + i) with
          | none => rfl
          | some entry =>
              simp only [hfind, Option.isNone] at hiT
              cases hiT
        have htok : ∀ token ∈ space.ausstehend,
            ∀ i < (region.extent.bis - region.extent.von) / target.seitengranule,
            ¬ token.contains (virt / target.seitengranule + i) := by
          intro token htmem i hi
          have hiT := (List.all_eq_true.mp
            ((List.all_eq_true.mp cond.2.2.2.2) token htmem)) i (List.mem_range.mpr hi)
          simpa only [decide_eq_true_eq] using hiT
        intro zelle mem
        obtain ⟨space0, found0, covered0⟩ := inv zelle mem
        by_cases same : zelle.raum = sp
        · have unique : space0 = space := by
            rw [same] at found0
            exact Option.some.inj (found0.symm.trans hs)
          rw [unique] at covered0
          have lt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
          refine ⟨?w, ?hw, ?hd⟩
          case hw =>
            rw [same]
            exact List.getElem?_set_self lt
          case hd =>
            refine Adressraum.deckt_mit (space := space) (fun entry found => ⟨entry, ?_, rfl⟩)
              (fun token tmem own => ⟨token, tmem, own⟩) covered0
            rw [abbildung_append_fern _ _ zelle.seite ?_]
            · exact found
            · intro e he
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
              intro heq
              have htrue : zelle.imBereich sp (virt / target.seitengranule)
                  ((region.extent.bis - region.extent.von) / target.seitengranule) = true := by
                simp only [TlbZelle.imBereich, decide_eq_true_eq, Bool.and_eq_true]
                refine ⟨same, ?_⟩
                unfold pageRange
                have hlt : i < (region.extent.bis - region.extent.von) / target.seitengranule :=
                  List.mem_range.mp hi
                omega
              rw [MemFrame.TlbGedeckt.keine_Zelle inv hs hnone htok zelle mem] at htrue
              cases htrue
        · exact ⟨space0, MemFrame.TlbGedeckt.set_fern same found0, covered0⟩
      · cases h

theorem tlbGedeckt_unmapSpace (target : ZielDaten) (sp virt pages : Nat) (s : MemState)
    (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.unmapSpace sp virt pages).evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    cases hf : space.abbildung (virt / target.seitengranule) with
    | none => simp only [hs, hf, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> cases h
    | some first =>
      simp only [hs, hf, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i cond
        have hall := List.all_eq_true.mp cond.2
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        intro zelle mem
        obtain ⟨space0, found0, covered0⟩ := inv zelle mem
        by_cases same : zelle.raum = sp
        · have unique : space0 = space := by
            rw [same] at found0
            exact Option.some.inj (found0.symm.trans hs)
          rw [unique] at covered0
          have lt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
          refine ⟨?w, ?hw, ?hd⟩
          case hw =>
            rw [same]
            exact List.getElem?_set_self lt
          case hd =>
            rcases covered0 with ⟨entry, he, hframe⟩ | ⟨token, tmem, own⟩
            · by_cases inside : pageRange (virt / target.seitengranule) pages zelle.seite
              · refine Or.inr ⟨⟨sp, virt / target.seitengranule, pages, space.generation + 1,
                  first.frame⟩, List.mem_cons_self .., inside, ?_⟩
                have idx : ((space.abbildung (virt / target.seitengranule +
                    (zelle.seite - virt / target.seitengranule))).map Seiteneintrag.frame ==
                      some (first.frame + (zelle.seite - virt / target.seitengranule))) = true :=
                  hall (zelle.seite - virt / target.seitengranule)
                    (List.mem_range.mpr (by unfold pageRange at inside; omega))
                have back : virt / target.seitengranule +
                    (zelle.seite - virt / target.seitengranule) = zelle.seite := by
                  unfold pageRange at inside; omega
                rw [back, he] at idx
                have eq := Option.some.inj (beq_iff_eq.mp idx)
                show zelle.eintrag.frame = first.frame + (zelle.seite - virt / target.seitengranule)
                rw [← hframe]
                exact eq
              · refine Or.inl ⟨entry, ?_, hframe⟩
                rw [abbildung_filter_fern space _ _ zelle.seite ?ent ?keep]
                · exact he
                case ent => rfl
                case keep =>
                  intro e he'
                  obtain ⟨page, entry'⟩ := e
                  simp only at he'
                  subst he'
                  simp only [decide_eq_false inside, Bool.not_false]
            · exact Or.inr ⟨token, List.mem_cons_of_mem _ tmem, own⟩
        · exact ⟨space0, MemFrame.TlbGedeckt.set_fern same found0, covered0⟩
      · cases h

end Gabbro.Core.Ast.LowLevel
