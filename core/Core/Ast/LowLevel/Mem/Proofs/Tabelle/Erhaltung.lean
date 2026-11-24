module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Deckung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # The table invariant survives every instruction

Each space keeps its entries disjoint from its pending `unmap` tokens, its tokens own frames and
belong to it, its entries carry rights and reached generations; pending narrowings own no frame.
`map` adds entries outside every pending token, `protect` narrows rights in place and records the
narrowing, `unmap` clears the range and reserves it with a token, `flush` ends a token. -/

private theorem frei_narrow (space : Adressraum) (base pages : Nat) (rights : List Speicherdienst)
    (wf : space.FreiAusstehend) :
    (narrowRights space base pages rights).FreiAusstehend := by
  intro entry hentry token tmem
  unfold narrowRights at hentry
  obtain ⟨old, hold, heq⟩ := List.mem_map.mp hentry
  have hpage : entry.1 = old.1 := by
    cases old with
    | mk pg ent =>
      simp only at heq
      cases h : decide (pageRange base pages pg) with
      | true =>
        simp only [h] at heq
        simp only [heq]
      | false =>
        simp only [h] at heq
        simp only [heq]
  rw [hpage]
  exact wf old hold token tmem

private theorem rechte_narrow (space : Adressraum) (base pages : Nat)
    (rights : List Speicherdienst) (hne : rights ≠ [])
    (ok : ∀ entry ∈ space.entries, entry.2.rights ≠ [] ∧ entry.2.generation ≤ space.generation)
    (entry : Nat × Seiteneintrag)
    (hmem : entry ∈ (narrowRights space base pages rights).entries) :
    entry.2.rights ≠ [] ∧
      entry.2.generation ≤ (narrowRights space base pages rights).generation := by
  unfold narrowRights at hmem
  simp only at hmem
  obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmem
  have hgen : (narrowRights space base pages rights).generation = space.generation := rfl
  rw [hgen]
  have holdOk := ok old hold
  cases old with
  | mk pg ent =>
    simp only at heq
    cases h : decide (pageRange base pages pg) with
    | true =>
      simp only [h] at heq
      cases heq
      exact ⟨hne, holdOk.2⟩
    | false =>
      simp only [h] at heq
      cases heq
      exact holdOk

theorem tabellenGedeckt_newSpace (target : ZielDaten) (tables : Nat) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.newSpace tables).evaluate target s c = some next)
    (inv : (s.lokal c).TabellenGedeckt) : next.TabellenGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hr : heldMemRegion target s c tables with
  | none =>
    simp only [hr, Option.bind_eq_bind, Option.bind_none] at h
    cases h
  | some region =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      obtain ⟨hspaces, hnarrow⟩ := inv
      refine ⟨?spaces, ?narrow⟩
      · intro sp space found
        by_cases hlt : sp < (s.lokal c).spaces.length
        · have found0 : (s.lokal c).spaces[sp]? = some space := by
            have happ := List.getElem?_append_left hlt (l₂ :=
              [{ tabellen := region.extent, entries := [],
                generation := 0, ausstehend := [] } : Adressraum])
            rw [happ] at found
            exact found
          exact hspaces sp space found0
        · have hlt' := (List.getElem?_eq_some_iff.mp found).1
          have hlen : ((s.lokal c).spaces ++
              [{ tabellen := region.extent, entries := [],
                generation := 0, ausstehend := [] } : Adressraum]).length =
              (s.lokal c).spaces.length + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil,
              Nat.add_zero]
          have hsp : sp = (s.lokal c).spaces.length := by
            omega
          have hge : (s.lokal c).spaces.length ≤ sp := by
            omega
          have happ := List.getElem?_append_right (l₁ := (s.lokal c).spaces)
            (l₂ := [{ tabellen := region.extent, entries := [],
              generation := 0, ausstehend := [] } : Adressraum]) hge
          rw [happ] at found
          have hsub : sp - (s.lokal c).spaces.length = 0 := by
            omega
          rw [hsub] at found
          simp only [List.getElem?_cons_zero] at found
          have hspace : space =
              { tabellen := region.extent, entries := [],
                generation := 0, ausstehend := [] } :=
            Option.some.inj found
          subst hspace
          refine ⟨?frei, ?flags, ?rights⟩
          · intro entry hentry
            cases hentry
          · intro token tmem
            cases tmem
          · intro entry hentry
            cases hentry
      · intro token mem
        exact hnarrow token mem
    · cases h

end Gabbro.Core.Ast.LowLevel
