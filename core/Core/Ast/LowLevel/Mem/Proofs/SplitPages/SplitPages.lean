module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Kern
import Core.Ast.LowLevel.Mem.Proofs.NewSpace

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Annahme Waechter
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

theorem splitPagesParseOfPrint {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) : MemParse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply (memParseKern form tree.print tree).2
  refine ⟨pieces, ?_, ?_⟩
  · simpa only [MemTree.print, Lexed] using lex
  · rw [aligned]
    exact prints

theorem splitPagesPrints (region : Identifier) (pages : Nat) :
    (MemTree.splitPages region pages).production
      ((MemTree.splitPages region pages).printPieces.map PrintedToken.value) := by
  rfl

theorem splitPagesHeadSingleton (target : ZielDaten) (op : MemInstruction)
    (s : MemState) (c : Kontext) :
    memHead target [op] s c = some op ↔
      s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
        (op.evaluate target s c).isSome = true := by
  constructor
  · intro h
    by_cases hc : c = entryContext
    · subst c
      cases hs : s.status entryContext with
      | laeuft =>
        cases hpc : (s.lokal entryContext).pc with
        | zero =>
          cases he : (op.evaluate target s entryContext).isSome with
          | true => exact ⟨rfl, rfl, rfl, rfl⟩
          | false =>
            simp only [memHead, if_pos rfl, hs, hpc, List.getElem?_cons_zero, he,
              Bool.false_eq_true, if_false, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none] at h
            cases h
        | succ n =>
          simp only [memHead, if_pos rfl, hs, hpc, List.getElem?_cons_succ,
            List.getElem?_nil, Option.bind_eq_bind, Option.bind_none] at h
          cases h
      | ruht =>
        simp only [memHead, if_pos rfl, hs] at h
        cases h
      | beendet _ =>
        simp only [memHead, if_pos rfl, hs] at h
        cases h
    · simp only [memHead, hc, if_false] at h
      cases h
  · rintro ⟨hs, rfl, hpc, he⟩
    rw [memHead]
    simp only [hs, hpc, List.getElem?_cons_zero, Option.bind_eq_bind, Option.bind_some,
      he, reduceIte]

private theorem memImplTransfer {target : ZielDaten} {op : MemInstruction} {c : Kontext}
    {s : MemState} {w : PUnit} {plans : List Plan} {u : MemState}
    (h : (MemInstruction.rule target op).impl c s w plans u) :
    ∃ frame, op.evaluate target s c = some frame ∧ plans = [plan] ∧ u = frame.advance c s := by
  change ∃ frame, op.evaluate target s c = some frame ∧ plans = [plan] ∧ u = frame.advance c s at h
  cases he : op.evaluate target s c with
  | none =>
    obtain ⟨frame, hf, _, _⟩ := h
    rw [he] at hf
    cases hf
  | some frame =>
    obtain ⟨frame', hf, hp, hu⟩ := h
    rw [he] at hf
    cases hf
    exact ⟨frame, rfl, hp, hu⟩

private theorem memVollzug (frame : MemFrame) (t : Nat) (c : Kontext) (s : MemState) :
    FuehrtSchrittAus memSetup t c s (frame.advance c s) plan ⟨[], []⟩ (frame.advance c s) := by
  refine ⟨?_, ?_, [], frame.advance c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [plan] at hl
    cases hl
  · change FuehrtAus memSetup t c s (frame.advance c s) .intern [] [] (frame.advance c s)
    exact FuehrtAus.intern
  · change Speicherfolge s.initial (.kontext c) s.graph [] [] (frame.advance c s).graph
    exact Speicherfolge.nil _

private theorem memGenauInternal {t : Nat} {c : Kontext} {s u : MemState}
    {trace : SchrittSpur Nat UInt8} {next : MemState}
    (execute : FuehrtSchrittAus memSetup t c s u plan trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨rahmen, _, _, _, action, memory, nextEq⟩ := execute
  cases trace with
  | mk events outside =>
    cases action
    simp only [plan, List.nil_append, schreibEreignisse, List.map_nil] at memory
    have unchanged : ∀ {recorded graph},
        Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
          recorded = [] ∧ graph = s.graph := by
      intro _ _ run
      cases run
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, graph⟩ := unchanged memory
    rw [graph] at nextEq
    rw [← rahmen.graph] at nextEq
    exact ⟨rfl, nextEq⟩

private theorem memAbgleich (k : Katalog) (op : MemInstruction) :
    I.RegelAbgleich (memUnit k op) op := by
  intro hw t c w s u s' i stepPlan spur related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨frame, evaluate, planEq, hu⟩ := memImplTransfer (target := k.plattform.ziel) (w := w) impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

private theorem memKomponierbar (k : Katalog) (op : MemInstruction) :
    I.RegelKomponierbar (memUnit k op).einrichtung (memUnit k op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨frame, evaluate, planEq, hu⟩ := memImplTransfer (target := k.plattform.ziel) (w := w) ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq, memVollzug frame t c s⟩

private theorem memProgramAussenLokal (k : Katalog) (code : List MemInstruction) :
    Annahme.AussenLokal (memProgram k code) := by
  refine ⟨Aussen.zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, rfl⟩ := memGenauInternal execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

theorem splitPagesProgramAkzeptiert (k : Katalog) (code : List MemInstruction)
    (hwf : KatalogWohlgeformt k) : Annahme.Akzeptiert (memProgram k code) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hwf, ?_, ⟨memProgramAussenLokal k code, memProgramFlussLokal k code⟩⟩
    intro i c s u w plan hideal
    simp only [memProgram, MemInstruction.rule, MemInstruction.step] at hideal
    obtain ⟨frame, _, hp, hu⟩ := hideal
    cases (List.cons.inj hp).1
    subst u
    rw [Annahme.Befugt]
    constructor
    · intro x hx; cases hx
    · intro l hl; cases hl
  · intro rho lauf
    refine ⟨?_, ?_, ?_⟩
    · intro p hp; cases hp
    · intro t p hp; cases hp
    · intro t fertig p hp; cases hp
  · constructor
    · intro rho lauf t op args need
      change (memProgram k code).quelltabellen.guard (rho.zeit.zustand t.val) op args at need
      cases need
    · intro rho lauf t closed
      obtain ⟨C, ⟨⟨c, hc⟩, rest⟩⟩ := closed
      obtain ⟨b, blocked, intern, locks, joins⟩ := rest c hc
      change False at blocked
      cases blocked

private theorem partitionPost (frame : MemFrame) (slot : Nat) (region : MemRegion) (point : Nat)
    (inside : region.extent.von < point ∧ point < region.extent.bis) :
    PartitionPost frame (frame.partition slot region point) region slot point := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl (Nat.le_refl _), ?_⟩
  intro addr
  change region.extent.von ≤ addr ∧ addr < region.extent.bis ↔
    (region.extent.von ≤ addr ∧ addr < point) ∨ (point ≤ addr ∧ addr < region.extent.bis)
  omega

theorem splitPagesMeaning : SplitPagesMeaningAussage := by
  intro target s c slot pages
  constructor
  · intro missing
    simp only [MemInstruction.evaluate, missing, Option.bind_eq_bind, Option.bind_none]
  · intro region held
    let granule := target.seitengranule
    let point := region.extent.von + pages * granule
    constructor
    · intro inside
      have hg : 0 < granule := by
        dsimp [granule, ZielDaten.seitengranule]
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      have hmul : 0 < pages * granule := Nat.mul_pos inside.2.1 hg
      have hvlt : region.extent.von < point := by dsimp [point]; omega
      have hcut : point < region.extent.bis := inside.2.2
      have hEval : (MemInstruction.splitPages slot pages).evaluate target s c =
          some ((s.lokal c).partition slot region point) := by
        simp only [MemInstruction.evaluate, held]
        change (if region.extent.von % granule = 0 ∧ 0 < pages ∧
            region.extent.von + pages * granule < region.extent.bis then
            some ((s.lokal c).partition slot region point) else none) =
          some ((s.lokal c).partition slot region point)
        rw [if_pos ⟨inside.1, inside.2.1, by simpa only [point] using hcut⟩]
      refine ⟨_, hEval, partitionPost (s.lokal c) slot region point ⟨hvlt, hcut⟩, ?_, ?_⟩
      · change (region.extent.von + pages * granule) % granule = 0
        rw [Nat.add_mod, inside.1]
        rw [Nat.mod_eq_zero_of_dvd (dvd_mul_left granule pages)]
        rfl
      · change (region.extent.von + pages * granule) - region.extent.von = pages * granule
        omega
    · intro outside
      simp only [MemInstruction.evaluate, held, Option.bind_eq_bind, Option.bind_some, if_neg outside]

end Gabbro.Core.Ast.LowLevel
