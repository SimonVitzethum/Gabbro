module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Kern
import Core.Ast.LowLevel.Mem.Proofs.NewSpace

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
open Gabbro.Core.Aussen
open Gabbro.Core.Annahme

private theorem memPrintIntegerVal (n : Nat) : (printInteger n).value = .natural n := by rfl
private theorem memIdentifierPrintVal (i : Identifier) : (Identifier.print i).value = .word i.val := by rfl
private theorem memPrintDotVal : printDot.value = dot := by rfl
private theorem memPrintOpenVal : printOpen.value = openParen := by rfl
private theorem memPrintCloseVal : printClose.value = closeParen := by rfl

private theorem memPrintsSplitAt (region : Identifier) (point : Nat) :
    (MemTree.splitAt region point).production
      ((MemTree.splitAt region point).printPieces.map PrintedToken.value) := by
  simp only [MemTree.production, MemTree.printPieces, List.map_cons, List.map_nil,
    memIdentifierPrintVal, memPrintIntegerVal, memPrintDotVal, memPrintOpenVal,
    memPrintCloseVal, word, Identifier.print, keyword, PrintedToken.unquoted,
    String.reduceToList]

private theorem memDerivesSymbols {form : MemForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact DerivesSymbols.nil
  | cons t ts ih => exact DerivesSymbols.terminal ih

private theorem memParseOfPrint {form} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) :
    MemParse tree.print tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨True.intro, pieces, lexical, ?_⟩
  refine Derives.production ⟨semanticTokens pieces, rfl, ?_⟩
    (memDerivesSymbols (semanticTokens pieces))
  change tree.production (canonicalTokens pieces)
  rw [align]
  exact prints

private theorem memImplTransfer {target : ZielDaten} {op : MemInstruction} {c : Kontext}
    {s : MemState} {w : PUnit} {plans : List Plan} {u : MemState}
    (h : MemInstruction.step target op c s w plans u) :
    ∃ frame, op.evaluate target s c = some frame ∧ plans = [plan] ∧ u = frame.advance c s := h

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

private theorem memHeadSingle {target : ZielDaten} {op : MemInstruction} {s : MemState}
    {c : Kontext} :
    memHead target [op] s c = some op ↔
      s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
        (op.evaluate target s c).isSome = true := by
  unfold memHead
  constructor
  · intro h
    by_cases hc : c = entryContext
    · subst c
      cases hs : s.status entryContext with
      | laeuft =>
          simp only [if_pos rfl, hs, ↓reduceIte] at h
          cases hp : (s.lokal entryContext).pc with
          | zero =>
              simp only [hp, List.getElem?_cons_zero, Option.bind_some] at h
              change (if (op.evaluate target s entryContext).isSome = true then some op else none) = some op at h
              cases he : (op.evaluate target s entryContext).isSome with
              | true => exact ⟨rfl, rfl, rfl, rfl⟩
              | false =>
                  simp only [he, Bool.false_eq_true, ↓reduceIte] at h
                  cases h
          | succ n =>
              simp only [hp, List.getElem?_cons_succ, List.getElem?_nil, Option.bind_none] at h
              cases h
      | ruht | beendet _ =>
          simp only [if_pos rfl, hs, ↓reduceIte] at h
          cases h
    · simp only [if_neg hc] at h
      cases h
  · rintro ⟨hstatus, hc, hpc, heval⟩
    subst c
    simp only [if_pos rfl, hstatus]
    rw [hpc]
    change (if (op.evaluate target s entryContext).isSome = true then some op else none) = some op
    rw [if_pos heval]

private theorem memRegelLokal (k : Katalog) (op : MemInstruction) :
    Annahme.RegelLokal (memUnit k op) op := by
  change ∀ (c : Kontext) (s u : MemState) (w : PUnit) (P : Plan),
    MemInstruction.step k.plattform.ziel op c s w [P] u →
      Annahme.Befugt (memUnit k op) s c P
  intro c s u w P hideal
  obtain ⟨frame, heval, hP, hu⟩ := memImplTransfer hideal
  cases (List.cons.inj hP).1
  subst u
  rw [Annahme.Befugt]
  have hfuss : plan.fuss = [] := rfl
  have hlesen : plan.lesen = [] := rfl
  rw [hfuss, hlesen]
  constructor
  · intro x hx
    cases hx
  · intro l hl
    cases hl

private theorem memAussenLokalUnit (k : Katalog) (op : MemInstruction) :
    Annahme.AussenLokal (memUnit k op) := by
  change Annahme.AussenLokal (memUnit k op)
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
      obtain ⟨i, head, frame, heval, planEq, rfl⟩ := regel
      cases (List.cons.inj planEq).1
      obtain ⟨rfl, rfl⟩ := memGenauInternal execute
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

private theorem memAkzeptiert (k : Katalog) (valid : KatalogWohlgeformt k)
    (op : MemInstruction) : Annahme.Akzeptiert (memUnit k op) := by
  refine ⟨⟨valid, fun i => memRegelLokal k i, memAussenLokalUnit k op, memFlussLokal k op, ?_⟩, ?_, ?_⟩
  · exact schrankenLokal_leer rfl rfl rfl  · intro ρ _
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨fun _ _ _ _ _ need => False.elim need, fun _ _ _ h => ?_,
      fun _ _ _ _ _ _ hne => (hne rfl).elim⟩
    obtain ⟨_, ⟨c, mem⟩, blockiert⟩ := h
    obtain ⟨_, nein, _⟩ := blockiert c mem
    exact nein

private theorem memImageGueltigX86 : image.gueltig Plattform.x86_64.ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro a mem
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨0, rfl⟩

private theorem memX86RegionsOk (extent : Strecke)
    (hbounds : extent.von < extent.bis ∧ extent.bis ≤ 2 ^ Plattform.x86_64.ziel.physicalBits)
    (hsep : extent.getrennt Plattform.x86_64.virtio.window) :
    ∀ r ∈ [extent], r.von < r.bis ∧ r.bis ≤ 2 ^ Plattform.x86_64.ziel.physicalBits ∧
      ∀ e d, Plattform.x86_64.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  intro e d hdev hmmio
  cases e with
  | uart =>
      change some Plattform.x86_64.uart = some d at hdev
      cases hdev
      change GeratBus.ioPorts = GeratBus.mmio at hmmio
      cases hmmio
  | virtio =>
      change some Plattform.x86_64.virtio = some d at hdev
      cases hdev
      exact hsep
  | bios | uefi | psci | sbi | hosted | cProcess =>
      change none = some d at hdev
      cases hdev

private def memWitnessName : Identifier :=
  keywordName 'r' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)

private def memWitnessExtent : Strecke := ⟨0, 4096⟩
private def memWitnessPoint : Nat := 2048

private def memWitnessScope : MemScope :=
  ⟨[memWitnessName], [], []⟩

private def memWitnessTree : MemTree .splitAt := .splitAt memWitnessName memWitnessPoint

private def memWitnessOp : MemInstruction := .splitRegion 0 memWitnessPoint

private def memWitnessSicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer

private def memWitnessEnv (k : Katalog) : Katalog.Umgebung :=
  Katalog.Umgebung.referenz k 1 memWitnessSicht

private def memWitnessStart (k : Katalog) : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none), [memWitnessExtent], (fun _ => none),
    (memWitnessEnv k).politik.sicht 0 []⟩

private theorem memWitnessElab : elaborateMem memWitnessScope memWitnessTree = some memWitnessOp := by
  change (memWitnessScope.slotRegion memWitnessName).map
      (fun slot => MemInstruction.splitRegion slot memWitnessPoint) = some memWitnessOp
  have hslot : memWitnessScope.slotRegion memWitnessName = some 0 := by
    change [memWitnessName.val].idxOf? memWitnessName.val = some 0
    simp only [List.idxOf?_cons, beq_self_eq_true, if_true]
  rw [hslot]
  rfl

theorem memErfuellbarSplitAt : MemErfuellbarAussage .splitAt := by
  let k : Katalog := Plattform.x86_64.katalog
  let E := memUnit k memWitnessOp
  let s : MemState := (I.start E (memWitnessStart k)).2
  let region : MemRegion := ⟨memWitnessExtent, [⟨0, 0⟩]⟩
  let next : MemFrame := (s.lokal entryContext).partition 0 region memWitnessPoint
  have hbounds : memWitnessExtent.von < memWitnessExtent.bis ∧
      memWitnessExtent.bis ≤ 2 ^ k.plattform.ziel.physicalBits := by
    change 0 < 4096 ∧ 4096 ≤ 2 ^ (52 : Nat)
    constructor <;> omega
  have hsep : memWitnessExtent.getrennt Plattform.x86_64.virtio.window := by
    unfold Strecke.getrennt
    change 4096 ≤ 0x10000000 ∨ 0x10000200 ≤ 0
    exact Or.inl (by omega)
  have hhr : heldMemRegion k.plattform.ziel s entryContext 0 = some region := by
    rfl
  have hinside : memWitnessExtent.von < memWitnessPoint ∧ memWitnessPoint < memWitnessExtent.bis := by
    change 0 < 2048 ∧ 2048 < 4096
    omega
  have heval : memWitnessOp.evaluate k.plattform.ziel s entryContext = some next := by
    change (MemInstruction.splitRegion 0 memWitnessPoint).evaluate k.plattform.ziel s entryContext = some next
    simp only [MemInstruction.evaluate]
    rw [hhr]
    change (if memWitnessExtent.von < memWitnessPoint ∧ memWitnessPoint < memWitnessExtent.bis then
      some ((s.lokal entryContext).partition 0 region memWitnessPoint) else none) = some next
    rw [if_pos hinside]
  have hhead : memHead k.plattform.ziel [memWitnessOp] s entryContext = some memWitnessOp :=
    memHeadSingle.mpr ⟨by
      change s.status entryContext = .laeuft
      rfl, rfl, by
      change (s.lokal entryContext).pc = 0
      rfl, by
      rw [heval]
      rfl⟩

  refine ⟨k, memWitnessScope, memWitnessTree, memWitnessOp, memWitnessEnv k,
    memWitnessStart k, memWitnessTree.print, [], s, next, ?_⟩
  dsimp only
  refine ⟨True.intro, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Umgebung.referenz_hardware k 1 memWitnessSicht
      (by simpa [k] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
  · change Katalog.ZulStart k (memWitnessEnv k) image (memWitnessStart k)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simpa [k, Plattform.katalog] using memImageGueltigX86
    · change 0 < 1
      omega
    · intro i hi
      refine ⟨0, ?_⟩
      change (if i = 0 then some 0 else none) = some 0
      change i < 1 at hi
      have : i = 0 := by omega
      subst i
      rfl
    · intro i c hc
      change (if i = 0 then some 0 else none) = some c at hc
      split at hc
      · rename_i hi
        subst i
        cases hc
        constructor
        · change 0 < 1
          omega
        · change 0 < 1
          omega
      · cases hc
    · change List.Pairwise Strecke.getrennt [memWitnessExtent]
      exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · change ∀ r ∈ [memWitnessExtent],
        r.von < r.bis ∧ r.bis ≤ 2 ^ Plattform.x86_64.ziel.physicalBits ∧
        ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window
      simpa [k, Plattform.katalog] using memX86RegionsOk memWitnessExtent hbounds hsep
    · intro a byte hb
      change none = some byte at hb
      cases hb
  · change Annahme.Akzeptiert (memUnit k memWitnessOp)
    exact memAkzeptiert k (by simpa [k] using Plattform.katalog_wohlgeformt .x86_64) memWitnessOp
  · change [memWitnessName.val].Nodup
    exact List.nodup_singleton _
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  · refine ⟨memWitnessTree, ?_, ?_⟩
    · exact memParseOfPrint memWitnessTree (memPrintsSplitAt memWitnessName memWitnessPoint)
    · exact ⟨memWitnessOp, memWitnessElab, rfl⟩
  · exact memParseOfPrint memWitnessTree (memPrintsSplitAt memWitnessName memWitnessPoint)
  · exact memWitnessElab
  · change E.system.IErreichbar (I.start E (memWitnessStart k)).2 s
    exact System.IErreichbar.start
  · exact hhead
  · exact heval
  · change ∃ i, memHead k.plattform.ziel [memWitnessOp] s entryContext = some i ∧
      MemInstruction.step k.plattform.ziel i entryContext s () [plan] (next.advance entryContext s)
    exact ⟨memWitnessOp, hhead, ⟨next, heval, rfl, rfl⟩⟩
  · change ∃ i, memHead k.plattform.ziel [memWitnessOp] s entryContext = some i ∧
      MemInstruction.step k.plattform.ziel i entryContext s () [plan] (next.advance entryContext s)
    exact ⟨memWitnessOp, hhead, ⟨next, heval, rfl, rfl⟩⟩

theorem splitAt_aussage : SplitAtAussage :=
  ⟨memObligationsKern_alle .splitAt, splitAt_meaning, memErfuellbarSplitAt⟩

end Gabbro.Core.Ast.LowLevel
