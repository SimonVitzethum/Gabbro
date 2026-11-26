module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Kern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
private theorem newSpacePrints (tree : MemTree .newSpace) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree with
  | newSpace tables =>
      simpa [MemTree.production, MemTree.printPieces, keyword, word, Identifier.print,
        PrintedToken.unquoted, printPunctuation, printDot, printOpen, printClose,
        dot, openParen, closeParen, String.reduceToList]
private def newSpaceSyntax : Gabbro.Core.Text.Syntax (MemTree .newSpace) where
  reads := fun tokens tree => tree.production tokens
  unique := by
    intro tokens a b ha hb
    exact memEindeutigKern .newSpace a b tokens ha hb
  printPieces := MemTree.printPieces
  reads_print := newSpacePrints
private theorem memHead_some_iff (target : ZielDaten) (op : MemInstruction)
    (s : MemState) (c : Kontext) :
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
          simp only [hs] at h
          dsimp at h
          cases hpc : [op][(s.lokal entryContext).pc]? with
          | none =>
              simp only [hpc, Option.bind_none] at h
              cases h
          | some instr =>
              simp only [hpc, Option.bind_some] at h
              cases hpci : (s.lokal entryContext).pc with
              | zero =>
                  simp only [hpci, List.getElem?_cons_zero] at hpc
                  cases hpc
                  split at h
                  · rename_i hev
                    exact ⟨rfl, rfl, rfl, hev⟩
                  · cases h
              | succ n =>
                  simp only [hpci, List.getElem?_cons_succ, List.getElem?_nil] at hpc
                  cases hpc
      | ruht =>
          simp only [hs] at h
          cases h
      | beendet e =>
          simp only [hs] at h
          cases h
    · simp only [hc, ↓reduceIte] at h
      cases h
  · rintro ⟨hs, rfl, hpci, hev⟩
    simp only [hs, hpci, List.getElem?_cons_zero, ↓reduceIte]
    dsimp
    rw [if_pos hev]
private theorem memRegelLokal (k : Katalog) (op : MemInstruction) :
    Annahme.RegelLokal (memUnit k op) op := by
  intro c s u w P hideal
  change ∃ frame, op.evaluate k.plattform.ziel s c = some frame ∧ [P] = [plan] ∧
    u = frame.advance c s at hideal
  rcases hideal with ⟨frame, heval, hP, hu⟩
  have hP' : P = plan := by simpa using hP
  subst P
  have hfuss : plan.fuss = [] := rfl
  have hlesen : plan.lesen = [] := rfl
  rw [Annahme.Befugt, hfuss, hlesen]
  constructor
  · intro x hx
    cases hx
  · intro l hl
    cases hl
private theorem memImplTransfer {target : ZielDaten} {op : MemInstruction} {c : Kontext}
    {s : MemState} {w : PUnit} {plans : List Plan} {u : MemState}
    (h : op.step target c s w plans u) :
    ∃ frame, op.evaluate target s c = some frame ∧ plans = [plan] ∧ u = frame.advance c s := h
private theorem memVollzug (frame : MemFrame) (t : Nat) (c : Kontext) (s : MemState) :
    FuehrtSchrittAus memSetup t c s (frame.advance c s) plan ⟨[], []⟩ (frame.advance c s) := by
  refine ⟨?_, ?_, [], frame.advance c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
      simp only [plan, List.nil_append, schreibEreignisse, List.map_nil, List.filter_nil, List.append_nil] at memory
      have unchanged : ∀ {recorded graph},
          Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
            recorded = [] ∧ graph = s.graph := by
        intro _ _ run
        cases run
        exact ⟨rfl, rfl⟩
      have hmem := unchanged memory
      rw [hmem.1]
      rw [hmem.2, ← rahmen.graph] at nextEq
      exact ⟨rfl, nextEq⟩
private theorem memAbgleich (k : Katalog) (op : MemInstruction) :
    I.RegelAbgleich (memUnit k op) op := by
  intro hw t c w s u s' i stepPlan trace related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨frame, evaluate, planEq, hu⟩ := memImplTransfer (target := k.plattform.ziel) (op := op) (w := w) impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩
private theorem memKomponierbar (k : Katalog) (op : MemInstruction) :
    I.RegelKomponierbar (memUnit k op).einrichtung (memUnit k op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨frame, evaluate, planEq, hu⟩ := memImplTransfer (target := k.plattform.ziel) (op := op) (w := w) ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq, memVollzug frame t c s⟩
private theorem memRegelSicher (k : Katalog) (op : MemInstruction) :
    Gabbro.Core.Sicherheit.RegelSicher (memSafetyUnit k op) op := by
  intro H ρ t c w vor zwischen nach stepPlan trace head impl execute
  obtain ⟨frame, _, planEq, _⟩ := memImplTransfer (target := k.plattform.ziel) (op := op) (w := w) impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := memGenauInternal execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (frame.advance c vor) (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
    Or.inr ⟨ohneAbsturz, (List.append_nil _).symm⟩
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => ordered, ?_, ?_⟩
  · intro i actor access recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    exact nomatch alive.symm.trans lost
  · intro _
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared _
    change [][i]? = some d at declared
    cases declared
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
private theorem memAussenLokal (k : Katalog) (op : MemInstruction) :
    Gabbro.Core.Annahme.AussenLokal (memUnit k op) := by
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, rfl⟩ := memGenauInternal execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

/-- Every memory instruction uses the public frame and region authority and emits no output. -/
theorem memProgramFlussLokal (k : Katalog) (code : List MemInstruction) :
    Beobachtung.FlussLokal (memProgram k code) := by
  constructor
  · intro s₁ s₂ same
    have regions : s₁.regions = s₂.regions := congrArg (fun p => p.2.2.1) same
    refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_, rfl, fun _ => rfl⟩
    · intro c _ _
      simp only [I.start, memProgram, memBoot, Zustand.start, regions]
    · simp only [I.start, memProgram, memBoot, Zustand.start, regions]
  · intro f
    constructor
    · intro c v w p u _
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun privateControl => ?_⟩
      exact (Bool.false_ne_true privateControl.symm).elim
    · intro _ c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ same step₁ step₂
      have run₁ : f.step k.plattform.ziel c v₁ w₁ [p₁] u₁ := step₁.2
      have run₂ : f.step k.plattform.ziel c v₂ w₂ [p₂] u₂ := step₂.2
      obtain ⟨frame₁, eval₁, plan₁, rfl⟩ := run₁
      obtain ⟨frame₂, eval₂, plan₂, rfl⟩ := run₂
      obtain ⟨locals, ends, initial, rights, loans, answers⟩ := same
      have localEq : v₁.lokal = v₂.lokal :=
        funext fun d => locals d ⟨0, Nat.zero_lt_succ _⟩ rfl
      rw [← f.evaluate_congr _ _ localEq rights loans, eval₁] at eval₂
      cases eval₂
      rw [(List.cons.inj plan₁).1, (List.cons.inj plan₂).1]
      refine ⟨⟨?_, ends, initial, rights, loans, answers⟩, rfl, rfl⟩
      intro d _ _
      simp only [MemFrame.advance, localEq]

theorem memFlussLokal (k : Katalog) (op : MemInstruction) :
    Beobachtung.FlussLokal (memUnit k op) := memProgramFlussLokal k [op]

private theorem newSpaceMeaning : NewSpaceMeaningAussage := by
  intro target s c slot region hhr
  constructor
  · intro hseiten
    let space : Adressraum := ⟨region.extent, [], 0, []⟩
    let next : MemFrame := { s.lokal c with
      result := some (.space (s.lokal c).spaces.length)
      spaces := (s.lokal c).spaces ++ [space] }
    refine ⟨next, space, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [MemInstruction.evaluate, hhr]
      dsimp
      rw [if_pos hseiten]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ⟨hseiten, List.nodup_nil, by intro entry hm; cases hm⟩
  · intro hnot
    simp only [MemInstruction.evaluate, hhr]
    dsimp
    rw [if_neg hnot]
private theorem imageGueltigX86 : image.gueltig (Plattform.x86_64).ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro a mem
    have h : a = 0 := List.mem_singleton.mp mem
    subst a
    exact ⟨0, rfl⟩
private theorem memZulStart {k : Katalog} {h : Katalog.Umgebung} {regions : List Strecke}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel)
    (pairwise : regions.Pairwise Strecke.getrennt)
    (ok : ∀ r ∈ regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window) :
    Katalog.ZulStart k h image
      ⟨0, (fun i => if i = 0 then some 0 else none), regions, (fun _ => none),
        h.politik.sicht 0 []⟩ := by
  refine ⟨img, hw.kerne, ?_, ?_, pairwise, ok, ?_, rfl⟩
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
      · simpa using hw.kerne
    · cases hc
  · intro a byte hb
    change (none : Option UInt8) = some byte at hb
    cases hb
private theorem memKlauseln (k : Katalog) (op : MemInstruction) :
    KlauselnWahr (memUnit k op) := by
  intro ρ runs
  dsimp [kanonischeKlauseln, memUnit, memProgram, Quelltabellen.leer, Quellklauseln.leer]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases hp
  · intro t p hp
    cases hp
  · intro t done p hp
    cases hp
private theorem memWaechter (k : Katalog) (op : MemInstruction) :
    WaechterHalten (memUnit k op) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ runs t o args bedarf
    dsimp [kanonischeVerwendung, memUnit, memProgram, Quelltabellen.leer] at bedarf
    cases bedarf
  · intro ρ runs t
    rintro ⟨C, nonempty, blocked⟩
    obtain ⟨c, hc⟩ := nonempty
    obtain ⟨b, hblock, _, _, _⟩ := blocked c hc
    exact hblock
  · intro ρ runs t l h _ hne; exact (hne rfl).elim
private theorem memAkzeptiertX86 (op : MemInstruction) :
    Annahme.Akzeptiert (memUnit Plattform.x86_64.katalog op) := by
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_, memAussenLokal _ op, memFlussLokal _ op, ?_, ?_, ?_⟩,
    memKlauseln _ op, memWaechter _ op⟩
  · intro i
    exact memRegelLokal _ i
  · exact schrankenLokal_leer rfl rfl rfl
  · exact Gabbro.Core.Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · refine ⟨Gabbro.Core.Maschine.eineTabelle_akzeptiert, fun s c i _ t c' sv u sv' w qq spur himpl haus => ?_⟩
    obtain ⟨_, _, planEq, _⟩ := himpl
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, _⟩ := memGenauInternal haus
    exact Gabbro.Core.Annahme.spurRespektiert_leer _ _ _
private def newSpaceName : Identifier :=
  ⟨['t'], ⟨'t', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩
private theorem newSpaceName_slot :
    MemScope.slotRegion ⟨[newSpaceName], [], []⟩ newSpaceName = some 0 := by
  change [newSpaceName.val].idxOf? newSpaceName.val = some 0
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]
private theorem newSpace_erfuellbar : MemErfuellbarAussage .newSpace := by
  let target := Plattform.x86_64.ziel
  let k : Katalog := Plattform.x86_64.katalog
  let extent : Strecke := ⟨0, 4096⟩
  let scope : MemScope := ⟨[newSpaceName], [], []⟩
  let tree : MemTree .newSpace := .newSpace newSpaceName
  let op : MemInstruction := .newSpace 0
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start : AussenStart := ⟨0, (fun i => if i = 0 then some 0 else none), [extent],
    (fun _ => none), env.politik.sicht 0 []⟩
  let pre : List MemInstruction := []
  let E : MemUnit := memProgram k (pre ++ [op])
  let text : RawText := tree.print
  let s : MemState := (I.start E start).2
  let space : Adressraum := ⟨extent, [], 0, []⟩
  let next : MemFrame := { s.lokal entryContext with
    result := some (.space (s.lokal entryContext).spaces.length)
    spaces := (s.lokal entryContext).spaces ++ [space] }
  have hardware : Hardware k env := by
    apply Katalog.Umgebung.referenz_hardware k 1 sicht
    · simpa [k] using Plattform.katalog_wohlgeformt .x86_64
    · omega
  have extent_ok : extent.seiten target := by
    change 0 < 4096 ∧ 4096 ≤ 2 ^ (52 : Nat) ∧ 0 % (2 ^ (12 : Nat)) = 0 ∧
      4096 % (2 ^ (12 : Nat)) = 0
    omega
  have regions_ok : ∀ r ∈ [extent], r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
    intro r hr
    have rext : r = extent := List.mem_singleton.mp hr
    subst r
    refine ⟨by change 0 < 4096; omega, by change 4096 ≤ 2 ^ (52 : Nat); omega, ?_⟩
    intro endpoint device selected mmio
    cases endpoint <;> cases selected
    · cases mmio
    · exact Or.inl (by change 4096 ≤ 0x10000000; omega)
  have admitted : E.ZulStart env start := by
    apply memZulStart (k := k) (h := env) (regions := [extent]) hardware imageGueltigX86
    · exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · exact regions_ok
  have accepted : Annahme.Akzeptiert E := memAkzeptiertX86 op
  have hElab : elaborateMem scope tree = some op := by
    simp only [tree, elaborateMem, op, scope, newSpaceName_slot, Option.map_some]
  have hParse : MemParse text tree := by
    change Gabbro.Core.Text.Parse newSpaceSyntax.grammar (newSpaceSyntax.print tree) tree
    exact newSpaceSyntax.parse_print tree
  have hhr : heldMemRegion target s entryContext 0 = some ⟨extent, [⟨0, 0⟩]⟩ := by
    rfl
  have heval : op.evaluate target s entryContext = some next := by
    simp only [op, MemInstruction.evaluate, hhr]
    dsimp
    rw [if_pos extent_ok]
  have hhead : E.system.kopf s entryContext = some op := by
    change memHead target [op] s entryContext = some op
    exact (memHead_some_iff target op s entryContext).2 ⟨rfl, rfl, rfl, by rw [heval]; rfl⟩
  have hreach : E.system.IErreichbar (I.start E start).2 s := by
    change E.system.IErreichbar s s
    exact System.IErreichbar.start
  have hstep : E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have himpl : E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s) := by
    refine ⟨op, hhead, ?_⟩
    exact ⟨next, heval, rfl, rfl⟩
  have hnodup : (scope.regionen.map Subtype.val).Nodup := by
    dsimp [scope]
    exact List.nodup_singleton _
  refine ⟨k, scope, tree, op, env, start, text, pre, s, next, ?_⟩
  exact ⟨True.intro, hardware, admitted, accepted, hnodup,
    List.nodup_nil, List.nodup_nil,
    ⟨tree, hParse, ⟨op, hElab, rfl⟩⟩, hParse, hElab, hreach, hhead, heval, hstep, himpl⟩
theorem newSpace_aussage : NewSpaceAussage :=
  ⟨memObligationsKern_alle .newSpace, newSpaceMeaning, newSpace_erfuellbar⟩

end Gabbro.Core.Ast.LowLevel
