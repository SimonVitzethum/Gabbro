module

public import Core.Ast.LowLevel.Obligations
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine
open Gabbro.Core.Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
open Gabbro.Core.Aussen

namespace Instruction

theorem implTransfer {k : Katalog} {op : Instruction k} {c : Kontext} {s : State k}
    {w : PUnit} {plans : List Plan} {u : State k} (h : op.impl c s w plans u) :
    ∃ transfer : Transfer k, op.evaluate s c = some transfer ∧ plans = [plan] ∧
      u = transfer.apply c s := by
  cases he : op.evaluate s c with
  | none =>
    unfold Instruction.impl at h
    rw [he] at h
    cases h
  | some transfer =>
    unfold Instruction.impl at h
    rw [he] at h
    exact ⟨transfer, rfl, h.1, h.2⟩

theorem vollzug {k : Katalog} (op : Instruction k) (transfer : Transfer k)
    (t : Nat) (c : Kontext) (s : State k) :
    FuehrtSchrittAus (setup k) t c s (transfer.apply c s) plan ⟨[], []⟩ (transfer.apply c s) := by
  refine ⟨?_, ?_, [], transfer.apply c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [plan] at hl
    cases hl
  · change FuehrtAus (setup k) t c s (transfer.apply c s) .intern [] [] (transfer.apply c s)
    exact FuehrtAus.intern
  · change Speicherfolge s.initial (.kontext c) s.graph [] [] (transfer.apply c s).graph
    exact Speicherfolge.nil _

theorem genauInternal {k : Katalog} {t : Nat} {c : Kontext} {s u : State k}
    {trace : SchrittSpur Nat UInt8} {next : State k}
    (execute : FuehrtSchrittAus (setup k) t c s u plan trace next) :
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

theorem vollzugGenau {k : Katalog} (op : Instruction k) {t : Nat} {c : Kontext}
    {s u : State k} {w : PUnit} {p : Plan} {trace : SchrittSpur Nat UInt8} {next : State k}
    (rule : op.impl c s w [p] u) (execute : FuehrtSchrittAus (setup k) t c s u p trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨_, _, hp, _⟩ := implTransfer (op := op) (w := w) rule
  cases (List.cons.inj hp).1
  exact genauInternal execute

end Instruction

theorem Instruction.abgleich {k : Katalog} (op : Instruction k) : I.RegelAbgleich (unit op) op := by
  intro hw t c w s u s' i stepPlan trace related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨transfer, evaluate, planEq, hu⟩ := Instruction.implTransfer (op := op) (w := w) impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨transfer, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

theorem Instruction.komponierbar {k : Katalog} (op : Instruction k) :
    I.RegelKomponierbar (unit op).einrichtung (unit op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨transfer, evaluate, planEq, hu⟩ := ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, transfer.apply c s, planEq, Instruction.vollzug op transfer t c s⟩

theorem Instruction.regelSicher {k : Katalog} (op : Instruction k) :
    Gabbro.Core.Sicherheit.RegelSicher (safetyUnit op) op := by
  intro H ρ t c w vor zwischen nach stepPlan trace head impl execute
  obtain ⟨transfer, _, planEq, _⟩ := Instruction.implTransfer (op := op) (w := w) impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := Instruction.genauInternal execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (transfer.apply c vor) (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
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

theorem Instruction.regelAntwortSicher {k : Katalog} (op : Instruction k) :
    Sicherheit.RegelAntwortSicher (safetyUnit op) op ∧
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      (∀ ev : AntwortEreignis, Ereignis.antwort ev ∉ trace.aussen) ∧
      next.verbraucht = s.verbraucht := by
  constructor
  · intro t c w vor zwischen nach p trace _ impl execute befugt
    obtain ⟨transfer, _, _, rfl⟩ := Instruction.implTransfer (op := op) (w := w) impl
    obtain ⟨_, rfl⟩ := op.vollzugGenau (w := w) impl execute
    exact befugt
  · intro t c s w middle next p trace impl execute
    obtain ⟨rfl, rfl⟩ := op.vollzugGenau (w := w) impl execute
    exact ⟨fun _ => List.not_mem_nil, execute.1.verbraucht⟩

theorem Instruction.aussenLokal {k : Katalog} (op : Instruction k) :
    Gabbro.Core.Annahme.AussenLokal (unit op) := by
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, transfer, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, rfl⟩ := Instruction.genauInternal execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

theorem Instruction.kosten {k : Katalog} (op : Instruction k) :
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (unit op).stotterLaenge op = 0 := by
  intro t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := Instruction.implTransfer (op := op) (w := w) impl
  cases (List.cons.inj hp).1
  exact ⟨(Instruction.genauInternal execute).1, rfl⟩

lemma viewErhaltungAussage : ErhaltungAussage .view := by
  intro k scope tree op _
  exact ⟨Instruction.abgleich op, Instruction.komponierbar op⟩

lemma viewRegelSicherAussage : RegelSicherAussage .view := by
  intro k scope tree op _
  exact Instruction.regelSicher op

lemma viewRegelAntwortSicherAussage : RegelAntwortSicherAussage .view := by
  intro k scope tree op _
  exact Instruction.regelAntwortSicher op

lemma viewAussenLokalAussage : AussenLokalAussage .view := by
  intro k scope tree op _
  exact Instruction.aussenLokal op

lemma viewKostenAussage : KostenAussage .view := by
  intro k scope tree op _
  exact Instruction.kosten op

private theorem derivesSymbols {form : Form} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : Tree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact DerivesSymbols.nil
  | cons t ts ih => exact DerivesSymbols.terminal ih

private theorem derivesTerminals {form : Form} {tree : Tree form} (ts : List LocatedToken)
    (prod : tree.production (ts.map LocatedToken.value)) :
    Derives (tokenGrammar (fun tokens (t : Tree form) => t.production tokens)) tree ts := by
  refine Derives.production (symbols := ts.map Symbol.terminal) ?_ ?_
  · exact ⟨ts, rfl, prod⟩
  · exact derivesSymbols ts

private theorem lowParse_of {form : Form} {text : RawText} {tree : Tree form}
    {pieces : List Piece} (lex : Lexed text pieces)
    (prod : tree.production (canonicalTokens pieces)) : Parse text tree := by
  refine ⟨True.intro, pieces, lex, ?_⟩
  exact derivesTerminals (semanticTokens pieces) prod

private theorem tree_parse_print {form : Form} (tree : Tree form)
    (prod : tree.production (tree.printPieces.map PrintedToken.value)) : Parse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply lowParse_of (text := tree.print) (tree := tree) lex
  rw [aligned]
  exact prod

private def lowName : Identifier :=
  ⟨['r'], ⟨'r', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem lowName_slot : RegionScope.slot [lowName] lowName = some 0 := by
  change [lowName.val].idxOf? lowName.val = some 0
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

private def lowStart (h : Katalog.Umgebung) (regions : List Strecke) : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none), regions, (fun _ => none), h.politik.sicht 0 []⟩

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

private theorem lowZulStart {k : Katalog} {h : Katalog.Umgebung} {regions : List Strecke}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel)
    (pairwise : regions.Pairwise Strecke.getrennt)
    (ok : ∀ r ∈ regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window) :
    Katalog.ZulStart k h image (lowStart h regions) := by
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

private theorem x86RegionsOk (extent : Strecke)
    (hbounds : extent.von < extent.bis ∧ extent.bis ≤ 2 ^ (Plattform.x86_64).ziel.physicalBits)
    (hsep : extent.getrennt (Plattform.x86_64.virtio.window)) :
    ∀ r ∈ [extent], r.von < r.bis ∧ r.bis ≤ 2 ^ (Plattform.x86_64).ziel.physicalBits ∧
      ∀ e d, Plattform.x86_64.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
  intro r hr
  have : r = extent := List.mem_singleton.mp hr
  subst r
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

private theorem erfuellbar_von {form : Form} {k : Katalog} {scope : RegionScope}
    {tree : Tree form} {op : Instruction k} {env : Katalog.Umgebung} {start : AussenStart}
    {text : RawText} {transfer : Transfer k}
    (hWF : KatalogWohlgeformt k)
    (hNodup : (scope.map Subtype.val).Nodup)
    (hLen : scope.length = start.regions.length)
    (hZul : (unit op).ZulStart env start)
    (hParse : Parse text tree)
    (hElab : elaborate k scope tree = some op)
    (hEval : op.evaluate (I.start (unit op) start).2 entryContext = some transfer) :
    ErfuellbarAussage form := by
  let s := (I.start (unit op) start).2
  have hEvalS : op.evaluate s entryContext = some transfer := hEval
  refine ⟨k, scope, tree, op, env, start, text, transfer, hWF, hNodup, hLen, hZul, hParse,
    hElab, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨op, hElab, rfl⟩
  · have hs : s.status entryContext = .laeuft := by
      simp only [s, I.start, unit, bootData, entryContext, Zustand.start, ↓reduceIte, reduceCtorEq]
    have hp : (s.lokal entryContext).pc = 0 := by
      simp only [s, I.start, unit, bootData, entryContext, Zustand.start, ↓reduceIte, reduceCtorEq]
    change head op s entryContext = some op
    unfold head
    rw [hs]
    have hcond : entryContext = entryContext ∧ (s.lokal entryContext).pc = 0 ∧
        (op.evaluate s entryContext).isSome := ⟨rfl, hp, by rw [hEvalS]; rfl⟩
    simp only [hcond, ↓reduceIte, and_true, true_and]
  · exact hEvalS
  · change op.ideal entryContext s () [plan] (transfer.apply entryContext s)
    exact ⟨transfer, hEvalS, rfl, rfl⟩
  · change op.impl entryContext s () [plan] (transfer.apply entryContext s)
    simp only [Instruction.impl, hEvalS, and_self]

lemma viewErfuellbarAussage : ErfuellbarAussage .view := by
  let k : Katalog := Plattform.x86_64.katalog
  let name : Identifier := lowName
  let scope : RegionScope := [name]
  let extent : Strecke := ⟨0x1000, 0x2000⟩
  let written : WrittenType := .integer false 8 none
  let tree : Tree .view := .view name written
  let shape : Layout := ⟨written, 1, 1, ByteOrder.ofTarget k.plattform.ziel⟩
  let op : Instruction k := .borrowView 0 shape
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start := lowStart env [extent]
  let text : RawText := tree.print
  let transfer : Transfer k := ⟨.view 0 (⟨0, 0⟩ : Griff) ⟨extent.von, extent.von + shape.bytes⟩ shape,
    some (⟨0, 0⟩ : Griff)⟩
  have hbounds : extent.von < extent.bis ∧ extent.bis ≤ 2 ^ (Plattform.x86_64).ziel.physicalBits := by
    constructor
    · change 0x1000 < 0x2000
      omega
    · change 0x2000 ≤ 2 ^ (52 : Nat)
      omega
  have hsep : extent.getrennt (Plattform.x86_64.virtio.window) := by
    unfold Strecke.getrennt
    change 0x2000 ≤ 0x10000000 ∨ 0x10000200 ≤ 0x1000
    exact Or.inl (by omega)
  apply erfuellbar_von (k := k) (scope := scope) (tree := tree) (op := op) (env := env)
    (start := start) (text := text) (transfer := transfer)
  · simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64
  · change [name.val].Nodup
    apply List.nodup_cons.mpr
    constructor
    · intro h
      cases h
    · exact List.nodup_nil
  · rfl
  · apply lowZulStart (k := k) (h := env) (regions := [extent])
    · exact Katalog.Umgebung.referenz_hardware k 1 sicht
        (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
    · simpa [k, Plattform.katalog] using imageGueltigX86
    · exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · simpa [k, Plattform.katalog] using x86RegionsOk extent hbounds hsep
  · apply tree_parse_print tree
    refine ⟨written.printPieces.map PrintedToken.value, rfl, ?_⟩
    exact TypeReads.integer
      (by
        change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
        omega)
      (by intro more h; cases h)
  · have hslot : scope.slot name = some 0 := by
      simpa [scope, name] using lowName_slot
    have hlayout : layout k.plattform.ziel written = some shape := by
      rfl
    simp only [elaborate, hslot, hlayout, op, tree, Option.bind, Option.bind_some]
    rfl
  · let s := (I.start (unit op) start).2
    have hhr : heldRegion s entryContext 0 = some ((⟨0, 0⟩ : Griff), extent) := by
      rfl
    have hcond : shape.fits extent := by
      constructor
      · change 0x1000 % 1 = 0
        rfl
      · change 0x1000 + 1 ≤ 0x2000
        omega
    change op.evaluate s entryContext = some transfer
    simp only [op, Instruction.evaluate, hhr, hcond, transfer, Bind.bind, Option.bind,
      Option.bind_some, ↓reduceIte]
    rfl

private lemma layout_endian (target : ZielDaten) (t : WrittenType) (shape : Layout)
    (h : layout target t = some shape) : shape.endian = ByteOrder.ofTarget target := by
  cases t with
  | integer signed width range =>
      simp only [layout] at h
      split at h
      · injection h with hs
        subst shape
        rfl
      · cases h
  | _ =>
    simp only [layout] at h
    cases h

private lemma heldRegion_borrowed_none {k : Katalog} (s : State k) (c : Kontext) (slot : Nat)
    (h : (⟨slot, 0⟩ : Griff) ∈ (s.lokal c).borrowed) :
    heldRegion s c slot = none := by
  unfold heldRegion
  dsimp
  rw [List.contains_eq_mem]
  rw [decide_eq_true h]
  rw [Bool.not_true]
  rw [Bool.and_false]
  cases (s.lokal c).regions[slot]? with
  | none => rfl
  | some extent =>
      dsimp

lemma viewMeaningAussage : ViewMeaningAussage := by
  intro k scope region type op s c transfer hop heval
  simp only [elaborate, Option.bind, Option.bind_some] at hop
  cases hslot : scope.slot region with
  | none =>
      simp only [hslot, Option.bind, Option.bind_some] at hop
      cases hop
  | some slot =>
      cases hlayout : layout k.plattform.ziel type with
      | none =>
          simp only [hslot, hlayout, Option.bind, Option.bind_some] at hop
          cases hop
      | some shape =>
          simp only [hslot, hlayout, Option.bind, Option.bind_some] at hop
          injection hop with hop'
          subst op
          cases hhr : heldRegion s c slot with
          | none =>
              simp only [Instruction.evaluate] at heval
              rw [hhr] at heval
              dsimp at heval
              cases heval
          | some pair =>
              rcases pair with ⟨handleV, extent⟩
              by_cases hcond : shape.fits extent
              · simp only [Instruction.evaluate] at heval
                rw [hhr] at heval
                dsimp at heval
                rw [if_pos hcond] at heval
                injection heval with hval
                subst transfer
                have hendian : shape.endian = ByteOrder.ofTarget k.plattform.ziel :=
                  layout_endian k.plattform.ziel type shape hlayout
                have hhandle : handleV = ⟨slot, 0⟩ := by
                  have hhr' := hhr
                  unfold heldRegion at hhr'
                  dsimp at hhr'
                  cases hreg : (s.lokal c).regions[slot]? with
                  | none =>
                      rw [hreg] at hhr'
                      dsimp at hhr'
                      cases hhr'
                  | some extent0 =>
                      rw [hreg] at hhr'
                      dsimp at hhr'
                      split at hhr'
                      · cases hleihe : s.leihen slot with
                        | eigen =>
                            simp only [hleihe] at hhr'
                            have hpair : ((⟨slot, 0⟩ : Griff), extent0) = (handleV, extent) :=
                              Option.some.inj hhr'
                            exact (congrArg Prod.fst hpair).symm
                        | verliehen x =>
                            simp only [hleihe] at hhr'
                            cases hhr'
                      · cases hhr'
                have hb :
                    (⟨slot, 0⟩ : Griff) ∈
                      (((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                          some handleV⟩ : Transfer k).apply c s).lokal c).borrowed := by
                  simp only [Transfer.apply, Function.update_self, hhandle, Option.toList,
                    List.mem_append, List.mem_singleton, true_or]
                have hlast :
                    heldRegion
                      ((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                          some handleV⟩ : Transfer k).apply c s) c slot = none :=
                  heldRegion_borrowed_none ((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                    some handleV⟩ : Transfer k).apply c s) c slot hb
                exact ⟨slot, handleV, extent, shape, (by first | exact hslot | rfl), hhr,
                  (by first | exact hlayout | rfl), hendian, hcond.1, hcond.2, rfl, rfl, hlast⟩
              · simp only [Instruction.evaluate] at heval
                rw [hhr] at heval
                dsimp at heval
                rw [if_neg hcond] at heval
                cases heval

end Gabbro.Core.Ast.LowLevel
