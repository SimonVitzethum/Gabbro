module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level joint satisfiability proofs

Prove `ErfuellbarAussage` separately at each of the four indices using the
canonical ideal initialisation. For the two region operations, use a
granted, aligned RAM extent disjoint from the platform device windows.

- `.addressType`
- `.regionAddress`
- `.view`
- `.environment`
-/

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine

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
  decide

private def lowStart (h : Umgebung) (regions : List Strecke) : AussenStart :=
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

private theorem lowZulStart {k : Katalog} {h : Umgebung} {regions : List Strecke}
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
    {tree : Tree form} {op : Instruction k} {env : Umgebung} {start : AussenStart}
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

theorem addressType_erfuellbar : ErfuellbarAussage .addressType := by
  let k : Katalog := Plattform.x86_64.katalog
  let scope : RegionScope := []
  let space : AddressSpace := .physical
  let tree : Tree .addressType := .addressType space
  let op : Instruction k := .denoteAddress space k.plattform.ziel.physicalBits (by
    simp only [space, AddressSpace.width])
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Umgebung := Umgebung.referenz k 1 sicht
  let start := lowStart env []
  let text : RawText := tree.print
  let transfer : Transfer k := ⟨.addressType space k.plattform.ziel.physicalBits, none⟩
  apply erfuellbar_von (k := k) (scope := scope) (tree := tree) (op := op) (env := env)
    (start := start) (text := text) (transfer := transfer)
  · simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  · rfl
  · apply lowZulStart (k := k) (h := env) (regions := [])
    · exact Umgebung.referenz_hardware k 1 sicht
        (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
    · simpa [k, Plattform.katalog] using imageGueltigX86
    · exact List.Pairwise.nil
    · intro r hr; cases hr
  · apply tree_parse_print tree
    dsimp [tree, space]
    rfl
  · have hSome : (space.width k.plattform).isSome := by
      change (some k.plattform.ziel.physicalBits : Option Nat).isSome
      rfl
    unfold elaborate
    simp only [tree]
    rw [dif_pos hSome]
    rfl
  · simp only [op, transfer, Instruction.evaluate]

theorem regionAddress_erfuellbar : ErfuellbarAussage .regionAddress := by
  let k : Katalog := Plattform.x86_64.katalog
  let name : Identifier := lowName
  let scope : RegionScope := [name]
  let extent : Strecke := ⟨0x1000, 0x2000⟩
  let tree : Tree .regionAddress := .regionAddress name
  let op : Instruction k := .projectAddress 0
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Umgebung := Umgebung.referenz k 1 sicht
  let start := lowStart env [extent]
  let text : RawText := tree.print
  let transfer : Transfer k := ⟨.address ⟨k.plattform.ziel.physicalBits, extent.von, rfl, by
    change 0x1000 < 2 ^ (52 : Nat)
    omega⟩, none⟩
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
    · exact Umgebung.referenz_hardware k 1 sicht
        (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
    · simpa [k, Plattform.katalog] using imageGueltigX86
    · exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · simpa [k, Plattform.katalog] using x86RegionsOk extent hbounds hsep
  · apply tree_parse_print tree
    dsimp [tree]
    rfl
  · have hslot : scope.slot name = some 0 := by
      simpa [scope, name] using lowName_slot
    simp only [elaborate, hslot, op, tree, Option.map_some]
  · let s := (I.start (unit op) start).2
    have hhr : heldRegion s entryContext 0 = some ((⟨0, 0⟩ : Griff), extent) := by
      rfl
    have hlt : extent.von < 2 ^ k.plattform.ziel.physicalBits := by
      change 0x1000 < 2 ^ (52 : Nat)
      omega
    change op.evaluate s entryContext = some transfer
    simp only [op, Instruction.evaluate, hhr, hlt, transfer, k, Option.bind, Option.bind_some, ↓reduceIte]
    rfl

theorem view_erfuellbar : ErfuellbarAussage .view := by
  let k : Katalog := Plattform.x86_64.katalog
  let name : Identifier := lowName
  let scope : RegionScope := [name]
  let extent : Strecke := ⟨0x1000, 0x2000⟩
  let written : WrittenType := .integer false 8 none
  let tree : Tree .view := .view name written
  let shape : Layout := ⟨written, 1, 1, ByteOrder.ofTarget k.plattform.ziel⟩
  let op : Instruction k := .borrowView 0 shape
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Umgebung := Umgebung.referenz k 1 sicht
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
    · exact Umgebung.referenz_hardware k 1 sicht
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
    have hcond : extent.von % shape.alignment = 0 ∧ extent.von + shape.bytes ≤ extent.bis := by
      constructor
      · change 0x1000 % 1 = 0
        rfl
      · change 0x1000 + 1 ≤ 0x2000
        omega
    change op.evaluate s entryContext = some transfer
    simp only [op, Instruction.evaluate, hhr, hcond, transfer, Option.bind, Option.bind_some, ↓reduceIte]
    rfl

theorem environment_erfuellbar : ErfuellbarAussage .environment := by
  let k : Katalog := Plattform.x86_64.katalog
  let name : Identifier := lowName
  let abi : DienstAbi := .biosInterrupt
  let row : FirmwareZeile := .biosServices
  let scope : RegionScope := []
  let tree : Tree .environment := .environment name abi row
  let allowed : row.zugelassen k abi := by
    decide
  let op : Instruction k := .selectEnvironment name abi row allowed
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Umgebung := Umgebung.referenz k 1 sicht
  let start := lowStart env []
  let text : RawText := tree.print
  let transfer : Transfer k := ⟨.environment name row abi, none⟩
  apply erfuellbar_von (k := k) (scope := scope) (tree := tree) (op := op) (env := env)
    (start := start) (text := text) (transfer := transfer)
  · simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  · rfl
  · apply lowZulStart (k := k) (h := env) (regions := [])
    · exact Umgebung.referenz_hardware k 1 sicht
        (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
    · simpa [k, Plattform.katalog] using imageGueltigX86
    · exact List.Pairwise.nil
    · intro r hr; cases hr
  · apply tree_parse_print tree
    dsimp [tree, abi, row]
    rfl
  · unfold elaborate
    simp only [tree, scope]
    exact dif_pos allowed
  · simp only [op, transfer, Instruction.evaluate]

end Gabbro.Core.Ast.LowLevel
