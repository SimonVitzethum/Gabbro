module

public import Core.Ziel.Korrektheit.PrueferLokal
public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ast.Semantik.Runtime.Mehrkontext.Kopf
public import Core.Ast.Semantik.Runtime.ValueCoercion

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast Gabbro.Core.Ast.Semantik Gabbro.Core.Maschine
open Gabbro.Core.Aussenfrage Gabbro.Core.Katalog Gabbro.Core.Annahme

/-- Frame-local properties preserved by all instructions hold across private runs, including
    interrupt entries and crash recovery. -/
private theorem privatRahmenInvariant (p : Fragment) (platform : Plattform)
    (privat : ∀ b ∈ p.code, b.Privat) (holds : Semantik.Rahmen → Prop)
    (boot : ∀ r, r.temp = (fun _ => none) → r.funktionen = [] → holds r)
    (preserves : ∀ b ∈ p.code, ∀ r live, holds r → holds (b.auswerten r live))
    (ρ : I.Lauf (p.einheit platform)) (run : I.Laeufe _ ρ) (t : Nat) :
    ∀ c, holds ((ρ.zeit.zustand t).lokal c) := by
  induction t with
  | zero =>
      rw [run.2.2.2.1]
      intro c
      exact boot _ rfl rfl
  | succ t ih =>
      cases ρ.zeit.takt t with
      | wartet label eq _ =>
          rw [(ρ.zeit.wartet label).1]
          exact ih
      | schritt label step =>
          cases step with
          | kontext hkb hber hreg haus =>
              rename_i u plan spur c w
              obtain ⟨b, head, ideal⟩ := hreg
              have mem : b ∈ p.code := kopf_mem head
              have hi : b.ideal c (ρ.zeit.zustand t) w [plan] u := ideal
              obtain ⟨plans, after⟩ := (b.ideal_privat (privat b mem) c _ w [plan] u).1 hi
              have still : plan.aktion.Still := by
                rw [(List.cons.inj plans).1]
                exact (b.privat_still_leer (privat b mem) _).1
              obtain ⟨_, _, _, v, hfa, _, eq⟩ := haus
              obtain ⟨_, _, localEq, _, _⟩ := hfa.still_erhaelt still
              rw [eq]
              intro d
              change holds (v.lokal d)
              rw [localEq, after]
              by_cases same : d = c
              · subst d
                rw [b.nach_lokal_eigener]
                exact preserves b mem _ _ (ih c)
              · rw [b.nach_lokal_anderer same]
                exact ih d
          | antwort _ h =>
              obtain ⟨_, _, _, eq⟩ := h
              rw [eq]
              exact ih
          | interrupt _ h =>
              obtain ⟨_, _, _, _, _, _, _, _, _, _, eq⟩ := h
              rw [eq]
              exact ih
          | absturz h =>
              obtain ⟨_, eq⟩ := AbsturzSchritt.genau h
              rw [eq]
              intro c
              exact boot _ rfl rfl

/-- The only partial operation indexes the one-byte literal at offset zero. -/
private def singletonIndexUnit : Ast.Unit :=
  let written : WrittenType := .integer false 8 none
  let value : Expr [] (.int 0 255) := Expr.textIndex (Expr.textLiteral ['x']) (Expr.lit 0)
  ⟨[⟨indexName, .int 0 255, false, true⟩],
    .step (.constant indexName indexName_ordinary written
      (by
        change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
        omega) value
      (by dsimp only [value, Expr.static]; exact ⟨trivial, trivial⟩)
      (by change (0 : Int) ≤ 0 ∧ (255 : Int) ≤ 255; omega)) .done⟩

private abbrev singletonFragment : Fragment := fragment .unit singletonIndexUnit
private abbrev singletonCapacity : Nat := (sourceUtf8 ['x']).size
private abbrev singletonIndex : Befehl := .textIndex 0 singletonCapacity

private theorem singletonCode :
    singletonFragment.code =
      [.textLiteral 0 ['x'], .literal 1 0, singletonIndex,
        .bindeWert 0 (.int 0 255) true, .starte mainName, .ende] := rfl

private theorem singletonLokal : lokalPruefeCode singletonFragment.code = true := by
  rw [singletonCode]
  rfl

private theorem singletonImFragment : waechterFragmentCode singletonFragment.code = true := by
  rw [singletonCode]
  rfl

private theorem singletonAbgelehnt : waechterPruefeCode singletonFragment.code = false := by
  rw [singletonCode]
  rfl

/-- A text value read at slot zero comes from the literal. The index can halt without
    changing the slot, or overwrite it with an integer; it cannot introduce a new text. -/
private abbrev singletonText (r : Semantik.Rahmen) : Prop :=
  ∀ t : TextValue singletonCapacity,
    (r.temp 0).bind (wertAls (.text singletonCapacity)) = some t → t.bytes.size = singletonCapacity

/-- No instruction of the unit installs a function, so its entry call can only halt. -/
private abbrev singletonRahmen (r : Semantik.Rahmen) : Prop :=
  r.funktionen = [] ∧ singletonText r

private theorem singletonIndexErhaelt (r : Semantik.Rahmen) (live : Nat → Bool)
    (h : singletonRahmen r) : singletonRahmen (singletonIndex.auswerten r live) := by
  change singletonRahmen ((Befehl.textIndex 0 singletonCapacity).auswerten r live)
  cases textEq : (r.temp 0).bind (wertAls (.text singletonCapacity)) with
  | none =>
      simp only [Befehl.auswerten, Id.run, textEq]
      exact h
  | some text =>
      cases offsetEq : r.zahl 1 with
      | none =>
          simp only [Befehl.auswerten, Id.run, textEq, offsetEq]
          exact h
      | some offset =>
          by_cases negative : offset.zahl.wert < 0
          · simp only [Befehl.auswerten, Id.run, textEq, offsetEq, if_pos negative]
            exact h
          · cases byteEq : text.bytes[offset.zahl.wert.toNat]? with
            | none =>
                simp only [Befehl.auswerten, Id.run, textEq, offsetEq, if_neg negative, byteEq]
                exact h
            | some byte =>
                have noText : wertAls (.text singletonCapacity) ⟨.int 0 255, byteValue byte⟩ = none := rfl
                simp only [Befehl.auswerten, Id.run, textEq, offsetEq, if_neg negative, byteEq]
                refine ⟨h.1, ?_⟩
                intro t lookup
                change ((Function.update r.temp 0 (some ⟨.int 0 255, byteValue byte⟩)) 0).bind
                  (wertAls (.text singletonCapacity)) = some t at lookup
                rw [Function.update_self, Option.bind_some, noText] at lookup
                cases lookup

private theorem singletonTextErhaelt (b : Befehl) (mem : b ∈ singletonFragment.code)
    (r : Semantik.Rahmen) (live : Nat → Bool) (h : singletonRahmen r) :
    singletonRahmen (b.auswerten r live) := by
  rw [singletonCode] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with eq | eq | eq | eq | eq | eq
  · subst b
    refine ⟨h.1, ?_⟩
    intro t lookup
    change ((Function.update r.temp 0 (some ⟨.text singletonCapacity, TextValue.literal ['x']⟩)) 0).bind
      (wertAls (.text singletonCapacity)) = some t at lookup
    have literalLookup :
        wertAls (.text singletonCapacity) ⟨.text singletonCapacity, TextValue.literal ['x']⟩ =
          some (TextValue.literal ['x']) :=
      wertAls_selbst (type := .text singletonCapacity) (TextValue.literal ['x'])
    rw [Function.update_self, Option.bind_some, literalLookup] at lookup
    cases lookup
    rfl
  · subst b
    refine ⟨h.1, ?_⟩
    intro t lookup
    change ((Function.update r.temp 1 (some ⟨.int 0 0, Zahl.literal 0⟩)) 0).bind
      (wertAls (.text singletonCapacity)) = some t at lookup
    rw [Function.update_of_ne (show (0 : Nat) ≠ 1 by decide)] at lookup
    exact h.2 t lookup
  · subst b
    exact singletonIndexErhaelt r live h
  · subst b
    exact h
  · subst b
    have halts : (Befehl.starte mainName).auswerten r live = r.halt (.ungueltigerRuf mainName) := by
      simp only [Befehl.auswerten, Id.run, h.1, List.map_nil, List.nodup_nil, not_true_eq_false,
        if_false, List.find?_nil, List.flatMap_nil, Funktion.finde] <;> rfl
    rw [halts]
    exact h
  · subst b
    exact h

private theorem singletonBedarf (b : Befehl) (mem : b ∈ singletonFragment.code)
    (r : Semantik.Rahmen) (htext : singletonText r) (joined : RahmenErfuellt singletonFragment.code r)
    (op : PartielleOperation) (args : Operanden op) (guard : b.guard r = some ⟨op, args⟩) :
    waechterBedarf op args := by
  rw [singletonCode] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  have index : b = singletonIndex := by
    rcases mem with eq | eq | eq | eq | eq | eq
    · subst b; cases guard
    · subst b; cases guard
    · exact eq
    · subst b; cases guard
    · subst b; cases guard
    · subst b; cases guard
  subst b
  change ((r.temp 0).bind (wertAls (.text singletonCapacity))).bind
    (fun text => (r.zahl 1).bind fun offset => pure
      (⟨.index, ((if offset.zahl.wert < 0 then text.bytes.size else offset.zahl.wert.toNat),
        text.bytes.size)⟩ : Bedarf)) = some ⟨op, args⟩ at guard
  cases textEq : (r.temp 0).bind (wertAls (.text singletonCapacity)) with
  | none =>
      rw [textEq, Option.bind_none] at guard
      cases guard
  | some text =>
      cases offsetEq : r.zahl 1 with
      | none =>
          rw [textEq, Option.bind_some, offsetEq, Option.bind_none] at guard
          cases guard
      | some offset =>
          rw [textEq, Option.bind_some, offsetEq, Option.bind_some] at guard
          cases guard
          have textSize := htext text textEq
          have positive : 0 < singletonCapacity := by
            change 0 < (sourceUtf8 ['x']).size
            rw [sourceUtf8, String.size_toByteArray, ← String.singleton_eq_ofList,
              String.utf8ByteSize_singleton]
            exact Char.utf8Size_pos _
          have hull : umgebungInt singletonFragment.code 1 = some (0, 0) := by
            rw [singletonCode]
            rfl
          have bounds := joined.1 1 0 0 hull offset offsetEq
          have zero : offset.zahl.wert = 0 := by omega
          change (if offset.zahl.wert < 0 then text.bytes.size else offset.zahl.wert.toNat) <
            text.bytes.size
          rw [zero, if_neg (Int.lt_irrefl 0), textSize]
          exact positive

private theorem singletonWaechter (platform : Plattform) :
    WaechterHalten (singletonFragment.einheit platform) := by
  have privateCode := (lokalPruefeCode_iff singletonFragment).mp singletonLokal
  have noAccess : singletonFragment.code.all keinFremdzugriff = true := by
    rw [singletonCode]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro ρ run t op args demand
    obtain ⟨c, b, head, guard⟩ : ∃ c b,
        kopf singletonFragment.code (ρ.zeit.zustand t.val) c = some b ∧
        b.guard ((ρ.zeit.zustand t.val).lokal c) = some ⟨op, args⟩ := demand
    have frame : singletonRahmen ((ρ.zeit.zustand t.val).lokal c) := by
      apply privatRahmenInvariant singletonFragment platform privateCode singletonRahmen
        ?_ singletonTextErhaelt ρ run t.val c
      intro r empty noFunctions
      refine ⟨noFunctions, ?_⟩
      intro v lookup
      rw [empty, Option.bind_none] at lookup
      cases lookup
    exact singletonBedarf b (kopf_mem head) _ frame.2
      ((invariantAlle singletonFragment platform noAccess ρ run t.val).1 c) op args guard
  · intro ρ _ t closed
    obtain ⟨C, ⟨c, member⟩, blocked⟩ := closed
    obtain ⟨_, impossible, _⟩ := blocked c member
    exact False.elim impossible
  · intro ρ run t lock holder held
    rw [(invariantAlle singletonFragment platform noAccess ρ run t.val).2 lock] at held
    cases held

/-- Excluding the index instruction from the fragment's writer count still leaves it in
    the analysis. Its integer result poisons the text-length lookup of its own input. -/
theorem waechterFragmentVollstaendig_widerlegt : ¬ WaechterFragmentVollstaendigAussage := by
  intro complete
  have verdict := complete singletonFragment .x86_64 singletonImFragment (singletonWaechter .x86_64)
  rw [singletonAbgelehnt] at verdict
  cases verdict

theorem prueferWaechterVollstaendig_widerlegt : ¬ PrueferWaechterVollstaendigAussage := by
  intro complete
  have verdict : waechterPruefeCode singletonFragment.code = true :=
    complete .x86_64 singletonIndexUnit singletonImFragment (singletonWaechter .x86_64)
  rw [singletonAbgelehnt] at verdict
  cases verdict

theorem prueferKombiniert_vollstaendig_widerlegt :
    ¬ PrueferVollstaendigAussage prueferKombiniert := by
  intro complete
  have clauseFragment : prueferKombiniert.fragmentKlauseln .x86_64 ⟨singletonIndexUnit, []⟩ = true := by
    show (programmMitInvarianten ⟨singletonIndexUnit, []⟩).code.all (pruefeBefehlErhalt []) = true
    exact List.all_eq_true.mpr (fun _ _ => rfl)
  have inFragment : prueferKombiniert.fragment .x86_64 singletonIndexUnit = true := by
    simp only [Pruefer.fragment, Bool.and_eq_true]
    exact ⟨⟨singletonLokal, clauseFragment⟩, singletonImFragment⟩
  have klauseln : KlauselnWahr (einheitVon .x86_64 singletonIndexUnit) := by
    rw [einheitVon_mitInvarianten]
    exact prueferKlauselnKorrekt_fuerDecidierbar _ _ (pruefeEinheit_leer _)
  have verdict := complete .x86_64 singletonIndexUnit inFragment
    ⟨lokalAbstrakt _ _ singletonLokal, klauseln, singletonWaechter .x86_64⟩
  simp only [Pruefer.pruefe, Bool.and_eq_true] at verdict
  have guardVerdict : waechterPruefeCode singletonFragment.code = true := verdict.2
  rw [singletonAbgelehnt] at guardVerdict
  cases guardVerdict

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
