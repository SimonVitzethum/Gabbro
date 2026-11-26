module

public import Core.Beobachtung.SchrankenBeweise.KostenEndlichBeweise
public import Core.Beobachtung.SchrankenBeweise.Kosten.MassHerkunft
import Core.Ast.Semantik.Auswertung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Maschine

private theorem pruefeMass_einrichtung {u : Ast.Unit} {name : Identifier}
    {kern : FunktionsKern} {m : Measure kern.koerper.1}
    (found : findeKern u.2 name = some kern) (declared : kern.mass = some m)
    {r : Rahmen} (owner : r.funktion = some name) (value : Zahl m.lo m.hi)
    (operand : r.temp 0 = some ⟨.int m.lo m.hi, value⟩) :
    KostenEinrichtung u (.pruefeMass 0) r := by
  intro id a other lo hi named read _ lookup interval
  have sameName : name = id := Option.some.inj (owner.symm.trans named)
  subst id
  have sameKern : kern = other := Option.some.inj (found.symm.trans lookup)
  subst other
  have endpoints : some (m.lo, m.hi) = some (lo, hi) := by
    simpa only [FunktionsKern.massIntervall, declared, Option.map_some] using interval
  cases endpoints
  have exactRead : some (⟨m.lo, m.hi, value⟩ : Ganzzahl) = some a := by
    simpa only [Rahmen.zahl, operand, Option.bind, alsGanzzahl] using read
  cases exactRead
  exact ⟨le_rfl, le_rfl⟩

/-- A cut's head identifies the exact source prologue address without using
    information about the current frame's call history. -/
theorem kostenKopf_pruefeMass_herkunft (P : Katalog.Plattform) (u : UnitMitSchranken)
    {s : Zustand} {c : Kontext} {slot : Nat}
    (head : (einheitMitSchranken P u).system.kopf s c = some (.pruefeMass slot)) :
    ∃ (name : Identifier) (kern : FunktionsKern) (m : Measure kern.koerper.1)
      (pre post : List Befehl),
      name ∈ alleFunktionen u.baum.2 ∧
      (((alleFunktionen u.baum.2).map Subtype.val).Nodup → findeKern u.baum.2 name = some kern) ∧
      kern.mass = some m ∧
      (∃ earlier params result globals skip calls effects,
        pre = earlier ++ [.definiere name params result globals skip true calls effects]) ∧
      (∃ later, post = (bracedBlock kern.koerper.2.2).code ++ (.rueckVoid :: later)) ∧
      (programm u.baum).code = pre ++ (measurePrologue (some m)).code ++ post ∧
      (s.lokal c).pc = pre.length + (expr 0 m.expression).code.length ∧ slot = 0 :=
  programm_pruefeMass_herkunft (u := u.baum) (kopf_position head)

private theorem lauf_ersterSchritt (walk : Rahmen.Lauf code start finish) :
    start = finish ∨ ∃ next, Rahmen.Schritt code start next ∧ Rahmen.Lauf code next finish := by
  induction walk with
  | start => exact .inl rfl
  | schritt _ step ih =>
    rcases ih with same | ⟨next, first, rest⟩
    · cases same
      exact .inr ⟨_, step, .start⟩
    · exact .inr ⟨next, first, rest.schritt step⟩

private theorem schritt_eindeutig (left : Rahmen.Schritt code start a)
    (right : Rahmen.Schritt code start b) : a = b := by
  obtain ⟨i, _, _, lookup, rfl⟩ := left
  obtain ⟨j, _, _, lookup', rfl⟩ := right
  cases Option.some.inj (lookup.symm.trans lookup')
  rfl

private theorem lauf_erhaeltEnde {code : List Befehl} (walk : Rahmen.Lauf code start a)
    (other : Rahmen.Lauf code start b) (otherEnd : code[b.pc]? = none) :
    Rahmen.Lauf code a b := by
  induction walk with
  | start => exact other
  | schritt _ step ih =>
    rcases lauf_ersterSchritt ih with same | ⟨next, first, rest⟩
    · rw [same] at step
      obtain ⟨_, _, _, lookup, _⟩ := step
      rw [otherEnd] at lookup
      cases lookup
    · rw [schritt_eindeutig step first]
      exact rest

private theorem lauf_ende_eindeutig {code : List Befehl} (walk : Rahmen.Lauf code start a)
    (atEnd : code[a.pc]? = none) (other : Rahmen.Lauf code start b)
    (otherEnd : code[b.pc]? = none) : a = b := by
  rcases lauf_ersterSchritt (lauf_erhaeltEnde walk other otherEnd) with same | ⟨_, step, _⟩
  · exact same
  · obtain ⟨_, _, _, lookup, _⟩ := step
    rw [atEnd] at lookup
    cases lookup

/-- A frame reached by the actual measure-prefix walk has the declared
    operand, by determinism up to the end of that prefix. -/
theorem pruefeMass_kostenEinrichtung_amEnde {u : Ast.Unit} {name : Identifier}
    {kern : FunktionsKern} {m : Measure kern.koerper.1}
    (found : findeKern u.2 name = some kern) (declared : kern.mass = some m)
    (env : Umgebung kern.koerper.1) (pre post : List Befehl)
    (code : (programm u).code = pre ++ (measurePrologue (some m)).code ++ post)
    {entry r : Rahmen} (entryPC : entry.pc = pre.length)
    (atCheck : r.pc = pre.length + (expr 0 m.expression).code.length)
    (active : entry.Aktiv) (typed : entry.traegt env) (owner : entry.funktion = some name)
    (checked : entry.WaechterHalten (programm u).code)
    (walk : Rahmen.Lauf (pre ++ (expr 0 m.expression).code) entry r) :
    r.funktion = some name ∧ KostenEinrichtung u (.pruefeMass 0) r := by
  let prefixCode := pre ++ (expr 0 m.expression).code
  have layout : (programm u).code = prefixCode ++ (.pruefeMass 0 :: post) := by
    simpa only [prefixCode, measurePrologue, Fragment.anhaengen, Fragment.einzel,
      List.append_assoc, List.singleton_append] using code
  have guarded : entry.WaechterHalten prefixCode := (layout ▸ checked).prefix
  obtain ⟨out, trace, operand⟩ :=
    expr_ergebnis_typ_am 0 m.expression env entry typed active pre [] entryPC
      (by simpa only [List.append_nil, prefixCode] using guarded)
  have outWalk : Rahmen.Lauf prefixCode entry out := by
    simpa only [List.append_nil, prefixCode] using trace.walk
  have atEnd (frame : Rahmen) (position : frame.pc = pre.length + (expr 0 m.expression).code.length) :
      prefixCode[frame.pc]? = none := by
    rw [List.getElem?_eq_none_iff, position]
    simp only [prefixCode, List.length_append, Nat.le_refl]
  have same := lauf_ende_eindeutig outWalk (atEnd out trace.position) walk (atEnd r atCheck)
  have named : out.funktion = some name := (congrArg Rahmen.funktion trace.frame).trans owner
  exact same ▸ ⟨named, pruefeMass_einrichtung found declared named (m.expression.wert env) operand⟩

/-- Evaluate the declared measure at its entry address and execute the actual
    installer. Both a successful write and a rejected decrease preserve the
    cost invariant, including the saved frames. -/
theorem measurePrologue_kostenEinrichtung {u : Ast.Unit} {name : Identifier}
    {kern : FunktionsKern} {m : Measure kern.koerper.1}
    (found : findeKern u.2 name = some kern) (declared : kern.mass = some m)
    (env : Umgebung kern.koerper.1) (pre post : List Befehl)
    (code : (programm u).code = pre ++ (measurePrologue (some m)).code ++ post)
    (entry : Rahmen) (position : entry.pc = pre.length) (active : entry.Aktiv)
    (typed : entry.traegt env) (owner : entry.funktion = some name)
    (checked : entry.WaechterHalten (programm u).code)
    (good : (kostenGrenzen u).RahmenGut entry) :
    ∃ r, Ausdrucksabschnitt (programm u).code (pre.length + (expr 0 m.expression).code.length) 0 entry r ∧
      (programm u).code[r.pc]? = some (.pruefeMass 0) ∧
      KostenEinrichtung u (.pruefeMass 0) r ∧
      Rahmen.Lauf (programm u).code entry ((Befehl.pruefeMass 0).auswerten r) ∧
      (kostenGrenzen u).RahmenGut ((Befehl.pruefeMass 0).auswerten r) ∧
      (((Befehl.pruefeMass 0).auswerten r).mass = some (m.expression.wert env).wert.toNat ∨
        ¬ ((Befehl.pruefeMass 0).auswerten r).Aktiv) := by
  have layout : (programm u).code = pre ++ (expr 0 m.expression).code ++ (.pruefeMass 0 :: post) := by
    simpa only [measurePrologue, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
      List.singleton_append] using code
  obtain ⟨r, trace, operand⟩ :=
    expr_ergebnis_typ_am 0 m.expression env entry typed active pre (.pruefeMass 0 :: post) position
      (layout ▸ checked)
  rw [← layout] at trace
  have lookup : (programm u).code[r.pc]? = some (.pruefeMass 0) := by
    rw [layout, trace.position, ← List.length_append,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have named : r.funktion = some name := (congrArg Rahmen.funktion trace.frame).trans owner
  have install := pruefeMass_einrichtung found declared named (m.expression.wert env) operand
  have atWrite : (kostenGrenzen u).RahmenGut r := by
    rw [trace.frame]
    exact good
  have running := trace.aktiv active
  refine ⟨r, trace, lookup, install, trace.walk.schritt ⟨_, running.1, running.2, lookup, rfl⟩,
    KostenGrenzen.auswerten atWrite install.gueltig _, ?_⟩
  have read : r.zahl 0 = some ⟨m.lo, m.hi, m.expression.wert env⟩ := by
    rw [Rahmen.zahl, operand]
    rfl
  simp only [Befehl.auswerten, Rahmen.setzeMass, Id.run, named, read]
  repeat' first
    | exact Or.inl rfl
    | exact Or.inr (fun stopped => by cases stopped.1)
    | split

private theorem loop_left {a b : Fragment} {pc : Nat} {limit : SchleifenGrenze}
    (atTest : (pc, limit) ∈ a.schleifen) : (pc, limit) ∈ (a.anhaengen b).schleifen :=
  List.mem_append_left _ atTest

private theorem loop_right {a b : Fragment} {pc : Nat} {limit : SchleifenGrenze}
    (atTest : (pc, limit) ∈ b.schleifen) :
    (pc + a.code.length, limit) ∈ (a.anhaengen b).schleifen :=
  List.mem_append_right _ (List.mem_map.mpr ⟨(pc, limit), atTest, rfl⟩)

private theorem loop_relocated {pre body post : Fragment} {pc : Nat} {limit : SchleifenGrenze}
    {u : Ast.Unit}
    (table : (programm u).schleifen = ((pre.anhaengen body).anhaengen post).schleifen)
    (atTest : (pc, limit) ∈ body.schleifen) :
    (pc + pre.code.length, limit) ∈ (programm u).schleifen := by
  rw [table]
  exact loop_left (loop_right atTest)

/-- The while setup and its table row remain paired when the source statement
    is placed in the unit. The setup counts from its own PC past the condition. -/
theorem whileBounded_kostenEinrichtung {u : Ast.Unit} {lo hi : Int}
    (condition : Expr scope .bool) (bound : Expr scope (.int lo hi))
    (static : bound.static) (nonnegative : 0 ≤ lo) (handler : Identifier)
    (body : BracedBlock result scope) (pre post : Fragment) (r : Rahmen)
    (table : (programm u).schleifen =
      ((pre.anhaengen (stmt (.whileBounded condition bound static nonnegative handler body))).anhaengen
        post).schleifen)
    (position : r.pc = pre.code.length + (expr 0 bound).code.length)
    (value : Zahl lo hi) (operand : r.temp 0 = some ⟨.int lo hi, value⟩) :
    KostenEinrichtung u (.setzePasszahl 0 ((expr 0 condition).code.length + 1)) r := by
  let limit := SchleifenGrenze.whileBounded bound
  have localRow :
      ((expr 0 bound).code.length + ((expr 0 condition).code.length + 1), limit) ∈
        (stmt (.whileBounded condition bound static nonnegative handler body)).schleifen := by
    rw [stmt]
    apply loop_left
    apply loop_left
    have row := loop_right (a := (((expr 0 bound).anhaengen
      (.einzel (.setzePasszahl 0 ((expr 0 condition).code.length + 1)))).anhaengen (expr 0 condition)))
      (b := { Fragment.einzel (whileInstruction condition (bracedBlock body) handler) with
        schleifen := [(0, limit)] }) List.mem_cons_self
    simpa only [Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using row
  have row := loop_relocated table localRow
  intro a read
  have same : some (⟨lo, hi, value⟩ : Ganzzahl) = some a := by
    simpa only [Rahmen.zahl, operand, Option.bind, alsGanzzahl] using read
  cases same
  refine ⟨limit, ?_, Nat.le_refl _⟩
  rw [position]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using row

/-- The range setup installs both fields at its following instruction, using
    the same typed endpoints as the relocated range-test row. -/
theorem forRange_kostenEinrichtung {u : Ast.Unit} {low lowHi highLo high : Int}
    (name : Identifier) (ordinary : ordinaryLocal name)
    (lower : Expr scope (.int low lowHi)) (upper : Expr scope (.int highLo high))
    (static : lower.static ∧ upper.static) (handler : Option Identifier)
    (body : BracedBlock result (rangeBinding name low high :: scope))
    (pre post : Fragment) (r : Rahmen)
    (table : (programm u).schleifen =
      ((pre.anhaengen (stmt (.forRange name ordinary lower upper static handler body))).anhaengen
        post).schleifen)
    (position : r.pc = pre.code.length + ((expr 0 lower).code.length + (expr 1 upper).code.length))
    (start : Zahl low lowHi) (stop : Zahl highLo high)
    (lowerOperand : r.temp 0 = some ⟨.int low lowHi, start⟩)
    (upperOperand : r.temp 1 = some ⟨.int highLo high, stop⟩) :
    KostenEinrichtung u
      (.forAnfang 0 1 (rangeBinding name low high).type ((bracedBlock body).code.length + 4)
        (BracedBlock.rangeUses name body).1 ((BracedBlock.rangeUses name body).2 && handler.isNone)) r := by
  let limit := SchleifenGrenze.forRange lower upper
  have localRow :
      ((expr 0 lower).code.length + (expr 1 upper).code.length + 1, limit) ∈
        (stmt (.forRange name ordinary lower upper static handler body)).schleifen := by
    cases uses : BracedBlock.rangeUses name body with
    | mk shadows writes =>
      simp only [stmt, uses]
      apply loop_left
      apply loop_left
      apply loop_left
      have row := loop_right (a := (((expr 0 lower).anhaengen (expr 1 upper)).anhaengen
        (.einzel (.forAnfang 0 1 (rangeBinding name low high).type ((bracedBlock body).code.length + 4)
          shadows (writes && handler.isNone)))))
        (b := { Fragment.einzel (forInstruction (bracedBlock body) handler) with
          schleifen := [(0, limit)] }) List.mem_cons_self
      simpa only [Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add] using row
  have row := loop_relocated table localRow
  intro a b readA readB _
  have sameA : some (⟨low, lowHi, start⟩ : Ganzzahl) = some a := by
    simpa only [Rahmen.zahl, lowerOperand, Option.bind, alsGanzzahl] using readA
  have sameB : some (⟨highLo, high, stop⟩ : Ganzzahl) = some b := by
    simpa only [Rahmen.zahl, upperOperand, Option.bind, alsGanzzahl] using readB
  cases sameA
  cases sameB
  refine ⟨limit, high, ?_, Nat.le_refl _, rfl, le_rfl⟩
  rw [position]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using row

/-- The declaration selected by the estimator contributes its own measure
    prologue immediately after its declaration instruction. -/
private theorem findeKern_prologImRumpf {source : UnitBody before after}
    {name : Identifier} {kern : FunktionsKern} (found : findeKern source name = some kern) :
    ∃ (pre post : List Befehl) (header : Befehl),
      (unitBody source).code = (pre ++ [header]) ++ (measurePrologue kern.mass).code ++ post := by
  induction source with
  | done => cases found
  | @step before middle after first rest ih =>
    have next (lookup : findeKern rest name = some kern) :
        ∃ (pre post : List Befehl) (header : Befehl),
          (unitBody (.step first rest)).code =
            (pre ++ [header]) ++ (measurePrologue kern.mass).code ++ post := by
      obtain ⟨pre, post, header, layout⟩ := ih lookup
      refine ⟨(decl first).code ++ pre, post, header, ?_⟩
      simp only [unitBody, Fragment.anhaengen, layout, List.append_assoc]
    cases first with
    | function fn ordinary params result valid measure body distinct returns effects =>
      rw [findeKern] at found
      split at found
      · cases found
        let code := functionCode result measure body
        refine ⟨[], (bracedBlock body).code ++ [.rueckVoid] ++ (unitBody rest).code,
          functionInstruction before fn params result measure.isSome code (declaredEffects effects), ?_⟩
        simp only [unitBody, decl, code, functionCode, Fragment.anhaengen,
          Fragment.einzel, List.nil_append, List.append_assoc]
      · exact next found
    | _ => exact next found

/-- Lookup yields the exact prefix ending at the declaration and the suffix
    after the measured entry code, in the installed unit's instruction list. -/
theorem findeKern_measurePrologue {u : Ast.Unit} {name : Identifier}
    {kern : FunktionsKern} {m : Measure kern.koerper.1}
    (found : findeKern u.2 name = some kern) (declared : kern.mass = some m) :
    ∃ (pre post : List Befehl) (header : Befehl),
      (programm u).code = (pre ++ [header]) ++ (measurePrologue (some m)).code ++ post := by
  obtain ⟨pre, post, header, layout⟩ := findeKern_prologImRumpf found
  refine ⟨pre, post ++ [.starte mainName, .ende], header, ?_⟩
  simp only [programm, Fragment.anhaengen, Fragment.einzel, layout, declared,
    List.append_assoc, List.singleton_append]

/-- Starting at the placed while statement, the actual bound expression
    produces the operand for the next instruction and its relocated table row. -/
theorem whileBounded_kostenEinrichtung_am {u : Ast.Unit} {lo hi : Int}
    (condition : Expr scope .bool) (bound : Expr scope (.int lo hi))
    (static : bound.static) (nonnegative : 0 ≤ lo) (handler : Identifier)
    (body : BracedBlock result scope) (pre post : Fragment)
    (code : (programm u).code =
      ((pre.anhaengen (stmt (.whileBounded condition bound static nonnegative handler body))).anhaengen
        post).code)
    (table : (programm u).schleifen =
      ((pre.anhaengen (stmt (.whileBounded condition bound static nonnegative handler body))).anhaengen
        post).schleifen)
    (env : Umgebung scope) (entry : Rahmen) (position : entry.pc = pre.code.length)
    (active : entry.Aktiv) (typed : entry.traegt env)
    (checked : entry.WaechterHalten (programm u).code) :
    let setup := Befehl.setzePasszahl 0 ((expr 0 condition).code.length + 1)
    ∃ r, Rahmen.Lauf (programm u).code entry r ∧
      (programm u).code[r.pc]? = some setup ∧ KostenEinrichtung u setup r := by
  let test := expr 0 condition
  let inner := bracedBlock body
  let setup := Befehl.setzePasszahl 0 (test.code.length + 1)
  let tail := test.code ++ [whileInstruction condition inner handler] ++ inner.code ++
    [.zurueckSprung (test.code.length + inner.code.length + 1)] ++ post.code
  have layout : (programm u).code = pre.code ++ (expr 0 bound).code ++ (setup :: tail) := by
    simpa only [stmt, Fragment.anhaengen, Fragment.einzel, setup, tail, inner, test,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using code
  obtain ⟨r, trace, operand⟩ :=
    expr_ergebnis_typ_am 0 bound env entry typed active pre.code (setup :: tail) position
      (layout ▸ checked)
  rw [← layout] at trace
  refine ⟨r, trace.walk, ?_, whileBounded_kostenEinrichtung condition bound static nonnegative handler
    body pre post r table trace.position (bound.wert env) operand⟩
  rw [layout, trace.position, ← List.length_append,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- Starting at the placed range statement, evaluation of the upper operand
    preserves the lower temporary and reaches the actual two-operand setup. -/
theorem forRange_kostenEinrichtung_am {u : Ast.Unit} {low lowHi highLo high : Int}
    (name : Identifier) (ordinary : ordinaryLocal name)
    (lower : Expr scope (.int low lowHi)) (upper : Expr scope (.int highLo high))
    (static : lower.static ∧ upper.static) (handler : Option Identifier)
    (body : BracedBlock result (rangeBinding name low high :: scope))
    (pre post : Fragment)
    (code : (programm u).code =
      ((pre.anhaengen (stmt (.forRange name ordinary lower upper static handler body))).anhaengen
        post).code)
    (table : (programm u).schleifen =
      ((pre.anhaengen (stmt (.forRange name ordinary lower upper static handler body))).anhaengen
        post).schleifen)
    (env : Umgebung scope) (entry : Rahmen) (position : entry.pc = pre.code.length)
    (active : entry.Aktiv) (typed : entry.traegt env)
    (checked : entry.WaechterHalten (programm u).code) :
    let uses := BracedBlock.rangeUses name body
    let setup := Befehl.forAnfang 0 1 (rangeBinding name low high).type
      ((bracedBlock body).code.length + 4) uses.1 (uses.2 && handler.isNone)
    ∃ r, Rahmen.Lauf (programm u).code entry r ∧
      (programm u).code[r.pc]? = some setup ∧ KostenEinrichtung u setup r := by
  let inner := bracedBlock body
  let index := (rangeBinding name low high).type
  let uses := BracedBlock.rangeUses name body
  let setup := Befehl.forAnfang 0 1 index (inner.code.length + 4) uses.1 (uses.2 && handler.isNone)
  let tail := [forInstruction inner handler] ++ inner.code ++
    [.forNaechster (inner.code.length + 1) index, .blockEnde 1] ++ post.code
  let earlierCode := pre.code ++ (expr 0 lower).code
  have layout : (programm u).code = earlierCode ++ ((expr 1 upper).code ++ (setup :: tail)) := by
    cases useCase : BracedBlock.rangeUses name body with
    | mk shadows writes =>
      simpa only [stmt, useCase, Fragment.anhaengen, Fragment.einzel, earlierCode,
        setup, tail, inner, index, uses, List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using code
  obtain ⟨mid, lowTrace, lowValue⟩ :=
    expr_ergebnis_typ_am 0 lower env entry typed active pre.code
      ((expr 1 upper).code ++ (setup :: tail)) position (layout ▸ checked)
  rw [← layout] at lowTrace
  have layoutUpper : (programm u).code = earlierCode ++ (expr 1 upper).code ++ (setup :: tail) := by
    rw [List.append_assoc, ← layout]
  have middle : mid.pc = earlierCode.length := lowTrace.position.trans List.length_append.symm
  obtain ⟨r, highTrace, highValue⟩ :=
    expr_ergebnis_typ_am 1 upper env mid (lowTrace.traegt typed) (lowTrace.aktiv active) earlierCode
      (setup :: tail) middle (layoutUpper ▸ checked.after lowTrace.walk)
  rw [← layoutUpper] at highTrace
  have atSetup : r.pc = pre.code.length + ((expr 0 lower).code.length + (expr 1 upper).code.length) := by
    simpa only [earlierCode, List.length_append, Nat.add_assoc] using highTrace.position
  have lowRetained := (highTrace.lower 0 (Nat.zero_lt_succ _)).trans lowValue
  refine ⟨r, lowTrace.walk.trans highTrace.walk, ?_,
    forRange_kostenEinrichtung name ordinary lower upper static handler body pre post r table atSetup
      (lower.wert env) (upper.wert env) lowRetained highValue⟩
  rw [layoutUpper, highTrace.position, ← List.length_append,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

end Gabbro.Core.Beobachtung
