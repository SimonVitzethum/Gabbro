module

public import Core.Beobachtung.SchrankenBeweise.KostenSchaetzer
import Core.Ast.Program.Control

public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

private def OhneMass (code : List Befehl) : Prop :=
  ∀ slot, Befehl.pruefeMass slot ∉ code

private theorem OhneMass.nil : OhneMass [] :=
  fun _ h => List.not_mem_nil h

private theorem OhneMass.append (a : OhneMass left) (b : OhneMass right) :
    OhneMass (left ++ right) := by
  intro slot h
  exact (List.mem_append.mp h).elim (a slot) (b slot)

private theorem OhneMass.single (h : ∀ slot, Befehl.pruefeMass slot ≠ b) :
    OhneMass [b] := fun slot atHead => h slot (List.mem_singleton.mp atHead)

private theorem expr_ohneMass (slot : Nat) (e : Expr scope type) :
    OhneMass (expr slot e).code := by
  intro src present
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp present
  let r : Rahmen := { Rahmen.start [] with funktion := some mainName }
  have effect := ((expr_ausdruckscode slot e) i _ lookup).2 r
  have haltAt : (Befehl.pruefeMass src).auswerten r = r.halt (.abstieg mainName) := rfl
  rw [haltAt] at effect
  rcases effect with ⟨advances, _, _⟩ | stopped
  · exact (Nat.lt_irrefl r.pc) advances
  · have stopEq := congrArg Rahmen.stopp stopped
    cases stopEq

private theorem args_ohneMass (slot : Nat) (args : List (TypedExpr scope)) :
    OhneMass (argsCode slot args).code := by
  induction args generalizing slot with
  | nil => exact .nil
  | cons arg args ih => exact .append (expr_ohneMass slot arg.2) (ih _)

private theorem option_ohneMass (slot : Nat) (value : OptionInitializer scope count) :
    OhneMass (optionCode slot value).code := by
  apply OhneMass.append
  · cases value
    · exact .nil
    · exact expr_ohneMass _ _
  · exact .single (fun _ h => by cases h)

private theorem access_ohneMass (a : Access before after) : OhneMass (accessCode a).code := by
  cases a <;> simp only [accessCode, Fragment.anhaengen, Fragment.einzel]
  all_goals
    apply_rules [OhneMass.append, expr_ohneMass, OhneMass.single]
    intro slot same
    cases same

private theorem braced_ohneMass (tree : BracedBlock result before) :
    OhneMass (bracedBlock tree).code := by
  refine @BracedBlock.rec result
    (fun _ _ t => OhneMass (stmt t).code)
    (fun _ _ t => OhneMass (block t).code)
    (fun _ t => OhneMass (bracedBlock t).code)
    (fun _ _ _ _ t => OhneMass (variantArms t).body.code)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before tree
  all_goals
    intros
    first
    | assumption
    | apply access_ohneMass
    | (simp only [stmt, block, bracedBlock, variantArms, callCode, callInstruction, whileInstruction,
        forInstruction, MatchCode.prepend, Bool.false_eq_true, if_false, if_true, Fragment.anhaengen,
        Fragment.einzel]
       try split
       all_goals
         apply_rules [OhneMass.nil, OhneMass.append, expr_ohneMass, args_ohneMass,
           option_ohneMass, OhneMass.single]
         intro slot same
         cases same)

private theorem OhneMass.not_at (free : OhneMass code) (atPC : code[pc]? = some (.pruefeMass slot)) :
    False :=
  free slot (List.mem_iff_getElem?.mpr ⟨pc, atPC⟩)

private theorem mass_imRumpf (source : UnitBody before after) {pc slot : Nat}
    (atPC : (unitBody source).code[pc]? = some (.pruefeMass slot)) :
    ∃ (name : Identifier) (kern : FunktionsKern) (m : Measure kern.koerper.1)
      (pre post : List Befehl),
      name ∈ alleFunktionen source ∧ kern.mass = some m ∧
      (unitBody source).code = pre ++ (measurePrologue (some m)).code ++ post ∧
      pc = pre.length + (expr 0 m.expression).code.length ∧ slot = 0 := by
  induction source generalizing pc with
  | done => cases atPC
  | @step before middle after first rest ih =>
    by_cases inside : pc < (decl first).code.length
    · have localPC : (decl first).code[pc]? = some (.pruefeMass slot) :=
        (List.getElem?_append_left inside).symm.trans atPC
      cases first with
      | function name ordinary params result valid measure body distinct returns effects =>
        let code := functionCode result measure body
        let header := functionInstruction before name params result measure.isSome code (declaredEffects effects)
        have restFree : OhneMass ((bracedBlock body).code ++ [.rueckVoid]) :=
          .append (braced_ohneMass body) (.single (fun _ same => by cases same))
        have layout : (decl (.function name ordinary params result valid measure body distinct returns effects)).code =
            [header] ++ (measurePrologue measure).code ++ ((bracedBlock body).code ++ [.rueckVoid]) := by
          simp only [decl, code, header, functionCode, Fragment.anhaengen, Fragment.einzel, List.append_assoc]
        rw [layout] at localPC
        by_cases prolog : pc < ([header] ++ (measurePrologue measure).code).length
        · rw [List.getElem?_append_left prolog] at localPC
          cases measure with
          | none => exact False.elim ((OhneMass.append (.single (fun _ h => by cases h)) .nil).not_at localPC)
          | some m =>
            have splitCode : [header] ++ (measurePrologue (some m)).code =
                ([header] ++ (expr 0 m.expression).code) ++ [.pruefeMass 0] := by
              simp only [measurePrologue, Fragment.anhaengen, Fragment.einzel, List.append_assoc]
            rw [splitCode] at localPC
            have free : OhneMass ([header] ++ (expr 0 m.expression).code) :=
              .append (.single (fun _ h => by cases h)) (expr_ohneMass 0 m.expression)
            by_cases earlier : pc < ([header] ++ (expr 0 m.expression).code).length
            · rw [List.getElem?_append_left earlier] at localPC
              exact False.elim (free.not_at localPC)
            · have bound := (List.getElem?_eq_some_iff.mp localPC).1
              have position : pc = [header].length + (expr 0 m.expression).code.length := by
                simp only [List.length_append, List.length_singleton] at earlier bound ⊢
                omega
              have zeroSlot : slot = 0 := by
                rw [List.getElem?_append_right (Nat.le_of_not_gt earlier), ← List.length_append] at localPC
                  <;> simp only [position, List.length_append, Nat.sub_self, List.getElem?_cons_zero,
                    Option.some.injEq, Befehl.pruefeMass.injEq] at localPC
                exact localPC.symm
              refine ⟨name, ⟨⟨_, _, body⟩, some m⟩, m, [header],
                ((bracedBlock body).code ++ [.rueckVoid]) ++ (unitBody rest).code,
                List.mem_cons_self, rfl, ?_, position, zeroSlot⟩
              simp only [unitBody, Fragment.anhaengen, layout, List.append_assoc]
        · rw [List.getElem?_append_right (Nat.le_of_not_gt prolog)] at localPC
          exact False.elim (restFree.not_at localPC)
      | constant _ _ _ _ value _ _ =>
        exact False.elim ((OhneMass.append (expr_ohneMass 0 value)
          (.single (fun _ same => by cases same))).not_at localPC)
      | record | tagged | table | effectGroup | environment =>
        exact False.elim ((OhneMass.single (fun _ same => by cases same)).not_at localPC)
    · have outside := Nat.le_of_not_gt inside
      change ((decl first).code ++ (unitBody rest).code)[pc]? = _ at atPC
      rw [List.getElem?_append_right outside] at atPC
      obtain ⟨name, kern, m, pre, post, mem, declared, layout, position, zeroSlot⟩ := ih atPC
      refine ⟨name, kern, m, (decl first).code ++ pre, post, ?_, declared, ?_, ?_, zeroSlot⟩
      · cases first <;> first | exact List.mem_cons_of_mem _ mem | exact mem
      · simp only [unitBody, Fragment.anhaengen, layout, List.append_assoc]
      · simp only [List.length_append]
        omega

/-- A measure head in the installed code occupies the final instruction of an
    actual source declaration's measure prologue. The address singles out the
    occurrence even if different declarations emit the same instruction. -/
theorem programm_pruefeMass_herkunft {u : Ast.Unit} {pc slot : Nat}
    (atPC : (programm u).code[pc]? = some (.pruefeMass slot)) :
    ∃ (name : Identifier) (kern : FunktionsKern) (m : Measure kern.koerper.1)
      (pre post : List Befehl),
      name ∈ alleFunktionen u.2 ∧ kern.mass = some m ∧
      (programm u).code = pre ++ (measurePrologue (some m)).code ++ post ∧
      pc = pre.length + (expr 0 m.expression).code.length ∧ slot = 0 := by
  change (((unitBody u.2).code ++ [.starte mainName]) ++ [.ende])[pc]? = _ at atPC
  rw [List.append_assoc] at atPC
  by_cases within : pc < (unitBody u.2).code.length
  · rw [List.getElem?_append_left within] at atPC
    obtain ⟨name, kern, m, pre, post, mem, declared, layout, position, zeroSlot⟩ := mass_imRumpf u.2 atPC
    refine ⟨name, kern, m, pre, post ++ [.starte mainName, .ende], mem, declared, ?_, position, zeroSlot⟩
    simp only [programm, Fragment.anhaengen, Fragment.einzel, layout, List.append_assoc,
      List.singleton_append]
  · rw [List.getElem?_append_right (Nat.le_of_not_gt within)] at atPC
    have free : OhneMass ([.starte mainName] ++ [.ende]) :=
      .append (.single (fun _ h => by cases h)) (.single (fun _ h => by cases h))
    exact False.elim (free.not_at atPC)

end Gabbro.Core.Beobachtung
