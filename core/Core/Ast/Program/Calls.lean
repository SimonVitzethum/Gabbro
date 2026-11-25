module

public import Core.Ast.Semantik.ProgramForms
import Core.Ast.Semantik.Formbeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- One unit exercises both a discarded result and a typed result binding. -/
theorem callForms_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (call : DirectCall []) (binding : Surface.BindDirectArgs [] none),
      ((directCallForm [] none).ErfuellbarAm platform start call ∧
        LaufenderRuf platform start ((directCallForm [] none).befehl call)) ∧
      ((bindDirectForm [] none).ErfuellbarAm platform start binding ∧
        LaufenderRuf platform start ((bindDirectForm [] none).befehl binding)) := by
  let name : Identifier := keywordName 'f' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
  have ordinary : directName name := directName_of_singleton rfl
  have ordinaryMain : directName mainName := mainName_direct
  let call : DirectCall [] := ⟨name, ordinary, []⟩
  have notMutableKeyword : name.val ≠ "mut".toList := by
    change ['f'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let binding : Surface.BindDirectArgs [] none :=
    ⟨name, ⟨notMutableKeyword, ordinary.1⟩, .bool, trivial, call⟩
  let target : Decl [] [] := .function name ordinary [] (some .bool)
    (by intro t mem; have h : t = WrittenType.bool := List.mem_singleton.mp mem; subst t; trivial)
    none (.braces (.step (.ret rfl .trueLit trivial) .done)) List.nodup_nil (fun _ => rfl) none
  let main : Decl [] [] := .function mainName ordinaryMain [] none (by intro _ h; cases h)
    none (.braces (.step (.directCall call)
      (.step (.bindDirect binding.name binding.ordinary binding.written binding.valid binding.call) .done)))
    List.nodup_nil (by intro h; cases h) none
  let unit : Ast.Unit := ⟨[], .step target (.step main .done)⟩
  let E := elaborieren platform (category := .unit) unit
  let s₀ := (I.start E start).2
  let defTarget : Befehl := .definiere name [] (some .bool) 0 5 false [] none
  let defMain : Befehl := .definiere mainName [] none 0 5 false
    [⟨name, [], none, none⟩, ⟨name, [], some .bool, none⟩] none
  let launch : Befehl := .starte mainName
  let discard := (directCallForm [] none).befehl call
  let bind := (bindDirectForm [] none).befehl binding
  let truth : Befehl := .wahrheitswert 0 true
  let ret : Befehl := .zurueck 0 .bool
  let s₁ := defTarget.nach eintritt s₀
  let s₂ := defMain.nach eintritt s₁
  let s₃ := launch.nach eintritt s₂
  let s₄ := discard.nach eintritt s₃
  let s₅ := truth.nach eintritt s₄
  let s₆ := ret.nach eintritt s₅
  let code := [defTarget, truth, ret, .blockEnde 0, .rueckVoid,
    defMain, discard, bind, .blockEnde 1, .rueckVoid, launch, .ende]
  have compiled : (programm unit).code = code := rfl
  let f₀ := (startdaten [] (fun _ => none) (start.assignment 0) platform start.regions).lokal eintritt
  let f₁ := defTarget.auswerten f₀
  let f₂ := defMain.auswerten f₁
  let saved : Fortsetzung := ⟨11, f₂.temp, [], f₂.zaehler, f₂.obergrenzen, none, none, none⟩
  let f₃ : Rahmen := { f₂ with pc := 6, funktion := some mainName, fortsetzungen := [saved] }
  have launched : launch.auswerten f₂ = f₃ := by
    have unique : (f₂.funktionen.map (fun f => f.name.val)).Nodup := by
      change ([['m', 'a', 'i', 'n'], ['f']] : List (List Char)).Nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        and_true, not_false_eq_true, true_and]
      intro same
      cases same
    have measured : f₂.funktionen.find? (fun f =>
        !f.misstAbstieg && Funktion.rekursiv f₂.funktionen f) = none := rfl
    have checked : (f₂.funktionen.flatMap Funktion.ruft).find? (fun call =>
        !(call.passt f₂.funktionen)) = none := rfl
    simp only [launch, Befehl.auswerten, unique, not_true_eq_false, if_false, measured, checked]
    rfl
  let f₄ := discard.auswerten f₃
  let f₅ := truth.auswerten f₄
  let f₆ : Rahmen := { f₃ with pc := 7 }
  have returned : ret.auswerten f₅ = f₆ := rfl
  have nextFrame {s : Zustand} {b : Befehl} {before after : Rahmen}
      (localEq : s.lokal eintritt = before)
      (transfer : b.auswerten before s.regionLive = after) :
      (b.nach eintritt s).lokal eintritt = after := by
    simp only [Befehl.nach, Function.update_self, localEq, transfer]
  have local₀ : s₀.lokal eintritt = f₀ := rfl
  have local₁ : s₁.lokal eintritt = f₁ := nextFrame local₀ rfl
  have local₂ : s₂.lokal eintritt = f₂ := nextFrame local₁ rfl
  have local₃ : s₃.lokal eintritt = f₃ := nextFrame local₂ launched
  have local₄ : s₄.lokal eintritt = f₄ := nextFrame local₃ rfl
  have local₅ : s₅.lokal eintritt = f₅ := nextFrame local₄ rfl
  have local₆ : s₆.lokal eintritt = f₆ := nextFrame local₅ returned
  have atHead {s : Zustand} {f : Rahmen} {b : Befehl}
      (running : s.status eintritt = .laeuft) (localEq : s.lokal eintritt = f)
      (live : f.stopp = none) (active : f.rueckgabe = none)
      (lookup : code[f.pc]? = some b) : E.system.kopf s eintritt = some b := by
    change kopf (programm unit).code s eintritt = some b
    simp only [compiled, kopf, if_pos rfl, running, localEq, active, live, Option.isNone_none,
      if_true, lookup]
  have headTarget : E.system.kopf s₀ eintritt = some defTarget := atHead rfl local₀ rfl rfl rfl
  have headMain : E.system.kopf s₁ eintritt = some defMain := atHead rfl local₁ rfl rfl rfl
  have headLaunch : E.system.kopf s₂ eintritt = some launch := atHead rfl local₂ rfl rfl rfl
  have headDiscard : E.system.kopf s₃ eintritt = some discard := atHead rfl local₃ rfl rfl rfl
  have headTruth : E.system.kopf s₄ eintritt = some truth := atHead rfl local₄ rfl rfl rfl
  have headReturn : E.system.kopf s₅ eintritt = some ret := atHead rfl local₅ rfl rfl rfl
  have headBind : E.system.kopf s₆ eintritt = some bind := atHead rfl local₆ rfl rfl rfl
  have extend {s : Zustand} {b : Befehl} (reach : E.system.IErreichbar s₀ s)
      (head : E.system.kopf s eintritt = some b)
      (priv : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
      E.system.IErreichbar s₀ (b.nach eintritt s) :=
    .schritt eintritt () [plan] reach
      ⟨b, head, (b.ideal_privat priv eintritt s () [plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩
  have r₁ : E.system.IErreichbar s₀ s₁ := extend .start headTarget
  have r₂ : E.system.IErreichbar s₀ s₂ := extend r₁ headMain
  have r₃ : E.system.IErreichbar s₀ s₃ := extend r₂ headLaunch
  have r₄ : E.system.IErreichbar s₀ s₄ := extend r₃ headDiscard
  have r₅ : E.system.IErreichbar s₀ s₅ := extend r₄ headTruth
  have r₆ : E.system.IErreichbar s₀ s₆ := extend r₅ headReturn
  have runs {b : Befehl} {s : Zustand} (reach : E.system.IErreichbar s₀ s)
      (head : E.system.kopf s eintritt = some b) (live : ((b.nach eintritt s).lokal eintritt).stopp = none)
      (pushes : ((b.nach eintritt s).lokal eintritt).fortsetzungen.length =
        (s.lokal eintritt).fortsetzungen.length + 1)
      (priv : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) : LaufenderRuf platform start b :=
    ⟨unit, Ast.print (category := .unit) unit, s, Ast.parse_print _, reach, head,
      ⟨b, head, (b.ideal_privat priv eintritt s () [plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩,
      ⟨b, head, (b.impl_privat priv eintritt s () [plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩, live, pushes⟩
  have boundFrame : (bind.nach eintritt s₆).lokal eintritt = bind.auswerten f₆ := nextFrame local₆ rfl
  have discardLive : (s₄.lokal eintritt).stopp = none := by rw [local₄]; rfl
  have discardPushes : (s₄.lokal eintritt).fortsetzungen.length =
      (s₃.lokal eintritt).fortsetzungen.length + 1 := by rw [local₄, local₃]; rfl
  have bindLive : ((bind.nach eintritt s₆).lokal eintritt).stopp = none := by rw [boundFrame]; rfl
  have bindPushes : ((bind.nach eintritt s₆).lokal eintritt).fortsetzungen.length =
      (s₆.lokal eintritt).fortsetzungen.length + 1 := by rw [boundFrame, local₆]; rfl
  refine ⟨call, binding, ⟨?_, runs r₃ headDiscard discardLive discardPushes⟩,
    ⟨?_, runs r₆ headBind bindLive bindPushes⟩⟩
  · exact (directCallForm [] none).erfuellbar_aus_erreichbar platform start call _ .start
      ((directCallForm [] none).realisiert (fun args => by
        change ((argsCode 0 args.args).anhaengen (.einzel (callInstruction args none))).code[
          (argsCode 0 args.args).code.length]? = some (callInstruction args none)
        simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero])
        platform call _ rfl rfl rfl rfl) (by intro _ h; cases h)
  · exact (bindDirectForm [] none).erfuellbar_aus_erreichbar platform start binding _ .start
      ((bindDirectForm [] none).realisiert (fun args => by
        change ((argsCode 0 args.call.args).anhaengen
          (.einzel (callInstruction args.call (some args.written.type)))).code[
            (argsCode 0 args.call.args).code.length]? =
          some (callInstruction args.call (some args.written.type))
        simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero])
        platform binding _ rfl rfl rfl rfl) (by intro _ h; cases h)

end Gabbro.Core.Ast.Semantik
