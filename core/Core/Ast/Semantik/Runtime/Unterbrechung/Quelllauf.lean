module

public import Core.Ast.Semantik.Runtime.Unterbrechung.Quellhandler
public import Core.Fortschritt.Verdraengung
import Core.Ast.Semantik.Runtime.Faden.Beweise.Komponierbar
import Core.Beobachtung.Fluss.Fragment

public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog LowLevel Fortschritt

/-- Prepend one chosen transition to a maximal continuation. -/
private def prepend {S Ev : Type} {step : Nat → S → Ev → S → Prop} {s : S} {event : Ev}
    (tail : Zeitlauf (fun t => step (t + 1)))
    (first : step 0 s event (tail.zustand 0)) : Zeitlauf step where
  zustand
    | 0 => s
    | t + 1 => tail.zustand t
  spur
    | 0 => some event
    | t + 1 => tail.spur t
  takt
    | 0 => .schritt rfl first
    | t + 1 => by
      cases tail.takt t with
      | schritt label move => exact .schritt label move
      | wartet label eq pause => exact .wartet label eq pause

/-- A source entry bound to vector zero is delivered, evaluates its result, terminates
    and restores the displaced context. That context takes its own source step at the
    next opportunity in the same admitted implementation run. -/
theorem quellhandler_rueckkehr_erfuellbar :
    let entry := ExecTree.entryDecl mainName .interrupt .perCore (some 0)
    let scope : ExecScope := ⟨[], [], [], [], [mainName]⟩
    let vectorFor := fun name : Identifier => if name.val = mainName.val then some 0 else none
    ∃ p, interruptHandler .x86_64 scope vectorFor entry (.lit 7) (.lit 1) = some p ∧
      let E := p.einheit .x86_64
      ∃ ρ : Lauf E, Laeufe E HV ρ ∧ FairLaeufe E.katalog HV ρ.hw ∧
        (ρ.zeit.spur 0).map Prod.fst = some (.interrupt (0, 0)) ∧
        (ρ.zeit.spur 1).map Prod.fst = some (.kontext Hv ()) ∧
        (ρ.zeit.spur 2).map Prod.fst = some (.kontext Hv ()) ∧
        (ρ.zeit.spur 3).map Prod.fst = some (.kontext eintritt ()) ∧
        ∃ z entered ready returned resumed,
          ρ.zeit.zustand 0 = some z ∧ ρ.zeit.zustand 1 = some entered ∧
          ρ.zeit.zustand 2 = some ready ∧ ρ.zeit.zustand 3 = some returned ∧
          ρ.zeit.zustand 4 = some resumed ∧
          (z.kerne 0).laeuft = some eintritt ∧ (entered.kerne 0).laeuft = some Hv ∧
          E.system.kopf entered Hv = some (.literal 0 7) ∧
          E.system.kopf ready Hv = some (.faden (.beende 0)) ∧
          returned.status Hv = .beendet (.wert 7) ∧
          (returned.kerne 0).laeuft = (z.kerne 0).laeuft ∧
          (returned.kerne 0).stapel = (z.kerne 0).stapel ∧
          returned.lokal eintritt = z.lokal eintritt ∧
          (resumed.lokal eintritt).pc = (z.lokal eintritt).pc + 1 := by
  intro entry scope vectorFor
  let p := ((expr 0 (.lit 1 : Expr [] (.int 1 1))).anhaengen (.einzel .ende)).anhaengen
    (((expr 0 (.lit 7 : Expr [] (.int 7 7))).anhaengen (.einzel (.faden (.beende 0)))).rumpf
      fun c => match c with
        | .handler _ line _ => decide (line = 0)
        | _ => false)
  refine ⟨p, ?_, ?_⟩
  · have slot : List.idxOf? mainName.val [mainName.val] = some 0 := by
      simp only [List.idxOf?_cons, beq_self_eq_true, if_true]
    simp only [interruptHandler, elaborateExec, entry, scope, List.map_cons, List.map_nil, slot,
      Option.map_some, Option.bind_some, vectorFor, if_pos rfl]
    rfl
  let E := p.einheit .x86_64
  have image : E.bild.gueltig E.katalog.plattform.ziel := by
    rcases ziele_gut Plattform.x86_64 with ⟨_, _, _, _, _, _, _, _, _, elf⟩
    refine ⟨elf, ?_, ?_⟩
    · intro a byte present
      change (if a = 0 then some 0 else none) = some byte at present
      split at present
      · subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases present
    · intro a mem
      have eq : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  obtain ⟨start, zul⟩ := zulStart_erfuellbar (bild := E.bild) fairV.hardware image
  obtain ⟨kern, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ 0)
  have kernZero : kern = 0 := by
    have bound := (zul.2.2.2.1 0 kern assigned).2
    rw [HV1] at bound
    omega
  subst kern
  let z := (I.start E start).2
  have loaded : E.laden start (HV.lade E.bild) = some z :=
    Beobachtung.fragment_geladen p .x86_64 fairV.hardware zul
  have dispatch : (z.kerne 0).laeuft = some eintritt := by
    change (if some 0 = start.assignment 0 then some eintritt else none) = _
    rw [assigned, if_pos rfl]
  let event := Ereignis.interrupt 0 irqV .handler
  let label := aussenEtikett E.einrichtung event
  obtain ⟨graph, append⟩ := Speicher.Zustand.schritt_ohne_lesen
    (Z := z.graph) Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    .aussen label (fun h => nomatch h)
  let entered := { Zustandseintritt z 0 (0, 0) Hv false with graph := graph }
  let ingress : SchrittSpur Zelle Int := ⟨[(.aussen, label)], [event]⟩
  have delivery : Lauffolge E hwV 0 (some z) (.interrupt (0, 0), ingress) (some entered) :=
    .schritt (.interrupt rfl ⟨0, irqV, Hv, false, rfl,
      ⟨Nat.le_refl _, Nat.le_refl _, pendingV0, List.not_mem_nil, auswahlV0⟩,
      NimmtUnterbrechung.handler_bei ⟨rfl, rfl⟩ (Nat.le_refl _), rfl, rfl,
      .cons (.ohne (Or.inl rfl)) append (.nil _), rfl⟩)
  let write : Befehl := .literal 0 7
  let ready := write.nach Hv entered
  have writeHead : E.system.kopf entered Hv = some write :=
    (handler_beginnt_im_rumpf p .x86_64 start 0 (0, 0) Hv false
      (fun h => Kontext.noConfusion h) (pos := 2) rfl).trans rfl
  have enteredDispatch : (entered.kerne 0).laeuft = some Hv := by
    simp only [entered, Zustandseintritt, Function.update_self, KernZustand.unterbrechen]
  have enteredLive : entered.status Hv = .laeuft := by
    simp only [entered, Zustandseintritt, Function.update_self]
  have evaluate : Lauffolge E hwV 1 (some entered) (.kontext Hv (), ⟨[], []⟩) (some ready) :=
    .schritt (.kontext rfl ⟨0, rfl, enteredDispatch, enteredLive⟩ ⟨write, writeHead, rfl, rfl⟩
      (write.vollzug E.einrichtung 1 Hv entered (Or.inl rfl)))
  let finish : Befehl := .faden (.beende 0)
  let endPlan := finish.plan (ready.lokal Hv) 0
  let u := finish.form.faedenNach Hv ready
  have finishHead : E.system.kopf ready Hv = some finish := by
    exact kopf_laufend (code := p.code) (s := ready) (c := Hv)
      enteredLive
      (by simp only [ready, Befehl.nach, Function.update_self]; rfl)
      (by simp only [ready, Befehl.nach, Function.update_self]; rfl) |>.trans (by
        simp only [ready, Befehl.nach, Function.update_self]
        rfl)
  have rule : finish.ideal Hv ready () [endPlan] u := by
    change (_ ∨ (_ = true ∧ _ ∧ _))
    exact Or.inr ⟨by simp only [ready, Befehl.nach, Function.update_self]; rfl, rfl, rfl⟩
  let returned := Abschlussrueckkehr ready u Hv
  have ended : u.status Hv = .beendet (.wert 7) := by
    simp only [u, Schrittform.faedenNach, finish, Befehl.form, Befehl.klasse, Fadenform.klasse,
      ready, Befehl.nach, Function.update_self]
    rfl
  have frame : Zustandsrahmen ready u :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have execute : FuehrtSchrittAus E.einrichtung 2 Hv ready u endPlan ⟨[], []⟩ returned :=
    beendeVollzug E.einrichtung rule rfl ⟨_, ended⟩
  have terminate : Lauffolge E hwV 2 (some ready) (.kontext Hv (), ⟨[], []⟩) (some returned) :=
    .schritt (.kontext rfl ⟨0, rfl, enteredDispatch, enteredLive⟩ ⟨finish, finishHead, rule⟩ execute)
  have active : KehrtZurueck ready Hv 0 := .handler enteredDispatch (by
    simp only [ready, Befehl.nach, entered, Zustandseintritt, KernZustand.unterbrechen,
      Function.update_self]
    exact fun h => nomatch h)
  have restored : returned = Zustandsrueckkehr u 0 := active.abschluss frame.kerne
  have coreRestored : (returned.kerne 0).laeuft = (z.kerne 0).laeuft ∧
      (returned.kerne 0).stapel = (z.kerne 0).stapel := by
    rw [restored]
    exact rueckkehr_setzt_fort z 0 (0, 0) Hv false
  have different : eintritt ≠ Hv := fun h => Kontext.noConfusion h
  have localRestored : returned.lokal eintritt = z.lokal eintritt := by
    change Function.update ready.lokal Hv
      (finish.form.uebertrag (ready.lokal Hv) ready.regionLive 0) eintritt = z.lokal eintritt
    rw [Function.update_of_ne different]
    exact write.nach_lokal_anderer different entered
  have entryLive : returned.status eintritt = .laeuft := by
    change Function.update ready.status Hv (.beendet (.wert 7)) eintritt = .laeuft
    rw [Function.update_of_ne different]
    change Function.update z.status Hv .laeuft eintritt = .laeuft
    rw [Function.update_of_ne different]
    rfl
  let main : Befehl := .literal 0 1
  let resumed := main.nach eintritt returned
  have mainHead : E.system.kopf returned eintritt = some main :=
    (kopf_kontextgleich entryLive localRestored).trans (by rfl)
  have resume : Lauffolge E hwV 3 (some returned) (.kontext eintritt (), ⟨[], []⟩) (some resumed) :=
    .schritt (.kontext rfl ⟨0, rfl, coreRestored.1.trans dispatch, entryLive⟩
      ⟨main, mainHead, rfl, rfl⟩ (main.vollzug E.einrichtung 3 eintritt returned (Or.inl rfl)))
  obtain ⟨tail, initial⟩ := Zeitlauf.existiert (fun t => Lauffolge E hwV (t + 4)) (some resumed)
  let afterReturn := prepend (step := fun t => Lauffolge E hwV (t + 3)) tail (initial.symm ▸ resume)
  let afterWrite := prepend (step := fun t => Lauffolge E hwV (t + 2)) afterReturn terminate
  let afterDelivery := prepend (step := fun t => Lauffolge E hwV (t + 1)) afterWrite evaluate
  let run := prepend afterDelivery delivery
  refine ⟨⟨start, hwV, run⟩, ⟨fairV.hardware, fairV.konform, zul, loaded.symm⟩,
    fairV, rfl, rfl, rfl, rfl, z, entered, ready, returned, resumed,
    rfl, rfl, rfl, rfl, initial, dispatch, enteredDispatch, writeHead, finishHead,
    ended, coreRestored.1, coreRestored.2, localRestored, ?_⟩
  rw [Befehl.nach_lokal_eigener]
  change (returned.lokal eintritt).pc + 1 = _
  rw [localRestored]

end Gabbro.Core.Ast.Semantik
