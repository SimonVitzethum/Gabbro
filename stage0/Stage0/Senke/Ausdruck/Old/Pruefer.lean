module
public import Stage0.Senke.Ausdruck.Old.Source
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.UebersetzeAllg3.Guest.Export
public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Bausteine.Kernzelle.Start
public import Grammatik.Zielsatz.Kern.Akzeptiert.Guest
@[expose] public section


namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- Substring test without recursion: some window of the haystack of the
    needle's length equals the needle. -/
def enthaelt (nadel hay : String) : Bool :=
  let n := nadel.toList
  let h := hay.toList
  (List.range (h.length + 1)).any fun i => decide ((h.drop i).take n.length = n)

/-- The remaining export restriction covers arena tables and accumulator
    storage. Declared checks already have a production exporter. -/
def zertifizierbar (u : UProg) : Bool :=
  (u.tabs.all fun t => !t.arena) &&
    (u.globs.all fun g => !enthaelt "#zelle" g.name) &&
    (u.locks.all fun l => !enthaelt "#sperre" l.name)

/-- The three conjuncts of the remaining export restriction. -/
theorem zertifizierbar_teile {u : UProg} (h : zertifizierbar u = true) :
    (u.tabs.all fun t => !t.arena) = true ∧
      (u.globs.all fun g => !enthaelt "#zelle" g.name) = true ∧
      (u.locks.all fun l => !enthaelt "#sperre" l.name) = true := by
  have h1 := (Bool.and_eq_true _ _).mp h
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  exact ⟨h2.1, h2.2, h1.2⟩

/-- A certifiable unit has no arena table. -/
theorem zertifizierbar_ohne_arena (u : UProg) (h : zertifizierbar u = true)
    (t : UTab) (hm : t ∈ u.tabs) : t.arena = false := by
  have h1 : (!t.arena) = true := (List.all_eq_true.mp (zertifizierbar_teile h).1) t hm
  cases ht : t.arena with
  | true =>
    rw [ht, Bool.not_true] at h1
    cases h1
  | false => rfl

/-- A certifiable unit carries no accumulator storage. -/
theorem zertifizierbar_ohne_akku (u : UProg) (h : zertifizierbar u = true) :
    (u.globs.all fun g => !enthaelt "#zelle" g.name) = true ∧
      (u.locks.all fun l => !enthaelt "#sperre" l.name) = true :=
  (zertifizierbar_teile h).2

/-- The exported program, locks, start environments and declared check
    descriptors, with the remaining ownership interfaces empty. -/
def einheitVon (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) : Einheit (declOf u) :=
  { P := P, S := sperrFamilie u, Q := Q, starts := starts, sp0 := sp,
    gestartet := gestartet, arenen := [], akku := [], pruefungen := checks,
    lockFormulas := sperrQuellen u, axiomSources := leereAxQuellen u Q,
    pointerSignatures := some (zeigerSignaturen u), measure := massVon u }

/-- `AkzeptiertX` does not depend on the chosen equality procedures
    (`bindetAxE_inst` for the same fact about the binding observation). -/
theorem akzeptiertX_inst (D : Deklaration) (fnEq₁ fnEq₂ : DecidableEq D.Fn)
    (axEq₁ axEq₂ : DecidableEq D.Ax) (P : Programm D) (S : SperrInv D)
    (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (aks : List (Kernzelle.AccumulatorDecl D))
    (checks : List (CheckDecl D)) (aqs : List D.Ax) (guests : List (GuestBoundary D))
    (sources : Invarianten.Pruefer.LockSources S := fun _ => none)
    (hints : Vertraege.Pruefer.LoopHints D := fun _ => none)
    (pointers : Option (Vertraege.Pruefer.PointerSignatures D) := none) :
    @AkzeptiertX D fnEq₁ axEq₁ P S fs ls cs ws aks checks aqs guests sources hints pointers =
      @AkzeptiertX D fnEq₂ axEq₂ P S fs ls cs ws aks checks aqs guests sources hints pointers := by
  cases Subsingleton.elim fnEq₁ fnEq₂
  cases Subsingleton.elim axEq₁ axEq₂
  rfl

/-- The production checker proves the model's program judgment with the
    exact function, lock, carrier and root enumerations. Guest admission
    is a separate proved conjunct. -/
theorem accepts_program (u : UProg) (P : Programm (declOf u)) (main : (declOf u).Fn)
    (accepted : accepts u P main = .ok true) {checks : List (CheckDecl (declOf u))}
    (derived : uCheckDecls u = .ok checks) :
    @AkzeptiertX (declOf u) (inferInstanceAs (DecidableEq (Fin u.fns.length)))
      (inferInstanceAs (DecidableEq (Fin u.axs.length))) P (sperrFamilie u)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr)
      (judgedRoots u main) [] checks [] [] (sperrQuellen u) (fun _ => none)
      (some (zeigerSignaturen u)) = true := by
  obtain ⟨guests, actual, _, exported, checked⟩ := accepts_core u P main accepted
  cases Except.ok.inj (exported.symm.trans derived)
  have split := (@akzeptiertX_guest_eq (declOf u)
    (inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (inferInstanceAs (DecidableEq (Fin u.axs.length))) P (sperrFamilie u)
    _ _ _ _ _ _ _ guests (sperrQuellen u) (fun _ => none) (some (zeigerSignaturen u))).symm.trans checked
  exact (Bool.and_eq_true_iff.mp split).1

/-- Soundness of the actual checker on the program it judges. The empty
    arena and accumulator lists are those used by `accepts`. -/
theorem accepts_program_spec [RootNativeFloat.Hardware] (u : UProg) (P : Programm (declOf u))
    (main : (declOf u).Fn) (accepted : accepts u P main = .ok true) :
    AkzeptiertSpecX P (sperrFamilie u) (List.finRange u.fns.length) (judgedRoots u main) [] [] := by
  letI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  letI : DecidableEq (declOf u).Ax := inferInstanceAs (DecidableEq (Fin u.axs.length))
  obtain ⟨_, _, _, derived, _⟩ := accepts_core u P main accepted
  refine akzeptiertSpecX_of List.mem_finRange List.mem_finRange ?_ [] (accepts_program u P main accepted derived)
  intro carrier
  cases carrier with
  | inl table => exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange table))
  | inr global => exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange global))

/-- Lift the production verdict on the declared checks to the goal
    checker on the same roots and the checked initial state. -/
theorem accepts_gibt_einheitVon (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) (derived : uCheckDecls u = .ok checks)
    (hFn : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (hws : (starts ++ gestartet ++ gestartet).map (·.1) = judgedRoots u main)
    (h : accepts u P main = .ok true)
    (hStart : unitStartGeprueftB (einheitVon u P Q sp starts gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length) = true) :
    akzeptiertX_pruefer.akzeptiert (einheitVon u P Q sp starts gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true := by
  have hX : @AkzeptiertX (declOf u) hFn (fun x y => Classical.propDecidable (x = y)) P
      (sperrFamilie u) (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr)
      (einheitVon u P Q sp starts gestartet checks).ws [] checks [] [] (sperrQuellen u) (fun _ => none)
      (some (zeigerSignaturen u)) = true := by
    have roots : (einheitVon u P Q sp starts gestartet checks).ws = judgedRoots u main := hws
    rw [roots]
    exact (akzeptiertX_inst (declOf u) _ hFn _ (fun x y => Classical.propDecidable (x = y))
      P (sperrFamilie u) _ _ _ _ _ _ _ _ (sperrQuellen u) (fun _ => none)
      (some (zeigerSignaturen u))).symm.trans (accepts_program u P main h derived)
  have hB : besitzB (einheitVon u P Q sp starts gestartet checks)
      (List.finRange u.fns.length) = true :=
    besitzB_leer rfl
  have hA : Kernzelle.akkuStartB (einheitVon u P Q sp starts gestartet checks)
      (einheitVon u P Q sp starts gestartet checks).akku = true :=
    Kernzelle.akkuStartB_leer (einheitVon u P Q sp starts gestartet checks)
  have starts := Bool.and_eq_true_iff.mp hStart
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hX, hB⟩, hA⟩, starts.1⟩, starts.2⟩

/-- After source metadata is admitted, the core checker and the actual start
    gate together give exactly the goal checker's verdict on the exported unit. -/
theorem accepts_einheitVon_iff (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) (derived : uCheckDecls u = .ok checks)
    (hws : (starts ++ gestartet ++ gestartet).map (·.1) = judgedRoots u main)
    (inv : sperrInvsOk u = true) {guests : List (GuestBoundary (declOf u))}
    (exported : sourceGuests u = .ok guests) (guest : GuestBoundary.admissionB guests = true) :
    (accepts u P main = .ok true ∧ unitStartGeprueftB (einheitVon u P Q sp starts gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length) = true) ↔
    akzeptiertX_pruefer.akzeptiert (einheitVon u P Q sp starts gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true := by
  constructor
  · rintro ⟨accepted, start⟩
    exact accepts_gibt_einheitVon u P Q sp main starts gestartet checks derived _ hws accepted start
  · intro accepted
    simp only [akzeptiertX_pruefer, Bool.and_eq_true] at accepted
    rcases accepted with ⟨⟨⟨⟨core, _⟩, _⟩, invariant⟩, logic⟩
    refine ⟨?_, Bool.and_eq_true_iff.mpr ⟨invariant, logic⟩⟩
    simp only [accepts, inv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, exported, derived, bind, Except.bind]
    apply (Vertraege.Pruefer.contractVerdict_true_iff _ _ _ _ _).mpr
    refine (@akzeptiertX_guest_eq (declOf u)
      (inferInstanceAs (DecidableEq (Fin u.fns.length)))
      (inferInstanceAs (DecidableEq (Fin u.axs.length)))
      P (sperrFamilie u) _ _ _ _ _ _ _ guests (sperrQuellen u) (fun _ => none)
      (some (zeigerSignaturen u))).trans (Bool.and_eq_true_iff.mpr ⟨?_, guest⟩)
    rw [← hws]
    exact (akzeptiertX_inst (declOf u) _ _ _ (fun x y => Classical.propDecidable (x = y))
      P (sperrFamilie u) _ _ _ _ _ _ _ _ (sperrQuellen u) (fun _ => none)
      (some (zeigerSignaturen u))).trans core

end Gabbro.Stage0.OldSource
