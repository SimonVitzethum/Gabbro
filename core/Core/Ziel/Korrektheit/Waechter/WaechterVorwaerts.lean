module

public import Core.Ziel.Korrektheit.Waechter.WaechterRahmen
public import Core.Ast.Semantik.Runtime.Mehrkontext.Kopf
public import Core.Ast.Semantik.Kernregister
public import Core.Ast.Semantik.Runtime.Walk

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast Gabbro.Core.Ast.Semantik Gabbro.Core.Maschine Gabbro.Core.Katalog

private theorem vorwaerts_privat {b : Befehl} (allowed : vorwaertsBefehl b = true) :
    b.Privat := by
  apply Befehl.privat_von_kein_zugriff <;> intro form eq <;> subst b <;> cases allowed

private theorem sprungweite_pos {distance : Nat} (allowed : decide (0 < distance) = true) :
    0 < distance := by
  cases distance with
  | zero => cases allowed
  | succ n => exact Nat.zero_lt_succ n

/-- Forward code installs no call targets. Every live post-state is at a larger position. -/
private theorem vorwaerts_auswerten (b : Befehl) (allowed : vorwaertsBefehl b = true)
    (r : Semantik.Rahmen) (live : Nat → Bool) (empty : r.funktionen = []) :
    let r' := b.auswerten r live
    r'.funktionen = [] ∧ (r'.stopp ≠ none ∨ r.pc < r'.pc) := by
  cases b <;>
    simp only [vorwaertsBefehl, prefixRein, istSteuerung, Bool.not_true, Bool.not_false,
      Bool.false_and, Bool.true_and] at allowed
  all_goals first
    | contradiction
    | exact ⟨empty, .inr (Nat.lt_succ_self _)⟩
    | skip
  case ende => exact ⟨empty, .inl (Option.some_ne_none _)⟩
  case springe distance =>
    exact ⟨empty, .inr (Nat.lt_add_of_pos_right (sprungweite_pos allowed))⟩
  case springeWenn source flag distance =>
    refine ⟨empty, .inr ?_⟩
    change r.pc < r.pc + (if (r.temp source).bind alsBoolean = some flag then distance else 1)
    split
    · exact Nat.lt_add_of_pos_right (sprungweite_pos allowed)
    · exact Nat.lt_succ_self _
  case starte name =>
    have halts : (Befehl.starte name).auswerten r live = r.halt (.ungueltigerRuf name) := by
      simp only [Befehl.auswerten, Id.run, empty, List.map_nil, List.nodup_nil, not_true_eq_false,
        if_false, List.find?_nil, List.flatMap_nil, Funktion.finde] <;> rfl
    rw [halts]
    exact ⟨empty, .inl (Option.some_ne_none _)⟩
  all_goals
    simp only [Befehl.auswerten, Id.run]
    repeat first
      | exact ⟨empty, .inr (Nat.lt_succ_self _)⟩
      | exact ⟨empty, .inl (Option.some_ne_none _)⟩
      | split

/-- An active frame below a cutoff has only executed writes before that cutoff.
    The invariant is usable with the current instruction position as the cutoff. -/
def VorwaertsRahmen (code : List Befehl) (r : Semantik.Rahmen) : Prop :=
  r.funktionen = [] ∧ ∀ cutoff, r.Aktiv → r.pc ≤ cutoff → RahmenErfuellt (code.take cutoff) r

private theorem vorwaertsRahmen_schritt {code : List Befehl} {b : Befehl}
    {r : Semantik.Rahmen} (live : Nat → Bool)
    (allowed : vorwaertsBefehl b = true) (safe : code.all keinFremdzugriff = true)
    (lookup : code[r.pc]? = some b) (active : r.Aktiv) (before : VorwaertsRahmen code r) :
    VorwaertsRahmen code (b.auswerten r live) := by
  obtain ⟨functions, stop | forward⟩ := vorwaerts_auswerten b allowed r live before.1
  · exact ⟨functions, fun _ active' _ => (stop active'.1).elim⟩
  refine ⟨functions, ?_⟩
  intro cutoff _ bound
  have lt := Nat.lt_of_lt_of_le forward bound
  have inPrefix : b ∈ code.take cutoff :=
    List.mem_of_getElem? ((List.getElem?_take_of_lt lt).trans lookup)
  have safePrefix : (code.take cutoff).all keinFremdzugriff = true :=
    List.all_eq_true.mpr fun b mem => List.all_eq_true.mp safe b (List.mem_of_mem_take mem)
  exact auswerten_erfuellt (code.take cutoff) r live b inPrefix safePrefix
    (before.2 cutoff active (Nat.le_of_lt lt))

theorem kopf_aktiv {code : List Befehl} {s : Semantik.Zustand} {c : Kontext} {b : Befehl}
    (head : kopf code s c = some b) : (s.lokal c).Aktiv := by
  simp only [kopf, kopf_laeuft head] at head
  split at head
  · rename_i returned
    split at head
    · rename_i running
      exact ⟨Option.isNone_iff_eq_none.mp running, returned⟩
    · cases head
  · cases head

/-- A frame invariant preserved by every reached private instruction survives all ideal cuts. -/
theorem privatRahmen_lauf (p : Fragment) (platform : Plattform)
    (holds : Semantik.Rahmen → Prop)
    (boot : ∀ k machine regions c,
      holds ((startdaten p.eingang p.eintritte k machine regions).lokal c))
    (preserve : ∀ b r live, p.code[r.pc]? = some b → r.Aktiv → holds r →
      b.Privat ∧ holds (b.auswerten r live))
    (ρ : I.Lauf (p.einheit platform)) (run : I.Laeufe _ ρ) (t : Nat) :
    ∀ c, holds ((ρ.zeit.zustand t).lokal c) := by
  induction t with
  | zero =>
      rw [run.2.2.2.1]
      intro c
      exact boot (ρ.start.assignment 0) platform ρ.start.regions c
  | succ t ih =>
      cases ρ.zeit.takt t with
      | wartet label eq _ =>
          rw [(ρ.zeit.wartet label).1]
          exact ih
      | schritt label step =>
          cases step with
          | kontext hkb hber rule execution =>
              rename_i u plan spur c w
              obtain ⟨b, head, ideal⟩ := rule
              have lookup := Gabbro.Core.Ast.Semantik.kopf_code head
              obtain ⟨privat, maintained⟩ :=
                preserve b _ _ lookup (kopf_aktiv head) (ih c)
              have hi : b.ideal c (ρ.zeit.zustand t) w [plan] u := ideal
              obtain ⟨plans, after⟩ := (b.ideal_privat privat c _ w [plan] u).1 hi
              have still : plan.aktion.Still := by
                rw [(List.cons.inj plans).1]
                exact (b.privat_still_leer privat _).1
              obtain ⟨_, _, _, v, exec, _, eq⟩ := execution
              obtain ⟨_, _, localEq, _, _⟩ := exec.still_erhaelt still
              rw [eq]
              intro d
              change holds (v.lokal d)
              rw [localEq, after]
              by_cases same : d = c
              · subst d
                rw [b.nach_lokal_eigener]
                exact maintained
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
              exact boot (some 0) .x86_64 [] c

/-- Prefix bounds hold at every ideal cut, including reboots and handler entries.
    New frames begin with no temporary values, regardless of their entry position. -/
theorem vorwaertsRahmen_lauf (p : Fragment) (platform : Plattform)
    (allowed : p.code.all vorwaertsBefehl = true) (safe : p.code.all keinFremdzugriff = true)
    (ρ : I.Lauf (p.einheit platform)) (run : I.Laeufe _ ρ) (t : Nat) :
    ∀ c, VorwaertsRahmen p.code ((ρ.zeit.zustand t).lokal c) := by
  apply privatRahmen_lauf p platform (VorwaertsRahmen p.code) _ _ ρ run t
  · intro k machine regions c
    exact ⟨rfl, fun _ _ _ => rahmenLeer_erfuellt _ _ rfl rfl⟩
  · intro b r live lookup active before
    have allowedB := List.all_eq_true.mp allowed b (List.mem_of_getElem? lookup)
    exact ⟨vorwaerts_privat allowedB, vorwaertsRahmen_schritt live allowedB safe lookup active before⟩

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
