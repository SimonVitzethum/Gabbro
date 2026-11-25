module

public import Core.Linken.Modul
public import Core.Annahme.Annahme
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- A fragment from a plain instruction list: no clauses, empty scope, no entries, no memory. -/
def codeFrag (code : List Befehl) : Fragment :=
  ⟨code, .leer, [], fun _ => none, .leer⟩

theorem codeFrag_code (code : List Befehl) : (codeFrag code).code = code :=
  rfl

theorem codeFrag_klauseln (code : List Befehl) : (codeFrag code).klauseln = .leer :=
  rfl

/-- Part A: straight-line code dividing 10 by 2. -/
def fragA : Fragment :=
  codeFrag [.literal 0 10, .literal 1 2, .teilen 0]

/-- Part B: straight-line code with a back jump to its own start. -/
def fragB : Fragment :=
  codeFrag [.literal 0 5, .literal 1 0, .zurueckSprung 3]

theorem fragA_code : fragA.code = [.literal 0 10, .literal 1 2, .teilen 0] :=
  rfl

theorem fragB_code : fragB.code = [.literal 0 5, .literal 1 0, .zurueckSprung 3] :=
  rfl

/-- The two modules carry no interface: the point is control flow, not calls. -/
def modulA : Modul :=
  { name := "a", fragment := fragA, exporte := [], importe := [] }

def modulB : Modul :=
  { name := "b", fragment := fragB, exporte := [], importe := [] }

/-- The witness plan: A linked before B, entry at A. -/
def planAB : Bauplan :=
  { module := [modulA, modulB], abhaengigkeiten := [], plattform := .x86_64, einstieg := "a" }

/-- The current link check accepts the witness plan. -/
theorem planAB_ok : bauplanOk planAB = true := by
  decide

/-- The linked code is the concatenation: the divider runs with B's divisor. -/
theorem planAB_code : (verknuepfteFragmente planAB).code =
    [.literal 0 10, .literal 1 2, .teilen 0, .literal 0 5, .literal 1 0, .zurueckSprung 3] := by
  rfl

/-- Linking the witness plan succeeds under the current check. -/
theorem planAB_linke : linke planAB = some (verknuepfteFragmente planAB) := by
  unfold linke
  rw [if_pos planAB_ok]

/-- Every instruction of B is guard-free. -/
theorem fragB_guard (b : Befehl) (present : b ∈ fragB.code) (frame : Rahmen) :
    b.guard frame = none := by
  rw [fragB_code] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

/-- Part B alone is accepted: guard-free with empty clauses. -/
theorem fragB_akzeptiert : Akzeptiert (fragB.einheit .x86_64) :=
  Fragment.akzeptiert_ohne_bedarf fragB _ (codeFrag_klauseln _) (fun b present frame => fragB_guard b present frame)

/-- The exact value `literal 1 2` writes to its slot. -/
def zweiWert : Dynamisch :=
  ⟨.int ((2 : Nat) : Int) ((2 : Nat) : Int), Zahl.literal ((2 : Nat) : Int)⟩

/-- Slot 1 only ever holds nothing or the literal 2. -/
def temp1Sauber (frame : Rahmen) : Prop :=
  frame.temp 1 = none ∨ frame.temp 1 = some zweiWert

/-- A `teilen` guard use determines its dividend, its divisor and the operands. -/
theorem teilen_guard_form {l : Nat} {frame : Rahmen} {p : (op : PartielleOperation) × Operanden op}
    (h : (Befehl.teilen l).guard frame = some p) :
    ∃ a b, frame.zahl l = some a ∧ frame.zahl (l + 1) = some b ∧
      p = ⟨.division, (a.zahl.wert.natAbs, b.zahl.wert.natAbs)⟩ := by
  dsimp only [Befehl.guard] at h
  obtain ⟨a, ha⟩ : ∃ a, frame.zahl l = some a := by
    cases hz : frame.zahl l with
    | none =>
      rw [hz] at h
      cases h
    | some _ => exact ⟨_, rfl⟩
  rw [ha] at h
  dsimp only at h
  obtain ⟨b, hb⟩ : ∃ b, frame.zahl (l + 1) = some b := by
    cases hz : frame.zahl (l + 1) with
    | none =>
      rw [hz] at h
      cases h
    | some _ => exact ⟨_, rfl⟩
  rw [hb] at h
  dsimp only at h
  cases h
  exact ⟨a, b, ha, hb, rfl⟩

/-- Every instruction of A preserves a clean slot 1 at the acting context. -/
theorem nach_temp1 {b : Befehl} {c : Kontext} {s : Zustand}
    (hb : b ∈ fragA.code) (h : temp1Sauber (s.lokal c)) :
    temp1Sauber ((b.nach c s).lokal c) := by
  rw [fragA_code] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · simp only [Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self,
      temp1Sauber]
    rw [Function.update_of_ne (by decide : (1 : Nat) ≠ 0)]
    exact h
  · simp only [Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self,
      temp1Sauber]
    exact Or.inr rfl
  · simp only [Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self,
      temp1Sauber]
    rw [Function.update_of_ne (by decide : (1 : Nat) ≠ 0)]
    exact h

/-- A step of A preserves a clean slot 1 in every context. -/
theorem schritt_temp1 {c : Kontext} {s u : Zustand} {w : PUnit.{1}}
    {plans : List Plan} (h : ∀ d, temp1Sauber (s.lokal d))
    (step : (fragA.einheit .x86_64).system.ISchritt c s w plans u) :
    ∀ d, temp1Sauber (u.lokal d) := by
  obtain ⟨b, head, ideal⟩ := step
  obtain ⟨same, after⟩ := (b.ideal_privat c s w plans u).1 ideal
  subst after
  have hpc : fragA.code[(s.lokal c).pc]? = some b := kopf_code head
  have hlen : (s.lokal c).pc < 3 := by
    by_contra hle
    push_neg at hle
    have h3 : fragA.code.length = 3 := by rw [fragA_code]
    have hnone : fragA.code[(s.lokal c).pc]? = none :=
      List.getElem?_eq_none (by omega)
    rw [hnone] at hpc
    cases hpc
  revert hpc hlen
  generalize (s.lokal c).pc = pc
  intro hpc hlen
  match hmpc : pc with
  | 0 =>
    have h0 : fragA.code[0]? = some (Befehl.literal 0 10) := rfl
    rw [hpc] at h0
    cases h0
    intro d
    by_cases heq : d = c
    · subst heq
      exact nach_temp1 (by simp [fragA_code]) (h c)
    · have hkeep : ((Befehl.literal 0 10).nach c s).lokal d = s.lokal d :=
        Function.update_of_ne heq _ _
      rw [hkeep]
      exact h d
  | 1 =>
    have h1 : fragA.code[1]? = some (Befehl.literal 1 2) := rfl
    rw [hpc] at h1
    cases h1
    intro d
    by_cases heq : d = c
    · subst heq
      exact nach_temp1 (by simp [fragA_code]) (h c)
    · have hkeep : ((Befehl.literal 1 2).nach c s).lokal d = s.lokal d :=
        Function.update_of_ne heq _ _
      rw [hkeep]
      exact h d
  | 2 =>
    have h2 : fragA.code[2]? = some (Befehl.teilen 0) := rfl
    rw [hpc] at h2
    cases h2
    intro d
    by_cases heq : d = c
    · subst heq
      exact nach_temp1 (by simp [fragA_code]) (h c)
    · have hkeep : ((Befehl.teilen 0).nach c s).lokal d = s.lokal d :=
        Function.update_of_ne heq _ _
      rw [hkeep]
      exact h d
  | n + 3 => omega
/-- Slot 1 is clean in every start frame of A. -/
theorem start_temp1 (s : AussenStart) (c : Kontext) :
    temp1Sauber ((((fragA.einheit .x86_64).startdaten s).lokal c)) := by
  exact Or.inl rfl

/-- Slot 1 stays clean along any ideal run of A: only `literal 1 2` writes it,
    interrupts and answers leave frames untouched, and a crash restarts from fresh frames. -/
theorem lauf_temp1 (ρ : I.Lauf (fragA.einheit .x86_64))
    (hρ : I.Laeufe _ ρ) (t : Nat) : ∀ c, temp1Sauber ((ρ.zeit.zustand t).lokal c) := by
  induction t with
  | zero =>
    intro c
    have h0 : ρ.zeit.zustand 0 = (I.start _ ρ.start).2 := hρ.2.2.2.1
    rw [h0]
    exact start_temp1 _ c
  | succ t ih =>
    intro c
    cases htakt : ρ.zeit.takt t with
    | schritt label step =>
      cases step with
      | kontext _ bereit regel aus =>
        have hall := schritt_temp1 (fun d => ih d) regel
        obtain ⟨b, head, ideal⟩ := regel
        obtain ⟨same, after⟩ := (b.ideal_privat _ _ _ _ _).1 ideal
        have hplan := (List.cons.inj same).1
        rw [after] at hall aus
        rw [hplan] at aus
        have hakt : Semantik.plan.aktion = .intern := rfl
        obtain ⟨rahmen, _, _, _, fuehrt, _, hstate⟩ := aus
        rw [hakt] at fuehrt
        cases fuehrt with
        | intern =>
          rw [hstate]
          exact hall c
      | antwort _ reply =>
        obtain ⟨_, _, _, hstate⟩ := reply
        rw [hstate]
        exact ih c
      | interrupt _ enters =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hstate⟩ := enters
        rw [hstate]
        exact ih c
      | absturz crash =>
        obtain ⟨_, _, p, _, hstate⟩ := crash
        rw [hstate]
        exact Or.inl rfl
    | wartet label eq hp =>
      rw [eq]
      exact ih c

/-- Every guard use on any run of A holds: at `teilen` the divisor slot is the literal 2. -/
theorem fragA_guard_hält (ρ : I.Lauf (fragA.einheit .x86_64))
    (hρ : I.Laeufe _ ρ) (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op)
    (need : (kanonischeVerwendung _).bedarf ρ t op args) : waechterBedarf op args := by
  obtain ⟨c, b, head, gdef⟩ := need
  have hpc : fragA.code[((ρ.zeit.zustand t.val).lokal c).pc]? = some b := kopf_code head
  have hmem : b ∈ fragA.code := List.mem_of_getElem? hpc
  rw [fragA_code] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · simp only [Befehl.guard] at gdef
    cases gdef
  · simp only [Befehl.guard] at gdef
    cases gdef
  · obtain ⟨a, g₂, ha, hb, hsig⟩ := teilen_guard_form gdef
    cases hsig
    have hclean := lauf_temp1 ρ hρ t.val c
    have htemp : ((ρ.zeit.zustand t.val).lokal c).temp 1 = some zweiWert := by
      have hbind : ((((ρ.zeit.zustand t.val).lokal c).temp 1).bind alsGanzzahl) = some g₂ := hb
      rcases hclean with hnone | hsome
      · rw [hnone] at hbind
        cases hbind
      · exact hsome
    have hzahl : Rahmen.zahl ((ρ.zeit.zustand t.val).lokal c) 1 =
        some ⟨((2 : Nat) : Int), ((2 : Nat) : Int), Zahl.literal ((2 : Nat) : Int)⟩ := by
      have e : ((((ρ.zeit.zustand t.val).lokal c).temp 1).bind alsGanzzahl) =
          some ⟨((2 : Nat) : Int), ((2 : Nat) : Int), Zahl.literal ((2 : Nat) : Int)⟩ := by
        rw [htemp]
        rfl
      exact e
    rw [hb] at hzahl
    cases hzahl
    show (2 : Nat) ≠ 0
    decide

/-- Part A alone is accepted: straight-line code with divisor 2. -/
theorem fragA_akzeptiert : Akzeptiert (fragA.einheit .x86_64) := by
  let E := fragA.einheit .x86_64
  have hklauseln : fragA.klauseln = .leer := codeFrag_klauseln _
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, fun b => b.lokal E rfl,
    ⟨Aussen.zulassung_m2 _, ?_⟩, Beobachtung.fragment_fluss_lokal fragA .x86_64, ?_⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, _, transfer⟩ := rule
      obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) transfer execute
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · exact schrankenLokal_leer rfl rfl rfl
  · intro run conforms
    change (∀ pred ∈ fragA.klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ fragA.klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ fragA.klauseln.sicher, _
    rw [hklauseln]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t op args need
      exact fragA_guard_hält run conforms t op args need
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

end Gabbro.Core.Linken
