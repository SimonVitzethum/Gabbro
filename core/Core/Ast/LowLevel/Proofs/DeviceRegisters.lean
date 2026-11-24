module

public import Core.Ast.LowLevel.Device
public import Core.Ast.LowLevel.DeviceSyntax

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Annahme Katalog Maschine

def RegisterBefugtAussage : Prop :=
  ∀ k (binding : Binding k) access required target c s plan next,
    Rule binding access required target c s plan next →
    Befugt binding required access s c ∧
      Sicherheit.RegisterErlaubt s c.nummer (binding.question access)

theorem register_befugt : RegisterBefugtAussage := by
  intro k binding access required target c s plan next step
  have owns : Befugt binding required access s c := by
    cases step with
    | issue owns _ | consume owns _ _ _ => exact owns
  exact ⟨owns, fun _ => ⟨c, rfl, owns.1⟩⟩

/-- The form uses the actual M5 local predicate at its composed issue and reply steps. -/
def RegisterAussenLokalAussage : Prop :=
  ∀ k (binding : Binding k) access required target
    (E : Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit)
    run t c s middle plan trace next,
    E.katalog = k →
    Rule binding access required target c s plan middle →
    FuehrtSchrittAus E.einrichtung t c s middle plan trace next →
    AussenKontextLokal E c run t s trace next ∧
      (OffeneGriffeEigen s → OffeneGriffeEigen next)

theorem register_aussenLokal : RegisterAussenLokalAussage := by
  intro k binding access required target E run t c s middle plan trace next catalogue step executes
  rcases trace with ⟨memory, events⟩
  obtain ⟨_, _, _, _, action, _, after⟩ := executes
  cases step with
  | issue owns _ =>
    cases action
    rw [after]
    refine ⟨⟨?_, [], (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, ?_⟩
    · intro ev mem
      cases Ereignis.frage.inj (List.mem_singleton.mp mem)
      rw [catalogue]
      exact ⟨binding.selected, owns.2.2.1⟩
    · intro outstanding asked mem epoch unanswered
      change asked ∈ s.fragen ++ [s.stelleFrage t c (binding.question access)] at mem
      rw [List.mem_append, List.mem_singleton] at mem
      rcases mem with previous | rfl
      · exact outstanding asked previous epoch unanswered
      · exact ⟨c, rfl, owns.2.2.1⟩
  | consume _ _ _ _ =>
    cases action
    rw [after]
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun outstanding => outstanding⟩

/-- A composed implementation step records its one device question and carries
    authority at that exact step. Answer consumption adds no second access. -/
def RegisterSafetyAussage : Prop :=
  ∀ k (binding : Binding k) access required target
    (setup : Einrichtung PUnit Nat UInt8 PUnit Frame PUnit PUnit)
    hw t c s middle plan trace next,
    Rule binding access required target c s plan middle →
    FuehrtSchrittAus setup t c s middle plan trace next →
    Sicherheit.RegisterImSchritt hw t s trace next

theorem register_safety : RegisterSafetyAussage := by
  intro k binding access required target setup hw t c s middle plan trace next step executes
  have authority := (register_befugt k binding access required target c s plan middle step).2
  rcases trace with ⟨memory, events⟩
  obtain ⟨_, _, _, _, action, _, after⟩ := executes
  cases step with
  | issue _ _ =>
    cases action
    rw [after]
    constructor
    · intro ev mem
      obtain rfl := List.mem_singleton.mp mem
      exact ⟨fun q same => by cases same; exact authority,
        fun _ commit => by cases commit.1⟩
    · refine ⟨[], Or.inr ⟨?_, (List.append_nil _).symm⟩, fun _ mem => (List.not_mem_nil mem).elim⟩
      intro crash
      change Ereignis.persistenz .crash ∈ [_] at crash
      cases List.mem_singleton.mp crash
  | consume _ _ _ _ =>
    cases action
    rw [after]
    exact ⟨fun _ mem => (List.not_mem_nil mem).elim,
      [], Or.inr ⟨List.not_mem_nil, (List.append_nil _).symm⟩, fun _ mem => (List.not_mem_nil mem).elim⟩

def RegisterCommitAussage : Prop :=
  ∀ k (binding : Binding k) access view answer,
    atomar k.plattform view (binding.question access) = .antwort answer →
    answer.result.isOk = true →
    Aussen.GueltigBeiCommit k.plattform view (binding.question access)

theorem register_commit : RegisterCommitAussage :=
  fun _ _ _ _ _ answer ok => Aussen.atomar_gueltig answer ok

def RegisterFallibleAussage : Prop :=
  (∀ offset range answer value,
    answer.result = .ok (.register value) →
    (RegisterAccess.fallibleRead offset range).result answer =
      if range.lower ≤ value ∧ value ≤ range.upper then .value value else .readOutOfRange value) ∧
  ∀ offset range answer failure,
    answer.result = .error failure →
    (RegisterAccess.fallibleRead offset range).result answer = .refused failure

theorem register_fallible : RegisterFallibleAussage := by
  constructor
  · intro offset range answer value reply
    simp only [RegisterAccess.result, reply]
  · intro offset range answer failure reply
    simp only [RegisterAccess.result, reply]

/-- The whole composed operation carries the actual M7 safety obligation,
    including the recorded question's authority at its issue cut. -/
def RegisterRegelSicherAussage (kind : RegisterAccess → Prop) : Prop :=
  ∀ k (binding : Binding k) access
    (E : Sicherheit.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit),
    kind access → E.invarianten = [] →
    E.maschine.system.regel () = registerRule binding access →
    Sicherheit.RegelSicher E ()

def RegisterReadAussage : Prop :=
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterCommitAussage ∧
  RegisterSafetyAussage ∧ RegisterRegelSicherAussage (fun access => ∃ offset, access = .read offset)

def RegisterWriteAussage : Prop :=
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterCommitAussage ∧
  RegisterSafetyAussage ∧ RegisterRegelSicherAussage (fun access => ∃ offset value, access = .write offset value)

def RegisterReadElseAussage : Prop :=
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterCommitAussage ∧
  RegisterSafetyAussage ∧ RegisterFallibleAussage ∧
  RegisterRegelSicherAussage (fun access => ∃ offset range, access = .fallibleRead offset range) ∧
  ∀ (k : Katalog) (scope : Scope) (d : Denotation k scope) destination binding offset promise handler,
    d = .fallibleRead destination binding offset promise handler →
    (∀ err, d.resume (.refused err) = .branch handler) ∧
    ∀ value, d.resume (.readOutOfRange value) = .branch handler

end Gabbro.Core.Ast.LowLevel.Device
