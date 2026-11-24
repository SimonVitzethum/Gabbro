module

public import Core.Ast.LowLevel.Device
public import Core.Ast.LowLevel.DeviceSyntax
public import Core.Ast.LowLevel.Execution

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

/-- A unit using the register protocol preserves ownership from issue to
    reply and checks successful answers at the commit cut. -/
def RegisterUnitAussenLokalAussage : Prop :=
  ∀ k (binding : Binding k) access required target
    (E : Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit),
    E.katalog = k → (∀ form, E.system.regel form = Rule.machine binding access required target) →
    Annahme.AussenLokal E

theorem register_unit_aussenLokal : RegisterUnitAussenLokalAussage := by
  intro k binding access required target E catalogue rules
  refine ⟨Aussen.zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w trace next step
  cases step with
  | kontext _ _ source executes =>
    obtain ⟨form, _, transfer⟩ := source
    rw [rules form] at transfer
    obtain ⟨chosen, plans, rule⟩ := transfer
    cases (List.cons.inj plans).1
    exact register_aussenLokal k binding access required target E run t c s _ _
      trace next catalogue rule executes

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
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterUnitAussenLokalAussage ∧ RegisterCommitAussage ∧
  RegisterSafetyAussage ∧ RegisterRegelSicherAussage (fun access => ∃ offset, access = .read offset)

def RegisterWriteAussage : Prop :=
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterUnitAussenLokalAussage ∧ RegisterCommitAussage ∧
  RegisterSafetyAussage ∧ RegisterRegelSicherAussage (fun access => ∃ offset value, access = .write offset value)

def RegisterReadElseAussage : Prop :=
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterUnitAussenLokalAussage ∧ RegisterCommitAussage ∧
  RegisterSafetyAussage ∧ RegisterFallibleAussage ∧
  RegisterRegelSicherAussage (fun access => ∃ offset range, access = .fallibleRead offset range) ∧
  ∀ (k : Katalog) (scope : Scope) (d : Denotation k scope) destination binding offset promise handler,
    d = .fallibleRead destination binding offset promise handler →
    (∀ err, d.resume (.refused err) = .branch handler) ∧
    ∀ value, d.resume (.readOutOfRange value) = .branch handler

theorem register_fallible_resume :
    ∀ (k : Katalog) (scope : Scope) (d : Denotation k scope) destination binding offset promise handler,
      d = .fallibleRead destination binding offset promise handler →
      (∀ err, d.resume (.refused err) = .branch handler) ∧
      ∀ value, d.resume (.readOutOfRange value) = .branch handler := by
  intro k scope d destination binding offset promise handler definition
  subst d
  constructor <;> intro result <;> rfl

theorem register_read_provable :
    RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterUnitAussenLokalAussage ∧
      RegisterCommitAussage ∧ RegisterSafetyAussage :=
  ⟨register_befugt, register_aussenLokal, register_unit_aussenLokal, register_commit, register_safety⟩

theorem registerRegelSicher_falsch :
    ¬ RegisterRegelSicherAussage (fun access => ∃ offset, access = .read offset) := by
  intro hsicher
  let k : Katalog := Plattform.x86_64.katalog
  let binding : Binding k :=
    { handle := ⟨0, ⟨⟨.virtio, 0⟩, 0⟩, [.read, .write]⟩
      row := Plattform.x86_64.virtio
      selected := by
        simp only [k, Katalog.enthaelt, Plattform.katalog, Plattform.zeilen, Plattform.endpunkte,
          List.map_cons, List.mem_append, List.mem_cons, eq_self, or_true, true_or]
      described := rfl }
  let access : RegisterAccess := .read 0x70
  let owner : Kontext := .faden 0
  let startdaten : Startdaten UInt8 PUnit Frame PUnit :=
    { lokal := fun _ => {}
      status := fun _ => .ruht
      kerne := fun _ => ⟨none, .nutzer, (), fun _ => false, 0, false, []⟩
      rechte := ⟨fun _ => true, fun _ => 0⟩ }
  let wiederanlauf : Wiederanlauf Nat UInt8 PUnit Frame PUnit :=
    { eintritt := owner
      kern := 0
      daten := fun _ => startdaten
      initial := fun _ _ => 0 }
  let einr : Einrichtung PUnit Nat UInt8 PUnit Frame PUnit PUnit :=
    { initial := fun _ => 0
      sperrOrt := fun _ => 0
      ereignisOrt := fun _ => 0
      ereignisWert := fun _ => 0
      bedingung := fun _ _ _ => False
      invariant := fun s _ => s.verlauf = []
      persistenzRegion := ⟨0, 0⟩
      wiederanlauf := wiederanlauf
      speicherObjekt := fun _ => 0
      speicherGriff := fun _ _ _ => none }
  let sys : MaschinenSystem PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit :=
    { regel := fun _ => registerRule binding access
      kopf := fun _ _ => some ()
      fertig := fun _ _ => False
      blockiert := fun _ _ _ => False }
  let maschine : Maschine.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit :=
    { katalog := k
      bild := LowLevel.image
      einrichtung := einr
      system := sys
      startdaten := fun _ => startdaten
      startmedium := fun _ _ => 0
      laden := fun _ _ => none
      lokalerBezug := Eq
      stotterLaenge := fun _ => 0
      quelltabellen := ⟨.leer, fun _ _ _ => False⟩ }
  let E : Sicherheit.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit :=
    ⟨maschine, []⟩
  let boot : State :=
    Zustand.start (fun _ => { phases := fun o => if o = binding.object then some .ready else none })
      (fun _ => .laeuft) (fun _ => ⟨some owner, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => true, fun _ => 0⟩ (fun _ => 0) (.leer (fun _ => 0))
  let vor : State :=
    { boot with buchung := { boot.buchung with
        geraet := fun o => if o = binding.object then some (owner, .frei) else none
        aussengriff := fun c h right => c = owner ∧ h = binding.handle ∧ right ∈ h.rights
        umfang := fun i => if i = 0 then List.range 4096 else []
        haelt := fun _ _ _ => False } }
  let q : Frage := binding.question access
  let plan : Plan := { internal with aktion := .frage q }
  let zwischen : State := setFrame vor owner { (vor.lokal owner) with pending := some q }
  let event : FrageEreignis := vor.stelleFrage 0 owner q
  let label := aussenEtikett einr (.frage event)
  obtain ⟨g', hschritt⟩ := Speicher.Zustand.schritt_ohne_lesen
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    (SpeicherAkteur.kontext owner) label (fun h => h)
  let folge : Speicherfolge (fun _ : Nat => (0 : UInt8)) (SpeicherAkteur.kontext owner)
      Speicher.Zustand.leer [label] [(SpeicherAkteur.kontext owner, label)] g' :=
    .cons (Initialisierung.ohne (Or.inl rfl)) hschritt (.nil _)
  let spur : SchrittSpur Nat UInt8 := ⟨[(SpeicherAkteur.kontext owner, label)], [.frage event]⟩
  let nach : State := { zwischen.frage event with graph := g' }
  let sicht0 : AussenSicht := AussenSicht.leer
  let H : Katalog.Umgebung := Umgebung.referenz k 2 (fun _ _ => sicht0)
  let hw : HwLauf := Umgebung.referenzLauf k 2 (fun _ _ => sicht0)
  let start : AussenStart := ⟨0, fun _ => none, [], fun _ => none, sicht0⟩
  let ρ : Sicherheit.Lauf E :=
    ⟨start, hw, Classical.choose (Zeitlauf.existiert (Lauffolge E.maschine hw) none)⟩
  have owns : Befugt binding .ready access vor owner := by
    refine ⟨rfl, rfl, ?_, rfl⟩
    intro z inAccess
    change z ∈ [⟨binding.handle, access.operation.required⟩] at inAccess
    cases List.mem_singleton.mp inAccess
    refine ⟨rfl, rfl, ?_⟩
    cases access with
    | read _ | fallibleRead _ _ => exact List.mem_cons_self
    | write _ _ => exact List.mem_cons_of_mem _ List.mem_cons_self
  have rule : Rule binding access .ready none owner vor plan zwischen := by
    exact Rule.issue owns rfl
  have impl : (sys.regel ()).impl owner vor () [plan] zwischen := by
    dsimp [sys, registerRule, Rule.machine]
    exact ⟨plan, rfl, rule⟩
  have executed : FuehrtSchrittAus einr 0 owner vor zwischen plan spur nach := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro l inRead
      simpa only [plan, internal, List.not_mem_nil] using inRead
    · refine ⟨[], zwischen.frage event, ?_, ?_, ?_⟩
      · exact FuehrtAus.frage q
      · simpa [spur, label, vor, boot, Zustand.start, plan, internal, schreibEreignisse, nach] using folge
      · rfl
  have hs := hsicher k binding access E ⟨0x70, rfl⟩ rfl rfl H ρ 0 owner () vor zwischen nach
    plan spur (by rfl) impl executed
  have hvor : Sicherheit.InvariantenAmSchnitt E vor := by
    refine ⟨?_, ?_⟩
    · intro l free
      rfl
    · intro i d hd
      change none = some d at hd
      cases hd
  have hleer : nach.verlauf = [] := (hs.invarianten hvor).1 () rfl
  simp only [nach, zwischen, Zustand.frage, Zustand.stelleFrage, event, vor, boot,
    Zustand.start, List.nil_append, List.cons_ne_nil] at hleer

end Gabbro.Core.Ast.LowLevel.Device
