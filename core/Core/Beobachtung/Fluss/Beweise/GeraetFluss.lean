module

public import Core.Beobachtung.Fluss.Beweise.Geraet
public import Core.Beobachtung.Fluss.Beweise.GeraetEntwurf
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device (Binding Denotation Rule RegisterAccess Frame State Plan)
open Gabbro.Core.Ast.LowLevel.Device (setFrame internal)

/-- Every elaborated device rule is a `Rule.machine` with fixed access and phase target. -/
private theorem denotation_rule_machine {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) :
    ∃ (binding : Binding k) (access : RegisterAccess) (required : GeraetePhase)
      (target : Option GeraetePhase),
      d.rule locals = Rule.machine binding access required target := by
  cases d with
  | read destination binding offset =>
      exact ⟨binding, .read offset, .ready, none, rfl⟩
  | fallibleRead destination binding offset promise handler =>
      exact ⟨binding, .fallibleRead offset promise, .ready, none, rfl⟩
  | write binding offset value =>
      exact ⟨binding, .write offset (value.wert locals).wert.toNat, .ready, none, rfl⟩
  | transition decl =>
      exact ⟨decl.binding, .write decl.row.offset decl.data, decl.changes.prior,
        some decl.changes.after, rfl⟩

/-- A form step of the device unit is a `Rule` of the denotation's machine rule. -/
private theorem formschritt_rule {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) {c v w p u}
    (s : FormSchritt (d.unit locals) () c v w p u)
    {binding : Binding k} {access : RegisterAccess} {required : GeraetePhase}
    {target : Option GeraetePhase}
    (ruleEq : d.rule locals = Rule.machine binding access required target) :
    Rule binding access required target c v p u := by
  have si := s.2
  dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit] at si
  rw [ruleEq] at si
  change (Rule.machine binding access required target).ideal c v w [p] u at si
  dsimp only [Rule.machine] at si
  rcases si with ⟨plan, hplans, rule⟩
  cases hplans
  exact rule

/-- With empty labels the public local projection is full equality. -/
private theorem quellgleich_lokal {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) {v u : State}
    (q : QuellzustandGleich (d.unit locals) v u) : v.lokal = u.lokal := by
  have hl := q.1
  dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit, Einheit.fluss,
    Flussdaten.leer, Flussdaten.lokal, LokaleEtiketten.ganz, LokaleEtiketten.gleich] at hl
  funext c
  exact hl c ⟨0, Nat.zero_lt_one⟩ (by simp only [oeffentlich, decide_true])

/-- The empty outside labels make every question visible. -/
private theorem leer_frage (q : Frage) : (Etiketten.leer (Ort := Nat)).frage q = (∅ : Etikett) := by
  simp only [Etiketten.frage, Etiketten.leer]
  induction q.zugriffe with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.map_cons, Finset.empty_union] at ih ⊢
      exact ih

private theorem leer_frage_sichtbar (q : Frage) (a : AntwortEreignis) :
    sichtbar ((Etiketten.leer (Ort := Nat)).frage q) a = some a := by
  rw [leer_frage]
  simp only [sichtbar, oeffentlich, decide_true, if_true]

/-- With empty labels the public answer view is full equality of `naechsteAntwort`. -/
private theorem quellgleich_antwort {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) {v u : State} {c : Kontext}
    (q : QuellzustandGleich (d.unit locals) v u) :
    v.naechsteAntwort c = u.naechsteAntwort c := by
  have h := q.2.2.2.2.2 c
  unfold AntwortSicht at h
  change (v.naechsteAntwort c).bind
      (fun a => sichtbar ((Etiketten.leer (Ort := Nat)).frage a.question) a) =
    (u.naechsteAntwort c).bind
      (fun a => sichtbar ((Etiketten.leer (Ort := Nat)).frage a.question) a) at h
  cases hv : v.naechsteAntwort c with
  | none =>
      cases hu : u.naechsteAntwort c with
      | none => rfl
      | some b =>
          simp only [hv, hu, Option.bind, leer_frage_sichtbar] at h
          cases h
  | some a =>
      cases hu : u.naechsteAntwort c with
      | none =>
          simp only [hv, hu, Option.bind, leer_frage_sichtbar] at h
          cases h
      | some b =>
          simp only [hv, hu, Option.bind, leer_frage_sichtbar] at h
          exact h

/-- Rebuilding public source equality after a step that changes only one context's frame. -/
private theorem quellgleich_nach_frame {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) {v u v₁ u₁ : State}
    (q : QuellzustandGleich (d.unit locals) v u)
    (lokEq : v₁.lokal = u₁.lokal)
    (hs₁ : ∀ d', v₁.status d' = v.status d') (hs₂ : ∀ d', u₁.status d' = u.status d')
    (hi₁ : v₁.initial = v.initial) (hi₂ : u₁.initial = u.initial)
    (hr₁ : v₁.rechte = v.rechte) (hr₂ : u₁.rechte = u.rechte)
    (hl₁ : v₁.leihen = v.leihen) (hl₂ : u₁.leihen = u.leihen)
    (hna₁ : ∀ d', v₁.naechsteAntwort d' = v.naechsteAntwort d')
    (hna₂ : ∀ d', u₁.naechsteAntwort d' = u.naechsteAntwort d') :
    QuellzustandGleich (d.unit locals) v₁ u₁ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d' p hp
    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit, Einheit.fluss,
      Flussdaten.leer, Flussdaten.lokal, LokaleEtiketten.ganz, LokaleEtiketten.gleich] at hp ⊢
    change v₁.lokal d' = u₁.lokal d'
    rw [lokEq]
  · intro d'
    dsimp only [EndeSicht]
    rw [hs₁ d', hs₂ d']
    exact q.2.1 d'
  · intro x
    rw [hi₁, hi₂]
    exact q.2.2.1 x
  · rw [hr₁, hr₂]
    exact q.2.2.2.1
  · rw [hl₁, hl₂]
    exact q.2.2.2.2.1
  · intro d'
    unfold AntwortSicht
    rw [hna₁ d', hna₂ d', quellgleich_antwort locals d q]

/-- The device form's public flow rule. Issue and consume cannot both be enabled from
    publicly equal source states (their pending requirements conflict), and equal step
    kinds from such states publish equal plans and post-states. -/
theorem geraeteRegelFlussAussage {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) : RegelFluss (d.unit locals) () := by
  constructor
  · intro c v w p u schritt
    constructor
    · unfold AusgabeLokal
      dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit, Einheit.fluss,
        Flussdaten.leer, Flussdaten.ausgaben, Flussdaten.ausgabeZuwachs]
      constructor
      · rfl
      · intro id quelle wert neu
        cases neu
    · intro hpriv
      have hpub : oeffentlich ((d.unit locals).fluss.kontrolle ()) = true := by
        change decide ((∅ : Etikett) = ∅) = true
        simp only [decide_eq_true_eq]
      rw [hpub] at hpriv
      cases hpriv
  · intro hpub c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ qg s₁ s₂
    obtain ⟨binding, access, required, target, ruleEq⟩ := denotation_rule_machine locals d
    have rule₁ : Rule binding access required target c v₁ p₁ u₁ :=
      formschritt_rule locals d s₁ ruleEq
    have rule₂ : Rule binding access required target c v₂ p₂ u₂ :=
      formschritt_rule locals d s₂ ruleEq
    have hlok : v₁.lokal = v₂.lokal := quellgleich_lokal locals d qg
    have hant₂ : v₁.naechsteAntwort c = v₂.naechsteAntwort c := quellgleich_antwort locals d qg
    have ausgabeEq : ∀ (a b : State), AusgabeSicht (d.unit locals) c a b = [] := by
      intro a b
      dsimp only [AusgabeSicht, AusgabeZuwachs, Denotation.unit,
        Gabbro.Core.Ast.LowLevel.Device.unit, Einheit.fluss, Flussdaten.leer,
        Flussdaten.ausgabeZuwachs]
      rfl
    have pendingEq : (v₁.lokal c).pending = (v₂.lokal c).pending := by rw [hlok]
    cases rule₁ with
    | issue owned₁ idle₁ =>
        cases rule₂ with
        | issue owned₂ idle₂ =>
            have postEq : (setFrame v₁ c { v₁.lokal c with pending := some (binding.question access) }).lokal =
                (setFrame v₂ c { v₂.lokal c with pending := some (binding.question access) }).lokal := by
              dsimp only [setFrame]
              rw [hlok]
            refine ⟨quellgleich_nach_frame locals d qg postEq (fun _ => rfl) (fun _ => rfl)
              rfl rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl), ?_, ausgabeEq _ _⟩
            dsimp only [PlanSicht, Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit,
              Einheit.fluss, Flussdaten.leer, Einheit.etiketten, Etiketten.leer, internal]
        | @consume owned₂ answer₂ pending₂ ready₂ same₂ =>
            rw [← pendingEq, idle₁] at pending₂
            cases pending₂
    | @consume owned₁ answer₁ pending₁ ready₁ same₁ =>
        cases rule₂ with
        | issue owned₂ idle₂ =>
            rw [pendingEq, idle₂] at pending₁
            cases pending₁
        | @consume owned₂ answer₂ pending₂ ready₂ same₂ =>
            have hans : answer₁ = answer₂ := by
              have tmp := hant₂
              rw [ready₁] at tmp
              rw [ready₂] at tmp
              exact Option.some.inj tmp
            have hres : access.result answer₁.reply = access.result answer₂.reply :=
              congrArg (fun a => access.result a.reply) hans
            refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ausgabeEq _ _⟩
            · intro d' p hp
              dsimp only [LokaleGleich, Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit,
                Einheit.fluss, Flussdaten.leer, Flussdaten.lokal, LokaleEtiketten.ganz,
                LokaleEtiketten.gleich] at hp ⊢
              by_cases hdc : d' = c
              · subst d'
                dsimp only [setFrame, Function.update_self]
                rw [hres]
                cases hrw : access.result answer₂.reply with
                | written =>
                    cases ht : target with
                    | none => rw [hlok]
                    | some phase => rw [hlok]
                | value _ | readOutOfRange _ | refused _ | unexpectedAnswer =>
                    rw [hlok]
              · simp only [setFrame, Function.update_of_ne hdc]
                exact congrFun hlok d'
            · intro d'
              dsimp only [EndeSicht, setFrame]
              exact qg.2.1 d'
            · intro x
              exact qg.2.2.1 x
            · exact qg.2.2.2.1
            · exact qg.2.2.2.2.1
            · intro d'
              unfold AntwortSicht
              simpa only [setFrame, Zustand.naechsteAntwort, Zustand.angekommen] using
                congrArg (fun o => o.bind
                    (fun a => sichtbar ((d.unit locals).etiketten.frage a.question) a))
                  (quellgleich_antwort locals d (c := d') qg)
            dsimp only [PlanSicht, Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit,
              Einheit.fluss, Flussdaten.leer, internal]

/-- Acceptance of a device unit binds the decidable checker row to its elaborated rule:
    `Akzeptiert` supplies `FlussLokal`, whose form rule is `geraeteRegelFlussAussage`; the
    elaborated rule's access and phase target are exactly the shapes the row accepts. -/
theorem geraeteEinheitAkzeptanzPruefer {k scope} (locals : Ast.Umgebung scope)
    (d : Denotation k scope) (akzeptiert : Annahme.Akzeptiert (d.unit locals)) :
    ∃ (binding : Binding k) (access : RegisterAccess) (required : GeraetePhase)
      (target : Option GeraetePhase),
      d.rule locals = Rule.machine binding access required target ∧
        geraetProtokollRegelBool access target = true := by
  have _fluss := Annahme.akzeptiert_fluss akzeptiert
  have _regelFluss := _fluss.2 ()
  cases d with
  | read destination binding offset =>
      exact ⟨binding, .read offset, .ready, none, rfl, rfl⟩
  | fallibleRead destination binding offset promise handler =>
      exact ⟨binding, .fallibleRead offset promise, .ready, none, rfl, rfl⟩
  | write binding offset value =>
      exact ⟨binding, .write offset (value.wert locals).wert.toNat, .ready, none, rfl, rfl⟩
  | transition decl =>
      refine ⟨decl.binding, .write decl.row.offset decl.data, decl.changes.prior,
        some decl.changes.after, rfl, ?_⟩
      cases decl.changes.freeAfter with
      | inl h => rw [h]; rfl
      | inr h => rw [h]; rfl

end Gabbro.Core.Beobachtung
