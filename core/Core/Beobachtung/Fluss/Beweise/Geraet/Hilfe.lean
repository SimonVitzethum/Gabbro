module

public import Core.Beobachtung.Fluss.Beweise.GeraetInvariante
public import Core.Beobachtung.Nichtinterferenz
public import Core.Beobachtung.Projektion
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- The device unit carries empty labels, an empty flow table and empty bounds. -/
theorem geraete_etiketten_leer (d : Denotation k scope) :
    (d.unit locals).etiketten = .leer := by
  cases d <;> rfl

theorem geraete_fluss_leer (d : Denotation k scope) :
    (d.unit locals).fluss = .leer := by
  cases d <;> rfl

/-- A low question label is empty, so every device question is public. -/
theorem geraete_frage_leer {Ort : Type} (q : Frage) :
    (Etiketten.leer (Ort := Ort)).frage q = ∅ := by
  simp only [Etiketten.frage, Etiketten.leer]
  induction q.zugriffe with
  | nil => simp only [List.map_nil, List.foldl_nil]
  | cons _ _ ih =>
    simp only [List.map_cons, List.foldl_cons, Finset.empty_union] at ih ⊢
    exact ih

theorem geraete_oeffentlich_leer : oeffentlich (∅ : Etikett) = true := by
  simp only [oeffentlich, decide_eq_true_eq]

theorem geraete_sichtbar_leer {A : Type} (x : A) :
    sichtbar (∅ : Etikett) x = some x := by
  simp only [sichtbar, geraete_oeffentlich_leer, if_true]

/-- With empty labels the public local projection is full equality. -/
theorem geraete_lokal_gleich {v u : State}
    (q : QuellzustandGleich (d.unit locals) v u) : v.lokal = u.lokal := by
  have hl := q.1
  dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit, Einheit.fluss,
    Flussdaten.leer, Flussdaten.lokal, LokaleEtiketten.ganz, LokaleEtiketten.gleich] at hl
  funext c
  exact hl c ⟨0, Nat.zero_lt_one⟩ (by simp only [oeffentlich, decide_true])

/-- The empty outside labels make every question visible. -/
theorem geraete_frage_sichtbar (q : Frage) (a : AntwortEreignis) :
    sichtbar ((Etiketten.leer (Ort := Nat)).frage q) a = some a := by
  rw [geraete_frage_leer]
  simp only [sichtbar, oeffentlich, decide_true, if_true]

/-- With empty labels the public answer view is full equality of `naechsteAntwort`. -/
theorem geraete_antwort_gleich {v u : State} {c : Kontext}
    (q : QuellzustandGleich (d.unit locals) v u) :
    v.naechsteAntwort c = u.naechsteAntwort c := by
  have hetik : (d.unit locals).etiketten = .leer := geraete_etiketten_leer d
  have h := q.2.2.2.2.2 c
  unfold AntwortSicht at h
  change (v.naechsteAntwort c).bind
      (fun a => sichtbar ((d.unit locals).etiketten.frage a.question) a) =
    (u.naechsteAntwort c).bind
      (fun a => sichtbar ((d.unit locals).etiketten.frage a.question) a) at h
  rw [hetik] at h
  simp only [geraete_frage_sichtbar] at h
  cases hv : v.naechsteAntwort c with
  | none =>
      cases hu : u.naechsteAntwort c with
      | none => rfl
      | some b =>
          simp only [hv, hu, Option.bind] at h
          cases h
  | some a =>
      cases hu : u.naechsteAntwort c with
      | none =>
          simp only [hv, hu, Option.bind] at h
          cases h
      | some b =>
          simp only [hv, hu, Option.bind] at h
          exact h

/-- Every elaborated device rule is a `Rule.machine` with fixed access and phase target. -/
theorem geraete_rule_form (locals : Umgebung scope) (d : Denotation k scope) :
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

/-- Invert a device context step to its head form and elaborated rule. -/
theorem geraete_kontext_regel {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    (ruleEq : d.rule locals = Rule.machine binding access required target)
    {c : Kontext} {s u : State} {w : PUnit} {plan : Plan}
    (regel : (d.unit locals).system.ImplSchritt c s w [plan] u) :
    (d.unit locals).system.kopf s c = some () ∧
      ∃ plan', [plan] = [plan'] ∧ Rule binding access required target c s plan' u := by
  obtain ⟨i, kopfEq, impl⟩ := regel
  cases i
  refine ⟨kopfEq, ?_⟩
  dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit] at impl
  rw [ruleEq] at impl
  dsimp only [Rule.machine] at impl
  exact impl

/-- Same-cut hardware offers coincide on compared runs: empty labels expose everything. -/
theorem geraete_angebot_gleich {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) (t : Nat) :
    (ρ₁.hw.angebot t) = (ρ₂.hw.angebot t) := by
  have hang := congrArg Prod.fst vergleich.politik
  have ht := congrFun hang t
  have hetik : (d.unit locals).etiketten = .leer := geraete_etiketten_leer d
  simp only [hwPolitikProjektion] at ht
  generalize ha1 : (ρ₁.hw.angebot t) = a1 at ht
  generalize ha2 : (ρ₂.hw.angebot t) = a2 at ht
  simp only [angebotProjektion, hetik] at ht
  have hend : ∀ e : Endpunkt, (Etiketten.leer (Ort := Nat)).endpunkt e = ∅ :=
    fun _ => rfl
  simp only [hend, geraete_sichtbar_leer] at ht
  have ecore : a1.core = a2.core := congrArg Prod.fst ht
  have einterrupt : a1.interrupt = a2.interrupt := congrArg (fun t => t.2.1) ht
  have einterrupts : a1.interrupts = a2.interrupts := congrArg (fun t => t.2.2.1) ht
  have hdelivery : (fun e => some (a1.delivery e)) = (fun e => some (a2.delivery e)) :=
    congrArg (fun t => t.2.2.2.1) ht
  have emedium : a1.medium = a2.medium := congrArg (fun t => t.2.2.2.2.1) ht
  have ecrash : a1.crash = a2.crash := congrArg (fun t => t.2.2.2.2.2.1) ht
  have ecycles : a1.cycles = a2.cycles := congrArg (fun t => t.2.2.2.2.2.2) ht
  have hdel : a1.delivery = a2.delivery :=
    funext fun e => Option.some.inj (congrFun hdelivery e)
  have eta1 : a1 = ⟨a1.core, a1.interrupt, a1.interrupts, a1.delivery, a1.medium,
    a1.crash, a1.cycles⟩ := rfl
  have eta2 : a2 = ⟨a2.core, a2.interrupt, a2.interrupts, a2.delivery, a2.medium,
    a2.crash, a2.cycles⟩ := rfl
  rw [eta1, eta2, ecore, einterrupt, einterrupts, hdel, emedium, ecrash, ecycles]

theorem geraete_delivery_gleich {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) (t : Nat) (e : Endpunkt) :
    (ρ₁.hw.angebot t).delivery e = (ρ₂.hw.angebot t).delivery e := by
  rw [geraete_angebot_gleich vergleich t]

/-- The low history projection is the identity under empty labels. -/
theorem geraete_verlauf_leer {Ort : Type} (h : AussenVerlauf) :
    niedrigerVerlauf (Etiketten.leer (Ort := Ort)) h = h := by
  have key : ∀ e : Nat × AussenEreignis,
      (match e.2 with
        | .frage q | .antwort q _ => oeffentlich ((Etiketten.leer (Ort := Ort)).frage q)) = true := by
    intro e
    obtain ⟨_, ev⟩ := e
    cases ev with
    | frage q => simp only [geraete_frage_leer, geraete_oeffentlich_leer]
    | antwort q _ => simp only [geraete_frage_leer, geraete_oeffentlich_leer]
  unfold niedrigerVerlauf
  induction h with
  | nil => rfl
  | cons e tail ih =>
    exact (List.filter_cons_of_pos (p := fun entry : Nat × AussenEreignis =>
      match entry.2 with
      | .frage q | .antwort q _ => oeffentlich ((Etiketten.leer (Ort := Ort)).frage q))
      (a := e) (l := tail) (key e)).trans (congrArg _ ih)

/-- Compared runs answer every question identically: empty labels expose the policy. -/
theorem geraete_politik_antwort_gleich {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (t : Nat) (history : AussenVerlauf) (q : Frage) :
    ρ₁.hw.politik.antwort t history q = ρ₂.hw.politik.antwort t history q := by
  have hsnd := congrArg Prod.snd vergleich.politik
  have hetik : (d.unit locals).etiketten = .leer := geraete_etiketten_leer d
  simp only [hwPolitikProjektion, politikProjektion, hetik, geraete_verlauf_leer] at hsnd
  simp only [geraete_frage_leer, geraete_sichtbar_leer] at hsnd
  have h2 := congrArg (fun p : _ × _ × _ => p.2.1) hsnd
  have h3 := congrFun (congrFun (congrFun h2 t) history) q
  exact Option.some.inj h3

/-- Authority transfers across runs with equal booking and local states. -/
theorem geraete_befugt_transport {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {c : Kontext} {s₁ s₂ : State}
    (h : Befugt binding required access s₁ c)
    (buchung : s₁.buchung = s₂.buchung) (lokal : s₁.lokal = s₂.lokal) :
    Befugt binding required access s₂ c := by
  obtain ⟨hgeraet, hphasen, heigen, hzugriff⟩ := h
  refine ⟨?_, ?_, ?_, hzugriff⟩
  · rw [← buchung]
    exact hgeraet
  · rw [← lokal]
    exact hphasen
  · unfold Gabbro.Core.Annahme.AussengriffeEigen at heigen ⊢
    intro z hz
    exact buchung ▸ heigen z hz

/-- An offered answer is offered on the compared run with equal ledgers and epoch. -/
theorem geraete_angeboten_transport {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    {s₁ s₂ : State} {t : Nat} {a : AntwortEreignis}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (offered : s₁.AntwortAngeboten (d.unit locals).katalog ρ₁.hw t a)
    (hfragen : s₁.fragen = s₂.fragen) (hverlauf : s₁.verlauf = s₂.verlauf)
    (hantworten : s₁.antworten = s₂.antworten) (hepoche : s₁.epoche = s₂.epoche) :
    s₂.AntwortAngeboten (d.unit locals).katalog ρ₂.hw t a := by
  obtain ⟨hcut, herlaubt, henthaelt, hfrage, hfrisch⟩ := offered
  refine ⟨hcut, ?_, henthaelt, ?_, ?_⟩
  · obtain ⟨hdel, hpol⟩ := herlaubt
    have hgoal : (ρ₂.hw.angebot a.cut).delivery a.question.endpoint = true ∧
        ρ₂.hw.politik.antwort a.cut s₂.verlauf a.question = Entscheidung.antwort a.reply := by
      rw [hcut] at hdel hpol ⊢
      refine ⟨?_, ?_⟩
      · have hdel2 := geraete_delivery_gleich vergleich t a.question.endpoint
        rw [← hdel2]
        exact hdel
      · have hpol2 := geraete_politik_antwort_gleich vergleich t s₂.verlauf a.question
        rw [← hpol2, ← hverlauf]
        exact hpol
    exact hgoal
  · obtain ⟨q, hqmem, hqcut, hzu⟩ := hfrage
    exact ⟨q, hfragen ▸ hqmem, hepoche ▸ hqcut, hzu⟩
  · intro e he
    exact hfrisch e (hantworten.symm ▸ he)

/-- Question instances follow the ledger order. -/
theorem geraete_fragen_inst {fragen : List FrageEreignis}
    (hrange : List.map (fun q : FrageEreignis => q.questionInstance) fragen =
      List.range fragen.length)
    {j : Nat} (hj : j < fragen.length) : (fragen[j]'hj).questionInstance = j := by
  have h0 : ((List.range fragen.length)[j]?) = some j := List.getElem?_range hj
  rw [← hrange] at h0
  have h2 : ((fragen.map (fun q : FrageEreignis => q.questionInstance))[j]?) =
      Option.map (fun q : FrageEreignis => q.questionInstance) (fragen[j]?) :=
    List.getElem?_map
  rw [h2, List.getElem?_eq_getElem hj] at h0
  simp only [Option.map_some] at h0
  exact Option.some.inj h0

/-- Compared runs agree at every cut on whether a state is loaded. -/
theorem geraete_zustand_gemeinsam {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) (t : Nat) :
    (ρ₁.zeit.zustand t = none ∧ ρ₂.zeit.zustand t = none) ∨
      (∃ v₁ v₂, ρ₁.zeit.zustand t = some v₁ ∧ ρ₂.zeit.zustand t = some v₂) := by
  induction t with
  | zero =>
    have ladenEq := geraete_laden_gleich (d := d) vergleich.umgebung vergleich.start
    have z1 := vergleich.links.2.2.2
    have z2 := vergleich.rechts.2.2.2
    cases h : (d.unit locals).laden ρ₁.start (h₁.lade (d.unit locals).bild) with
    | none =>
      exact Or.inl ⟨z1.trans h, z2.trans (ladenEq.symm.trans h)⟩
    | some v =>
      exact Or.inr ⟨v, _, z1.trans h, z2.trans (ladenEq.symm.trans h)⟩
  | succ t ih =>
    cases ih with
    | inl hnone =>
      obtain ⟨n1, n2⟩ := hnone
      have tick1 := ρ₁.zeit.takt t
      rw [n1] at tick1
      have tick2 := ρ₂.zeit.takt t
      rw [n2] at tick2
      cases tick1 with
      | schritt _ step1 => cases step1
      | wartet _ eq1 _ =>
        cases tick2 with
        | schritt _ step2 => cases step2
        | wartet _ eq2 _ =>
          exact Or.inl ⟨eq1, eq2⟩
    | inr hsome =>
      obtain ⟨v1, v2, s1, s2⟩ := hsome
      have tick1 := ρ₁.zeit.takt t
      rw [s1] at tick1
      have tick2 := ρ₂.zeit.takt t
      rw [s2] at tick2
      generalize hN1 : ρ₁.zeit.zustand (t + 1) = post1 at tick1
      generalize hN2 : ρ₂.zeit.zustand (t + 1) = post2 at tick2
      cases tick1 with
      | schritt _ step1 =>
        cases step1 with
        | schritt _ =>
          cases tick2 with
          | schritt _ step2 =>
            cases step2 with
            | schritt _ => exact Or.inr ⟨_, _, rfl, rfl⟩
          | wartet _ eq2 _ => exact Or.inr ⟨_, _, rfl, eq2⟩
      | wartet _ eq1 _ =>
        cases tick2 with
        | schritt _ step2 =>
          cases step2 with
          | schritt _ => exact Or.inr ⟨_, _, eq1, rfl⟩
        | wartet _ eq2 _ => exact Or.inr ⟨_, _, eq1, eq2⟩

end Gabbro.Core.Beobachtung
