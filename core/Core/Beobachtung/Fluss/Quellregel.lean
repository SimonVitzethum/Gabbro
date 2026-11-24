module

public import Core.Beobachtung.Projektion

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)

/-- Local stores are compared place by place using the unit's typed labels. -/
def LokaleGleich (v u : Kontext → Lok) : Prop :=
  ∀ c, (E.fluss.lokal c).gleich (v c) (u c)

def EndeSicht (c : Kontext) : Status Wert Grund → Option (Ende Wert Grund)
  | .beendet e => sichtbar (E.etiketten.ende c) e
  | .ruht | .laeuft => none

def AntwortSicht (v : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) : Option AntwortEreignis :=
  (v.naechsteAntwort c).bind fun a => sichtbar (E.etiketten.frage a.question) a

/-- Public source-state components updated by a form. Shared memory event order is
    handled at the machine boundary, through the public plan and recorded trace. -/
def QuellzustandGleich (v u : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  LokaleGleich E v.lokal u.lokal ∧
  (∀ c, EndeSicht E c (v.status c) = EndeSicht E c (u.status c)) ∧
  (∀ x, sichtbar (E.etiketten.ort x) (v.initial x) =
    sichtbar (E.etiketten.ort x) (u.initial x)) ∧
  v.rechte = u.rechte ∧ v.leihen = u.leihen ∧
    ∀ c, AntwortSicht E v c = AntwortSicht E u c

/-- The syntax-side initialisation respects the public projection of legal inputs.
    The actual loader is related to this specification in the implementation proof. -/
def StartFlussLokal : Prop :=
  ∀ s₁ s₂, NiedrigGleich E s₁ s₂ →
    QuellzustandGleich E (I.start E s₁).2 (I.start E s₂).2

def PlanSicht (p : SchrittPlan L Ort Wert Bedingung) :
    List (Speicher.Etikett Ort Wert) × List (Ort × Speicher.Modus × Wert) × Option Frage :=
  (p.lesen.filter (fun e => oeffentlich (E.etiketten.ort e.ort)),
    p.fuss.filterMap (fun x => if p.schreibt x && oeffentlich (E.etiketten.ort x)
      then some (x, p.modus x, p.wert x) else none),
    match p.aktion with
    | .frage q => sichtbar (E.etiketten.frage q) q
    | _ => none)

def AusgabeZuwachs (c : Kontext) (v u : Zustand L Ort Wert Raum Lok Grund) : List (Ausgabe Wert) :=
  E.fluss.ausgabeZuwachs (v.lokal c) (u.lokal c)

def AusgabeSicht (c : Kontext) (v u : Zustand L Ort Wert Raum Lok Grund) : List (Ausgabe Wert) :=
  ((AusgabeZuwachs E c v u).filter (Ausgabe.niedrig E.etiketten)).map fun
    | .wert kanal wert => .wert kanal wert
    | .freigabe id _ wert =>
      match E.fluss.freigabe id with
      | some g => .freigabe id g.quelle (g.projektion wert)
      | none => .freigabe id ∅ wert

/-- A form's append-only output journal can release to public only through a declaration.
    Each selected release dominates the payload and control labels. -/
def AusgabeLokal (f : Form) (c : Kontext) (v u : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  let neu := AusgabeZuwachs E c v u
  E.fluss.ausgaben (u.lokal c) = E.fluss.ausgaben (v.lokal c) ++ neu ∧
  ∀ id quelle w, Ausgabe.freigabe id quelle w ∈ neu →
    ∃ g, E.fluss.freigabe id = some g ∧ quelle ∪ E.fluss.kontrolle f ⊆ g.quelle ∧
      oeffentlich (E.etiketten.ausgabe g.kanal) = true

def FormSchritt (f : Form) (c : Kontext) (v : Zustand L Ort Wert Raum Lok Grund) (w : Wahl)
    (p : SchrittPlan L Ort Wert Bedingung) (u : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  E.system.kopf v c = some f ∧ (E.system.regel f).ideal c v w [p] u

/-- A private control step preserves the public source state and has no public effect.
    Two executions of a public form from public-equal source states agree on its public
    state and effects. The form's semantic choice is independently quantified on each side. -/
def RegelFluss (f : Form) : Prop :=
  (∀ c v w p u, FormSchritt E f c v w p u →
    AusgabeLokal E f c v u ∧
    (oeffentlich (E.fluss.kontrolle f) = false →
      QuellzustandGleich E v u ∧ PlanSicht E p = ([], [], none) ∧ AusgabeSicht E c v u = [])) ∧
  (oeffentlich (E.fluss.kontrolle f) = true →
    ∀ c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂, QuellzustandGleich E v₁ v₂ →
      FormSchritt E f c v₁ w₁ p₁ u₁ → FormSchritt E f c v₂ w₂ p₂ u₂ →
      QuellzustandGleich E u₁ u₂ ∧ PlanSicht E p₁ = PlanSicht E p₂ ∧
        AusgabeSicht E c v₁ u₁ = AusgabeSicht E c v₂ u₂)

/-- Labelled flow is a source rule. Neither the implementation loader nor runs are queried
    during acceptance. -/
def FlussLokal : Prop :=
  StartFlussLokal E ∧ ∀ f, RegelFluss E f

end Gabbro.Core.Beobachtung
