module

public import Gabbro.Body
public import Gabbro.Coverage
public import Gabbro.Sicherheit.Anweisung
public import Gabbro.KompositionBeweis.Teil1

@[expose] public section

namespace Gabbro.Komposition
open Gabbro.Body
open Gabbro.Sicherheit

theorem nachpost_of_antwortpasst (S : Signatur) (erg : Option Shape) (R : List String)
    (herg : erg = S.ergebnis) (hR : R = S.gruende) (v : Option Value)
    (ha : AntwortPasst erg R v) : NachPost S v := by
  subst herg; subst hR
  cases hE : S.ergebnis with
  | some sh =>
      cases v with
      | none =>
          rw [hE] at ha
          exact ha.elim
      | some w =>
          rw [hE] at ha
          rw [nachpost_some S sh hE]
          exact ⟨w, rfl, ha⟩
  | none =>
      cases v with
      | none =>
          rw [nachpost_none S hE]
          exact Or.inl rfl
      | some w =>
          rw [hE] at ha
          obtain ⟨q, hq, hwq⟩ := ha
          rw [nachpost_none S hE]
          exact Or.inr ⟨q, hq, by rw [hwq]⟩

/-- **No declared result, no missing `return`.** Against `S.ergebnis = none` the duty
    holds of a body that falls off the end (`finalValue = none`); the C2 failure is
    exactly the declared-result case below. -/
theorem nachpost_none_of_kein_ergebnis (S : Signatur) (h : S.ergebnis = none) :
    NachPost S none := by
  rw [nachpost_none S h]
  exact Or.inl rfl

/-- **C2: a missing `return` fails the duty explicitly.** Where the outcome carries no
    value (`finalValue = none` -- falling off the end, `exit`, `leave`) against a
    declared result, `Nach` is `False`-headed at the answer: no value is invented. -/
theorem pflicht_scheitert_ohne_wert (P : Programm) (Γ : Typing) (S : Signatur)
    (sh : Shape) (ρ : Env) (body : List Stmt) (t s' : State)
    (h : S.ergebnis = some sh) (hfv : finalValue (exec ρ body t) = none) :
    ¬ Nach P Γ S t s' (finalValue (exec ρ body t)) := by
  rw [hfv]
  intro hN
  unfold Nach at hN
  rw [nachpost_some S sh h] at hN
  obtain ⟨v, hv, _⟩ := hN.2
  cases hv

/-- **Valueless outcomes, per outcome value: duty or loud missing `return`.** The
    shared terminal of the `running`/`exited`/`left` (and valueless `returned`)
    branches below, stated over the outcome value `o` so the `cases ho : …`
    substitution in each branch meets it as stated. -/
theorem nach_oder_fehlend_of_kein_wert (P : Programm) (Γ : Typing) (ρ : Env)
    (body : List Stmt) (r : Routine) (t s' : State) (o : Outcome)
    (hw' : Welt P.D Γ s'.world)
    (hfs : finalState o = some s') (hfv : finalValue o = none) :
    (∃ s'', finalState o = some s'' ∧ Nach P Γ r.S t s'' (finalValue o))
    ∨ (finalValue o = none ∧ ∃ sh, r.S.ergebnis = some sh) := by
  by_cases he : ∃ sh, r.S.ergebnis = some sh
  · obtain ⟨sh, hsh⟩ := he
    exact Or.inr ⟨hfv, sh, hsh⟩
  · have hnone : r.S.ergebnis = none := by
      by_contra hne
      exact he (by
        cases hE : r.S.ergebnis with
        | some sh => exact ⟨sh, rfl⟩
        | none => exact absurd hE hne)
    have hnp : Nach P Γ r.S t s' (finalValue o) := by
      rw [hfv]
      exact ⟨hw', nachpost_none_of_kein_ergebnis r.S hnone⟩
    exact Or.inl ⟨s', hfs, hnp⟩

/-- **C1 duty half and C2 ending, per unit: a checked body meets its duty, or its
    missing `return` is named.** From the bridge (`ergebnis_of_geprueft`) plus an
    outcome analysis: `returned` carries the answer through `nachpost_of_antwortpasst`
    (under the emitter's wiring `P.ruferR = S.gruende`); every valueless outcome
    (`running`, `exited`, `left`) meets the duty when no result is declared and stands
    as the loud right disjunct when one is. `stuck` is `False`. Exact residuals: the
    entry `WFU` (C1, provided per call by `wfu_eintritt_of_argumente`), the person's
    `¬ LogikB`, the nested `UmgebungOK`/`SchleifenOK` (C6), and the missing-return
    disjunct (C2). -/
theorem pflicht_of_geprueft_oder_fehlend (P : Programm) (Γ : Typing) (ρ : Env)
    (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (r : Routine) (Δ' : Umgebung)
    (hcheck : pruefeBlock P r.S.ergebnis (paramUmgebung r.S.params) r.body = some Δ')
    (hR : P.ruferR = r.S.gruende)
    (t : State) (hw : Welt P.D Γ t.world)
    (hl : WFU (paramUmgebung r.S.params) t.local')
    (hlogik : ¬ LogikB ρ r.body t) :
    (∃ s', finalState (exec ρ r.body t) = some s' ∧
      Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    ∨ (finalValue (exec ρ r.body t) = none ∧ ∃ sh, r.S.ergebnis = some sh) := by
  have herg := ergebnis_of_geprueft P Γ ρ hD hU hS r.S.ergebnis r.body
    (paramUmgebung r.S.params) Δ' t hcheck hw hl hlogik
  cases ho : exec ρ r.body t with
  | running s' =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
        (Outcome.running s') herg.1 rfl rfl
  | returned s' v =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      cases v with
      | none =>
          exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
            (Outcome.returned s' none) herg.1 rfl rfl
      | some w =>
          have hnp : Nach P Γ r.S t s' (some w) :=
            ⟨herg.1, nachpost_of_antwortpasst r.S r.S.ergebnis P.ruferR rfl hR
              (some w) herg.2.2⟩
          exact Or.inl ⟨s', rfl, hnp⟩
  | exited s' =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
        (Outcome.exited s') herg.1 rfl rfl
  | left s' =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
        (Outcome.left s') herg.1 rfl rfl
  | stuck =>
      rw [ho] at herg; simp only [Ergebnis] at herg

/-- **C3 discharged for leaves: a duty that names only foreign callees IS the
    contract, with no rank.** Where `ruftAuf r.body g → Fremd g` for every `g`, the
    topological order has nothing to order; the single step
    (`vertrag_einzeln_of_pflicht`) is the whole induction. Exact residual: every
    callee foreign. -/
theorem vertrag_blatt_of_pflicht (ρ : Env) (P : Programm) (Γ : Typing)
    (r : Routine) (Fremd : String → Prop)
    (hruns : Runs ρ r.name r.body)
    (hduty : ∀ (t : State), Welt P.D Γ t.world → (∀ g, ruftAuf r.body g → Fremd g) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    (hF : ∀ g, ruftAuf r.body g → Fremd g) :
    Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S) :=
  vertrag_einzeln_of_pflicht ρ P Γ r hruns (fun t hw => hduty t hw hF)

/-- **C3/C4 SCC-at-a-time in miniature: two discharged contract sets compose through
    the shared fold.** The composition adds no induction and no order -- each set
    carries its own justification (a rank for an acyclic group, `ContractBelowM` for
    a cycle) -- so closing supply-at-a-time is exactly closing each supply. Exact
    residual: the per-set discharges plus the partition (`hdef`) over the union. -/
theorem umgebung_ok_kette_of_vertraege (P : Programm) (Γ : Typing) (ρ : Env)
    (rs1 rs2 : List Routine) (Fremd : String → Prop)
    (hcon1 : ∀ r ∈ rs1, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hcon2 : ∀ r ∈ rs2, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs1 ++ rs2, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  apply umgebung_ok_of_vertrag P Γ ρ (rs1 ++ rs2) Fremd _ hdef hFremd hDiv
  intro r hr
  rcases List.mem_append.mp hr with h1 | h2
  · exact hcon1 r h1
  · exact hcon2 r h2

/-- **C4 narrowed: a cycle member's duty assumes foreign posts only for the names its
    body calls.** The ambient `∀ g, Fremd g → …` of `umgebung_ok_of_runs` is weakened
    to `∀ g, ruftAuf r.body g → Fremd g → …` -- an uncalled foreign body is never
    queried along this duty. Exact residual: bounded intra-cycle contracts plus the
    called foreign posts; the emitter's SCC order decides which defined names enter
    as foreign per invocation. -/
theorem umgebung_ok_of_runs_zyklus_min (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop)
    (hrs : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hduty : ∀ r ∈ rs, ∀ (t : State), Welt P.D Γ t.world →
      (∀ r' ∈ rs, ContractBelowM ρ (Routine.toMember P Γ r') r.mass t) →
      (∀ g, ruftAuf r.body g → Fremd g → ∀ S, P.sig g = some S → ∀ u, Welt P.D Γ u.world →
        Welt P.D Γ (ρ g u).1.world ∧ NachPost S (ρ g u).2) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  apply umgebung_ok_of_runs P Γ ρ rs Fremd hrs _ hdef hFremd hDiv
  intro r hr t hw hcb hF
  exact hduty r hr t hw hcb (fun g hg hfr S hs u hu => hF g hfr S hs u hu)

/-- **D split, the answer without the divergence: `UmgebungOK` minus its passthrough
    conjunct.** The world-plus-answer half, derived from canonical contracts and the
    foreign hypothesis alone -- `DivergenzOK` is owed nowhere in it. -/
def UmgebungAntwort (P : Programm) (Γ : Typing) (ρ : Env) : Prop :=
  ∀ f S, P.sig f = some S → ∀ (t : State), Welt P.D Γ t.world →
    Welt P.D Γ (ρ f t).1.world ∧
    (match S.ergebnis with
     | some sh => ∃ v, (ρ f t).2 = some v ∧
        (v.hasShape sh = true ∨ ∃ q, q ∈ S.gruende ∧ v = .reason q)
     | none => (ρ f t).2 = none ∨ ∃ q, q ∈ S.gruende ∧ (ρ f t).2 = some (.reason q))

/-- **The answer half folds without divergence.** Same case split as
    `umgebung_ok_of_vertrag`, minus the conjunct that never touches world or answer. -/
theorem umgebung_antwort_of_vertrag (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop)
    (hcon : ∀ r ∈ rs, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2) :
    UmgebungAntwort P Γ ρ := by
  intro f S hsig t hw
  rcases hdef f S hsig with ⟨r, hr, hname, hS⟩ | hfr
  · subst hname; subst hS
    obtain ⟨hw', ha⟩ := hcon r hr t hw
    exact ⟨hw', ha⟩
  · obtain ⟨hw', ha⟩ := hFremd f hfr S hsig t hw
    exact ⟨hw', ha⟩

/-- **D minimal: the answer plus exactly the divergence conjunct is `UmgebungOK`.**
    `DivergenzOK P.sig` is used once, here, and nowhere else in the fold. -/
theorem umgebung_ok_of_antwort (P : Programm) (Γ : Typing) (ρ : Env)
    (hA : UmgebungAntwort P Γ ρ) (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  intro f S hsig t hw
  obtain ⟨hw', ha⟩ := hA f S hsig t hw
  exact ⟨hw', ha, hDiv⟩

#print axioms Gabbro.Komposition.wfu_eintritt_of_argumente
#print axioms Gabbro.Komposition.nachpost_some
#print axioms Gabbro.Komposition.nachpost_none
#print axioms Gabbro.Komposition.nachpost_of_antwortpasst
#print axioms Gabbro.Komposition.nachpost_none_of_kein_ergebnis
#print axioms Gabbro.Komposition.pflicht_scheitert_ohne_wert
#print axioms Gabbro.Komposition.nach_oder_fehlend_of_kein_wert
#print axioms Gabbro.Komposition.pflicht_of_geprueft_oder_fehlend
#print axioms Gabbro.Komposition.vertrag_blatt_of_pflicht
#print axioms Gabbro.Komposition.umgebung_ok_kette_of_vertraege
#print axioms Gabbro.Komposition.umgebung_ok_of_runs_zyklus_min
#print axioms Gabbro.Komposition.umgebung_antwort_of_vertrag
#print axioms Gabbro.Komposition.umgebung_ok_of_antwort

end Gabbro.Komposition
