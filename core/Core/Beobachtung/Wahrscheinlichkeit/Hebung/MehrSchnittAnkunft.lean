/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/MehrSchnittAnkunft.lean
  Subject:   Two admitted draw cuts on one shared multi-cut policy (M9P).

  The shared policy of `MehrSchnitt` installs a band-selected exchange body at each
  scheduled cut. This module carries its total atomic decision down to the machine
  arrival boundary: the commit computed from the shared policy is turned into an
  admitted `AntwortSchritt` and packed as `Teilbuendel`'s checked draw step
  `IstZufallsAnkunftSchritt`. Two distinct cuts of the one policy are exhibited with
  the bodies of two distinct draw indices, and the two-position cylinder has exactly
  the product measure by `ZiehungsMass`.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.MehrSchnitt

public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Katalog Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- A successful exchange answer on a snapshot: the decision is total and its body payload
    is the snapshot body, with origin and revalidation footprint unchanged. -/
private theorem atomar_exchange_erfolg (p : Plattform) (basis : AussenSicht) (q : Frage)
    {tag : List UInt8} (operation : q.operation = .exchange tag)
    (supported : p.operationAngeboten q = true)
    (valid : q.zugriffe.all (basis.gueltig q.endpoint) = true)
    (wartet : basis.wartet p q = false)
    (ready : (basis.objects q.handle.origin.object).ready = true) :
    atomar p basis q =
      .antwort ⟨basis.herkunft q.handle.origin.object,
        q.zugriffe.map (fun z => basis.herkunft z.handle.origin.object),
        .ok (.exchanged tag (basis.objects q.handle.origin.object).body)⟩ := by
  have erfolg : basis.erfolg p q =
      .ok (.exchanged tag (basis.objects q.handle.origin.object).body) := by
    simp only [AussenSicht.erfolg, operation]
  simp only [atomar, supported, valid, wartet, ready, erfolg, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

/-- The total decision of the shared policy at a scheduled cut, specialized to a successful
    marked exchange: only the body payload is replaced by the band-selected body. -/
private theorem mehrSchnittPlan_erfolg {B : Zufallsbindung}
    (code : Fin B.quelle.anz → List UInt8) (objekt : Objekt) {p : Plattform} {h : Umgebung}
    (plan : SchnittPlan) {u : Nat} {verlauf : AussenVerlauf} {q : Frage} {tag : List UInt8}
    (body : List UInt8)
    (hplan : plan u = some (objekt, body))
    (operation : q.operation = .exchange tag)
    (supported : p.operationAngeboten q = true)
    (valid : q.zugriffe.all ((h.politik.sicht u verlauf).gueltig q.endpoint) = true)
    (ready : ((h.politik.sicht u verlauf).objects objekt).ready = true)
    (hobj : q.handle.origin.object = objekt) :
    atomar p (mehrSchnittSicht h.politik.sicht plan u verlauf) q =
      .antwort ⟨(h.politik.sicht u verlauf).herkunft objekt,
        q.zugriffe.map (fun z => (h.politik.sicht u verlauf).herkunft z.handle.origin.object),
        .ok (.exchanged tag body)⟩ := by
  rw [mehrSchnittUmgebung_atomarTotal]
  simp only [hplan]
  rw [if_pos hobj]
  have basis : atomar p (h.politik.sicht u verlauf) q =
      .antwort ⟨(h.politik.sicht u verlauf).herkunft objekt,
        q.zugriffe.map (fun z => (h.politik.sicht u verlauf).herkunft z.handle.origin.object),
        .ok (.exchanged tag ((h.politik.sicht u verlauf).objects objekt).body)⟩ := by
    have warte : (h.politik.sicht u verlauf).wartet p q = false := by
      simp only [AussenSicht.wartet, operation]
    have rdy : ((h.politik.sicht u verlauf).objects q.handle.origin.object).ready = true := by
      rw [hobj]
      exact ready
    exact atomar_exchange_erfolg p (h.politik.sicht u verlauf) q operation supported valid warte rdy
  rw [basis]
  rw [operation]
  simp only [antwortBody, erfolgBody, wertBody]

/-- The commit of the shared policy at a scheduled cut is the atomic decision above, since
    the shared environment is row-governed by `mehrSchnittUmgebung_hardware`. -/
private theorem mehrSchnittPlan_commit {B : Zufallsbindung}
    (code : Fin B.quelle.anz → List UInt8) (objekt : Objekt) {k : Katalog} {h : Umgebung}
    (hardware : Hardware k h) (plan : SchnittPlan) {u : Nat} {verlauf : AussenVerlauf}
    {q : Frage} {tag : List UInt8} (body : List UInt8)
    (hplan : plan u = some (objekt, body))
    (selected : k.enthaelt (.endpoint q.endpoint))
    (operation : q.operation = .exchange tag)
    (supported : k.plattform.operationAngeboten q = true)
    (valid : q.zugriffe.all ((h.politik.sicht u verlauf).gueltig q.endpoint) = true)
    (ready : ((h.politik.sicht u verlauf).objects objekt).ready = true)
    (hobj : q.handle.origin.object = objekt) :
    (mehrSchnittUmgebung k h plan).politik.antwort u verlauf q =
      .antwort ⟨(h.politik.sicht u verlauf).herkunft objekt,
        q.zugriffe.map (fun z => (h.politik.sicht u verlauf).herkunft z.handle.origin.object),
        .ok (.exchanged tag body)⟩ := by
  rw [(mehrSchnittUmgebung_hardware hardware plan).antwort u verlauf q selected]
  rw [mehrSchnittUmgebung_sicht]
  exact mehrSchnittPlan_erfolg code objekt plan body hplan operation supported valid ready hobj

/-- Turn an already-installed policy's commit at a pending question into an admitted
    machine arrival. This is the arrival half of `KatalogAnkunft.zufallsAnkunft`, used
    there once and here at two cuts of one shared policy. -/
private theorem zufallsAnkunftBeiPolitik {k : Katalog} {h : Umgebung} {run : HwLauf}
    {u : Nat} {q : FrageEreignis} {s : Zustand L Ort Wert Raum Lok Grund}
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    (konform : run.konform k h)
    (pending : q ∈ s.fragen) (epoche : s.epoche ≤ q.cut) (gestellt : q.cut ≤ u)
    (einmal : ∀ a ∈ s.antworten, a.questionInstance ≠ q.questionInstance)
    (delivery : (run.angebot u).delivery q.question.endpoint = true)
    (selected : k.enthaelt (.endpoint q.question.endpoint))
    (konsistent : s.graph.graph.Konsistent) (vollstaendig : s.graph.graph.Vollstaendig)
    (reply : Antwort)
    (commit : h.politik.antwort u s.verlauf q.question = .antwort reply) :
    ∃ a spur s', a.question = q.question ∧ AntwortSchritt e k run u a s spur s' ∧
      a.reply = reply := by
  let a : AntwortEreignis := ⟨u, q.context, q.questionInstance, q.question, reply⟩
  have zu : a.zu q := ⟨gestellt, rfl, rfl, rfl⟩
  have offered : s.AntwortAngeboten k run u a := by
    refine ⟨rfl, ⟨delivery, ?_⟩, selected, ⟨q, pending, epoche, zu⟩, einmal⟩
    change run.politik.antwort u s.verlauf q.question = .antwort reply
    rw [konform.1]
    exact commit
  let label := aussenEtikett e (.antwort a)
  obtain ⟨g', schritt⟩ := Speicher.Zustand.schritt_ohne_lesen konsistent vollstaendig
    (SpeicherAkteur.aussen : SpeicherAkteur Ort) label id
  refine ⟨a, ⟨[(.aussen, label)], [.antwort a]⟩, { s.antwort a with graph := g' }, rfl, ?_, rfl⟩
  exact ⟨offered, rfl, .cons (.ohne (Or.inl rfl)) schritt (.nil _), rfl⟩

/-- Pack a shared-policy arrival as `Teilbuendel`'s checked draw step at the chosen index. -/
private theorem mehrSchnitt_checkedStep {B : Zufallsbindung}
    (code : Fin B.quelle.anz → List UInt8) (objekt : Objekt) (k : Katalog) (h : Umgebung)
    (plan : SchnittPlan) (b : Band) (index : Nat)
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (u : Nat) (s : Zustand L Ort Wert Raum Lok Grund) (q : FrageEreignis) (run : HwLauf)
    (hardware : Hardware k h) (konform : run.konform k (mehrSchnittUmgebung k h plan))
    (pending : q ∈ s.fragen) (epoche : s.epoche ≤ q.cut) (gestellt : q.cut ≤ u)
    (einmal : ∀ a ∈ s.antworten, a.questionInstance ≠ q.questionInstance)
    (delivery : (run.angebot u).delivery q.question.endpoint = true)
    (selected : k.enthaelt (.endpoint q.question.endpoint))
    (konsistent : s.graph.graph.Konsistent) (vollstaendig : s.graph.graph.Vollstaendig)
    (marker : Zufallsfrage B q.question)
    (body : List UInt8)
    (hbody : body = code (Ziehung B.quelle b index))
    (hplan : plan u = some (objekt, body))
    (operation : q.question.operation = .exchange B.kennung)
    (supported : k.plattform.operationAngeboten q.question = true)
    (valid : q.question.zugriffe.all ((h.politik.sicht u s.verlauf).gueltig q.question.endpoint) = true)
    (ready : ((h.politik.sicht u s.verlauf).objects objekt).ready = true)
    (hobj : q.question.handle.origin.object = objekt) :
    ∃ a spur s',
      IstZufallsAnkunftSchritt B code b E u index (some s)
        (some (SchrittWahl.antwort (Wahl := Wahl) a, spur), some s') ∧
      (some (SchrittWahl.antwort (Wahl := Wahl) a, spur) :
        Option (SchrittWahl Wahl × SchrittSpur Ort Wert)) ≠ none := by
  let reply : Antwort := ⟨(h.politik.sicht u s.verlauf).herkunft objekt,
    q.question.zugriffe.map (fun z => (h.politik.sicht u s.verlauf).herkunft z.handle.origin.object),
    .ok (.exchanged B.kennung body)⟩
  have commit : (mehrSchnittUmgebung k h plan).politik.antwort u s.verlauf q.question = .antwort reply := by
    dsimp only [reply]
    exact mehrSchnittPlan_commit code objekt hardware plan body hplan selected operation supported
      valid ready hobj
  obtain ⟨a, spur, s', hquestion, schritt, areply⟩ := zufallsAnkunftBeiPolitik
    (e := E.einrichtung) konform pending epoche gestellt einmal delivery selected
    konsistent vollstaendig reply commit
  refine ⟨a, spur, s', ?_, ?_⟩
  · dsimp only [IstZufallsAnkunftSchritt]
    refine ⟨a, spur, s, s', rfl, rfl, ?_, reply.origin, reply.checkedObjects, body, ?_, hbody, ?_⟩
    · simpa only [hquestion] using marker
    · rw [areply]
      rfl
    · exact ⟨run, schritt⟩
  · simp

/-- The two-position cylinder of the two draw cuts has exactly the product measure. -/
theorem zweiZiehungsSchnitte_mass (Q : Zufallsquelle) (a0 a1 : Fin Q.anz) :
    bandMass Q {band : Band | Ziehung Q band 0 = a0 ∧ Ziehung Q band 1 = a1} =
      Q.gesetz a0 * Q.gesetz a1 := by
  let Z : Zylinder Q := ⟨[(0, a0), (1, a1)]⟩
  have hnodup : (Z.pfad.map Prod.fst).Nodup := by
    simp [Z]
  have mass := bandMass_zylinder Q Z hnodup
  have hmenge : {band : Band | Ziehung Q band 0 = a0 ∧ Ziehung Q band 1 = a1} =
      {band : Band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val} := by
    ext band
    simp [Z, Ziehung, Fin.ext_iff]
  rw [hmenge]
  simpa only [Z, ZylinderGewicht, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] using mass

end Gabbro.Core.Beobachtung
