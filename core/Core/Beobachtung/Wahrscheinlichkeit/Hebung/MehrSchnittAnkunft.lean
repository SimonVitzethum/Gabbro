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
    simpa only [hobj] using
      atomar_exchange_erfolg p (h.politik.sicht u verlauf) q operation supported valid warte rdy
  rw [basis]
  simp only [antwortBody, erfolgBody, wertBody, operation]

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
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (hk : k = E.katalog)
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
      IstZufallsAnkunftSchritt B code b E run u index (some s)
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
    · rw [hk] at schritt
      exact schritt
  · intro empty
    cases empty

/-- The two-position cylinder of the two draw cuts has exactly the product measure. -/
theorem zweiZiehungsSchnitte_mass (Q : Zufallsquelle) (a0 a1 : Fin Q.anz) :
    bandMass Q {band : Band | Ziehung Q band 0 = a0 ∧ Ziehung Q band 1 = a1} =
      Q.gesetz a0 * Q.gesetz a1 := by
  let Z : Zylinder Q := ⟨[(0, a0), (1, a1)]⟩
  have hnodup : (Z.pfad.map Prod.fst).Nodup := by
    simp? [Z]
  have mass := bandMass_zylinder Q Z hnodup
  have hmenge : {band : Band | Ziehung Q band 0 = a0 ∧ Ziehung Q band 1 = a1} =
      {band : Band | ∀ p ∈ Z.pfad, band Q.id p.1 % Q.anz = p.2.val} := by
    ext band
    simp? [Z, Ziehung, Fin.ext_iff]
  rw [hmenge]
  simpa only [Z, ZylinderGewicht, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] using mass

/-- **Two distinct draw cuts on one shared policy.** On the x86-64 platform one base
    environment and one multi-cut plan yield two admitted `Teilbuendel` draw steps at
    cuts `0` and `1`, using draw indices `0` and `1`. The two installed bodies are
    distinct; both arrivals are admitted by the same row-governed shared policy. -/
theorem zweiZiehungsSchnitte_erfuellbar
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (hkatalog : E.katalog = Plattform.x86_64.katalog)
    (basisZ : Zustand L Ort Wert Raum Lok Grund) :
    let B : Zufallsbindung := ⟨muenzQuelle, .cProcess, []⟩
    let code : Fin B.quelle.anz → List UInt8 := fun v => if v.val = 0 then [] else [1]
    let k : Katalog := Plattform.x86_64.katalog
    let obj : Objekt := ⟨.cProcess, 1⟩
    ∃ (s0 s1 : Zustand L Ort Wert Raum Lok Grund) (q0 q1 : FrageEreignis) (band : Band)
      (plan : SchnittPlan) (h : Umgebung) (run : HwLauf) (body0 body1 : List UInt8)
      (a0 : AntwortEreignis) (spur0 : SchrittSpur Ort Wert) (s0' : Zustand L Ort Wert Raum Lok Grund)
      (a1 : AntwortEreignis) (spur1 : SchrittSpur Ort Wert) (s1' : Zustand L Ort Wert Raum Lok Grund),
        q0 ∈ s0.fragen ∧ q1 ∈ s1.fragen ∧
        body0 = code (Ziehung B.quelle band 0) ∧ body1 = code (Ziehung B.quelle band 1) ∧
        body0 ≠ body1 ∧ plan 0 = some (obj, body0) ∧ plan 1 = some (obj, body1) ∧
        Hardware k (mehrSchnittUmgebung k h plan) ∧
        run.konform k (mehrSchnittUmgebung k h plan) ∧
        IstZufallsAnkunftSchritt B code band E run 0 0 (some s0)
          (some (SchrittWahl.antwort (Wahl := Wahl) a0, spur0), some s0') ∧
        IstZufallsAnkunftSchritt B code band E run 1 1 (some s1)
          (some (SchrittWahl.antwort (Wahl := Wahl) a1, spur1), some s1') := by
  dsimp only
  let B : Zufallsbindung := ⟨muenzQuelle, .cProcess, []⟩
  let code : Fin B.quelle.anz → List UInt8 := fun v => if v.val = 0 then [] else [1]
  let k : Katalog := Plattform.x86_64.katalog
  let obj : Objekt := ⟨.cProcess, 1⟩
  let handle : Handle := ⟨0, ⟨obj, 0⟩, [.invoke]⟩
  let q0 : FrageEreignis := ⟨0, 0, 0, ⟨.cProcess, handle, [], .exchange []⟩⟩
  let q1 : FrageEreignis := ⟨1, 0, 0, ⟨.cProcess, handle, [], .exchange []⟩⟩
  let s0 := (Zustand.start (L := L) basisZ.lokal basisZ.status basisZ.kerne basisZ.rechte
    basisZ.initial basisZ.persistenz).frage q0
  let s1 := (Zustand.start (L := L) basisZ.lokal basisZ.status basisZ.kerne basisZ.rechte
    basisZ.initial basisZ.persistenz).frage q1
  let snapshot : AussenSicht := { AussenSicht.leer with
    objects := Function.update AussenSicht.leer.objects obj ⟨0, true, true, [], fun _ => 0⟩
    channels := fun ep i => if ep = .cProcess ∧ i = 0 then some handle else none }
  let h := Umgebung.referenz k 1 (fun _ _ => snapshot)
  let runBase := Umgebung.referenzLauf k 1 (fun _ _ => snapshot)
  let fair : FairLaeufe k h runBase :=
    Umgebung.referenz_fair k 1 _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ 0)
  let band : Band := fun _idx idx => if idx = 0 then 0 else 1
  let body0 := code (Ziehung B.quelle band 0)
  let body1 := code (Ziehung B.quelle band 1)
  let plan : SchnittPlan := fun u =>
    if u = 0 then some (obj, body0) else if u = 1 then some (obj, body1) else none
  let run : HwLauf := { runBase with politik := (mehrSchnittUmgebung k h plan).politik }
  have hw' : Hardware k (mehrSchnittUmgebung k h plan) := mehrSchnittUmgebung_hardware fair.hardware plan
  have konform' : run.konform k (mehrSchnittUmgebung k h plan) := by
    refine ⟨rfl, ?_⟩
    intro i
    change AngebotGueltig k h (runBase.angebot i) (runBase.interruptUrsprung i)
    exact fair.gueltig i
  have endpoint : Zeile.endpoint .cProcess ∈ Plattform.x86_64.zeilen := by
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map_of_mem
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have delivery0 : (run.angebot 0).delivery q0.question.endpoint = true := by
    change decide (Zeile.endpoint .cProcess ∈ Plattform.x86_64.zeilen) = true
    exact decide_eq_true endpoint
  have delivery1 : (run.angebot 1).delivery q1.question.endpoint = true := by
    change decide (Zeile.endpoint .cProcess ∈ Plattform.x86_64.zeilen) = true
    exact decide_eq_true endpoint
  have selected0 : k.enthaelt (.endpoint q0.question.endpoint) :=
    (fair.gueltig 0).2.2.2.1 _ delivery0
  have selected1 : k.enthaelt (.endpoint q1.question.endpoint) :=
    (fair.gueltig 1).2.2.2.1 _ delivery1
  have valid0 : q0.question.zugriffe.all
      ((h.politik.sicht 0 s0.verlauf).gueltig q0.question.endpoint) = true := by
    change q0.question.zugriffe.all (snapshot.gueltig .cProcess) = true
    simp only [q0, Frage.zugriffe, List.all_cons, AussenOperation.required, snapshot,
      AussenSicht.gueltig, handle, obj, AussenSicht.herkunft, Function.update_self,
      ↓reduceIte, and_self, BEq.rfl, List.mem_singleton, decide_true, Bool.and_self, List.all_nil]
  have valid1 : q1.question.zugriffe.all
      ((h.politik.sicht 1 s1.verlauf).gueltig q1.question.endpoint) = true := by
    change q1.question.zugriffe.all (snapshot.gueltig .cProcess) = true
    simp only [q1, Frage.zugriffe, List.all_cons, AussenOperation.required, snapshot,
      AussenSicht.gueltig, handle, obj, AussenSicht.herkunft, Function.update_self,
      ↓reduceIte, and_self, BEq.rfl, List.mem_singleton, decide_true, Bool.and_self, List.all_nil]
  have ready0 : ((h.politik.sicht 0 s0.verlauf).objects obj).ready = true := by
    change (snapshot.objects obj).ready = true
    simp only [snapshot, Function.update_self]
  have ready1 : ((h.politik.sicht 1 s1.verlauf).objects obj).ready = true := by
    change (snapshot.objects obj).ready = true
    simp only [snapshot, Function.update_self]
  have hz0 : Ziehung B.quelle band 0 = (⟨0, by decide⟩ : Fin B.quelle.anz) := by
    apply Fin.ext
    rfl
  have hz1 : Ziehung B.quelle band 1 = (⟨1, by decide⟩ : Fin B.quelle.anz) := by
    apply Fin.ext
    rfl
  have hbodies : body0 ≠ body1 := by
    dsimp only [body0, body1]
    rw [hz0, hz1]
    intro same
    cases same
  have step0 := mehrSchnitt_checkedStep (B := B) code obj k h plan band 0 E hkatalog.symm 0
    s0 q0 run fair.hardware konform' List.mem_cons_self (Nat.zero_le _) (Nat.le_refl _)
    (fun _ mem => (List.not_mem_nil mem).elim) delivery0 selected0
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    (by rfl : Zufallsfrage B q0.question) body0 rfl rfl (by rfl) (by rfl) valid0 ready0 (by rfl)
  have step1 := mehrSchnitt_checkedStep (B := B) code obj k h plan band 1 E hkatalog.symm 1
    s1 q1 run fair.hardware konform' List.mem_cons_self (Nat.zero_le _) (Nat.le_refl _)
    (fun _ mem => (List.not_mem_nil mem).elim) delivery1 selected1
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    (by rfl : Zufallsfrage B q1.question) body1 rfl rfl (by rfl) (by rfl) valid1 ready1 (by rfl)
  obtain ⟨a0, spur0, s0', step0', _⟩ := step0
  obtain ⟨a1, spur1, s1', step1', _⟩ := step1
  refine ⟨s0, s1, q0, q1, band, plan, h, run, body0, body1, a0, spur0, s0', a1, spur1, s1', ?_⟩
  exact ⟨List.mem_cons_self, List.mem_cons_self, rfl, rfl, hbodies, rfl, rfl,
    hw', konform', step0', step1'⟩

end Gabbro.Core.Beobachtung
