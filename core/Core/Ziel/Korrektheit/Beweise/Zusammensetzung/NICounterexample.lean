module

public import Core.Beobachtung.Satz
import Core.Beobachtung.Fluss.Beschriftung.Leck
import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Beobachtung Katalog Maschine

private def geheimeLadersicht (alive : Bool) : Nat → AussenVerlauf → AussenSicht :=
  fun _ _ =>
    { AussenSicht.leer with
      objects := fun _ => { AussenSicht.leer.objects ⟨.hosted, 0⟩ with alive } }

private def laderLeck : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  let basis := (Sicherheit.Laufkonstruktion.einheit Sicherheit.Laufkonstruktion.start
    (fun _ _ _ _ => False) []).maschine
  { basis with
    etiketten := { objekt := fun _ => Ast.Semantik.geheim, endpunkt := fun _ => Ast.Semantik.geheim }
    laden := fun s _ => if (s.outside.objects ⟨.hosted, 0⟩).alive then
      some Sicherheit.Laufkonstruktion.start else none }

private theorem laderLeck_label_union :
    Ast.Semantik.geheim ∪ Ast.Semantik.geheim = Ast.Semantik.geheim := by
  ext n
  simp only [Finset.mem_union, or_self]

private theorem laderLeck_sicht (a b : Bool) (t : Nat) (v : AussenVerlauf) :
    niedereAussensicht laderLeck.etiketten (geheimeLadersicht a t v) =
      niedereAussensicht laderLeck.etiketten (geheimeLadersicht b t v) := by
  refine Prod.ext (funext fun o => ?_) rfl
  change sichtbar (Ast.Semantik.geheim ∪ Ast.Semantik.geheim) ((geheimeLadersicht a t v).objects o) =
    sichtbar (Ast.Semantik.geheim ∪ Ast.Semantik.geheim) ((geheimeLadersicht b t v).objects o)
  simp only [laderLeck_label_union, sichtbar, Ast.Semantik.geheim_verborgen, Bool.false_eq_true, if_false]

private theorem laderLeck_frage (q : Frage) : laderLeck.etiketten.frage q = Ast.Semantik.geheim := by
  change (q.zugriffe.map (fun _ => Ast.Semantik.geheim)).foldl (· ∪ ·) Ast.Semantik.geheim =
    Ast.Semantik.geheim
  induction q.zugriffe with
  | nil => rfl
  | cons _ _ ih => simpa only [List.map_cons, List.foldl_cons, laderLeck_label_union] using ih

private theorem laderLeck_umgebung :
    GleicheNiedrigeUmgebung laderLeck
      (Sicherheit.Laufkonstruktion.umgebung (geheimeLadersicht true))
      (Sicherheit.Laufkonstruktion.umgebung (geheimeLadersicht false)) := by
  have policy : politikProjektion laderLeck.etiketten
      (Sicherheit.Laufkonstruktion.umgebung (geheimeLadersicht true)).politik =
    politikProjektion laderLeck.etiketten
      (Sicherheit.Laufkonstruktion.umgebung (geheimeLadersicht false)).politik := by
    apply Prod.ext
    · exact funext fun t v => laderLeck_sicht true false t (niedrigerVerlauf laderLeck.etiketten v)
    · refine Prod.ext ?_ rfl
      funext t v q
      simp only [politikProjektion, laderLeck_frage, sichtbar, Ast.Semantik.geheim_verborgen,
        Bool.false_eq_true, if_false]
  unfold GleicheNiedrigeUmgebung umgebungsProjektion
  rw [policy]

private theorem ladefehler_bleibt {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} (init : ρ.zeit.zustand 0 = none)
    (p : Praediktor) (t : Nat) :
    NiedrigeBeob E ρ p t = [.ladefehler] := by
  have leer (u : Nat) : ρ.zeit.zustand u = none ∧ ρ.zeit.spur u = none := by
    have zustandLeer (i : Nat) : ρ.zeit.zustand i = none := by
      induction i with
      | zero => exact init
      | succ i ih =>
        have takt := ρ.zeit.takt i
        rw [ih] at takt
        cases takt with
        | schritt _ step => cases step
        | wartet _ same _ => exact same
    have takt := ρ.zeit.takt u
    rw [zustandLeer u] at takt
    cases takt with
    | schritt _ step => cases step
    | wartet idle _ _ => exact ⟨zustandLeer u, idle⟩
  induction t with
  | zero => simp only [NiedrigeBeob, NiedrigeBeob.praefix, init]
  | succ t ih => exact (beob_pause ρ p t (leer t).2).trans ih

/-- A loaded run and a loader failure have incompatible low traces under the same public policy. -/
theorem vergleich_mit_ladefehler {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {H₁ H₂ : Umgebung} {s₁ s₂ : AussenStart} {z : Zustand L Ort Wert Raum Lok Grund}
    (hw₁ : Hardware E.katalog H₁) (hw₂ : Hardware E.katalog H₂)
    (zul₁ : E.ZulStart H₁ s₁) (zul₂ : E.ZulStart H₂ s₂)
    (lowEnv : GleicheNiedrigeUmgebung E H₁ H₂) (lowStart : NiedrigGleich E s₁ s₂)
    (loaded : E.laden s₁ (H₁.lade E.bild) = some z)
    (failed : E.laden s₂ (H₂.lade E.bild) = none) :
    ∃ (links rechts : Lauf E), Vergleich E H₁ H₂ links rechts ∧
      ¬ NiedrigAequiv E (NiedrigeBeob E links) (NiedrigeBeob E rechts) := by
  obtain ⟨links, lauf₁, start₁⟩ := lauf_ab_start E hw₁ zul₁
  obtain ⟨rechts, lauf₂, start₂, policy⟩ := vergleichslauf E lauf₁ hw₂ lowEnv zul₂
  refine ⟨links, rechts, ⟨lauf₁, lauf₂, lowEnv, ?_, policy⟩, ?_⟩
  · rw [start₁, start₂]
    exact lowStart
  · intro beob
    let predictor : Praediktor := ⟨fun _ _ => false, fun _ _ => 0, fun _ _ => none⟩
    have init₁ : links.zeit.zustand 0 = some z := by
      rw [lauf₁.2.2.2, start₁]
      exact loaded
    have init₂ : rechts.zeit.zustand 0 = none := by
      rw [lauf₂.2.2.2, start₂]
      exact failed
    obtain ⟨u, related⟩ := (beob predictor).1 0
    have erster : NiedrigeBeob E links predictor 0 =
        [.anfangsspeicher (fun x => sichtbar (E.etiketten.ort x) (z.initial x))] := by
      simp only [NiedrigeBeob, NiedrigeBeob.praefix, init₁]
    rw [erster, ladefehler_bleibt init₂ predictor u] at related
    change List.Forall₂ (EreignisAequiv E.fluss.freigabe)
      [.anfangsspeicher (fun x => sichtbar (E.etiketten.ort x) (z.initial x))] [.ladefehler] at related
    cases related with
    | cons head _ => cases head

/-- A generic machine unit whose loader publicly succeeds or fails according to a private object. -/
theorem niRefutierbar :
    ∃ E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit, ¬ Nichtinterferent E := by
  refine ⟨laderLeck, ?_⟩
  intro ni
  let H₁ := Sicherheit.Laufkonstruktion.umgebung (geheimeLadersicht true)
  let H₂ := Sicherheit.Laufkonstruktion.umgebung (geheimeLadersicht false)
  have hw₁ : Hardware laderLeck.katalog H₁ :=
    Sicherheit.Laufkonstruktion.erlaubt (geheimeLadersicht true)
  have hw₂ : Hardware laderLeck.katalog H₂ :=
    Sicherheit.Laufkonstruktion.erlaubt (geheimeLadersicht false)
  obtain ⟨s₁, zul₁⟩ := zulStart_erfuellbar hw₁ Sicherheit.Laufkonstruktion.bild_gueltig
  let s₂ := { s₁ with outside := geheimeLadersicht false 0 [] }
  obtain ⟨image, core, assignments, fits, apart, regions, bytes, outside⟩ := zul₁
  have zul₁ : laderLeck.ZulStart H₁ s₁ :=
    ⟨image, core, assignments, fits, apart, regions, bytes, outside⟩
  have zul₂ : laderLeck.ZulStart H₂ s₂ :=
    ⟨image, core, assignments, fits, apart, regions, bytes, rfl⟩
  have lowStart : NiedrigGleich laderLeck s₁ s₂ := by
    unfold NiedrigGleich startProjektion
    change (s₁.bootCore, s₁.assignment, s₁.regions, _,
      niedereAussensicht laderLeck.etiketten s₁.outside) =
      (s₁.bootCore, s₁.assignment, s₁.regions, _,
        niedereAussensicht laderLeck.etiketten (geheimeLadersicht false 0 []))
    rw [outside]
    exact congrArg (fun view => (s₁.bootCore, s₁.assignment, s₁.regions,
      (fun a => (sichtbar (laderLeck.etiketten.bootByte a) (s₁.inputBytes a)).join), view))
      (laderLeck_sicht true false 0 [])
  have loaded : laderLeck.laden s₁ (H₁.lade laderLeck.bild) = some Sicherheit.Laufkonstruktion.start := by
    change (if (s₁.outside.objects ⟨.hosted, 0⟩).alive then
      some Sicherheit.Laufkonstruktion.start else none) = _
    rw [outside] <;> rfl
  have failed : laderLeck.laden s₂ (H₂.lade laderLeck.bild) = none := rfl
  obtain ⟨links, rechts, v, mismatch⟩ :=
    vergleich_mit_ladefehler hw₁ hw₂ zul₁ zul₂ laderLeck_umgebung lowStart loaded failed
  exact mismatch ((ni H₁ H₂ links rechts.start hw₁ hw₂ v.links v.umgebung
    v.rechts.2.2.1 v.start).2 rechts v.rechts rfl v.politik)

end Gabbro.Core.Ziel.Korrektheit
