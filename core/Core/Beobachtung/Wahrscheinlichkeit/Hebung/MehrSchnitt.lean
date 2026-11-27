/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/MehrSchnitt.lean
  Subject:   The causal multi-cut exchange policy over one shared outside policy (M9P).

  `austauschUmgebung` installs one band-selected body at one commit cut. This module
  generalizes it to ONE policy that schedules a body at every cut of a plan, the body at
  cut `u` being selected by the draw index determined by the marked response prefix
  strictly before `u`. The draw index is `schnittIndex` = the consumed-answer count of
  `Teilbuendel`, proved causal from `StimmenBis`: equal prefixes give equal indices, so
  equal draws give equal bodies. Every cut's atomic decision is total (same object: the
  body payload is rewritten; other object: unchanged), and a nonrandom question disjoint
  from the draw keeps its base decision by `KatalogErhalt`. Two distinct cuts of one
  shared plan are exhibited with distinct indices.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.KatalogErhalt
public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.Teilbuendel

public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Katalog Gabbro.Core.Maschine

/-- Which object carries which exchange body at a cut, or no rewrite at all. -/
abbrev SchnittPlan := Nat → Option (Objekt × List UInt8)

/-- The sight of the shared policy at one cut: the base snapshot with the scheduled
    object's body overwritten. Cuts with no scheduled exchange keep the base sight. -/
def mehrSchnittSicht (basis : Nat → AussenVerlauf → AussenSicht)
    (plan : SchnittPlan) (u : Nat) (verlauf : AussenVerlauf) : AussenSicht :=
  match plan u with
  | none => basis u verlauf
  | some (objekt, body) => austauschSichtOeffentlich (basis u verlauf) objekt body

/-- One outside policy carrying all scheduled cuts. At a scheduled cut the answer is the
    atomic decision on the rewritten snapshot; everywhere else it is the base answer. -/
def mehrSchnittUmgebung (k : Katalog) (h : Umgebung) (plan : SchnittPlan) : Umgebung :=
  let sicht := fun u verlauf => mehrSchnittSicht h.politik.sicht plan u verlauf
  let antwort := fun u verlauf q =>
    match plan u with
    | none => h.politik.antwort u verlauf q
    | some _ => atomar k.plattform (sicht u verlauf) q
  { h with politik := ⟨sicht, antwort, h.politik.dma⟩ }

/-- The shared policy is governed by the same rows: at an unscheduled cut it equals the
    base answer and sight, at a scheduled cut it is atomic by construction. -/
theorem mehrSchnittUmgebung_sicht (k : Katalog) (h : Umgebung) (plan : SchnittPlan) :
    (mehrSchnittUmgebung k h plan).politik.sicht = mehrSchnittSicht h.politik.sicht plan := rfl

theorem mehrSchnittUmgebung_hardware (hardware : Hardware k h) (plan : SchnittPlan) :
    Hardware k (mehrSchnittUmgebung k h plan) := by
  refine { hardware with antwort := ?_ }
  intro u verlauf q selected
  dsimp only [mehrSchnittUmgebung, mehrSchnittSicht]
  cases hplan : plan u with
  | none => simpa only [hplan] using hardware.antwort u verlauf q selected
  | some _ => rfl

/-- **Total atomic decision at a cut.** For every question the decision at a cut of the
    shared policy is fully determined: an unscheduled cut leaves it untouched; a scheduled
    cut rewrites exactly the body of a successful body-carrying answer on the scheduled
    object and leaves every other question unchanged. -/
theorem mehrSchnittUmgebung_atomarTotal {p : Plattform} {h : Umgebung} {plan : SchnittPlan}
    {u : Nat} {verlauf : AussenVerlauf} {q : Frage} :
    atomar p (mehrSchnittSicht h.politik.sicht plan u verlauf) q =
      match plan u with
      | none => atomar p (h.politik.sicht u verlauf) q
      | some (objekt, body) =>
          if q.handle.origin.object = objekt then
            match atomar p (h.politik.sicht u verlauf) q with
            | .antwort a => .antwort (antwortBody q body a)
            | .warten => .warten
          else atomar p (h.politik.sicht u verlauf) q := by
  cases hplan : plan u with
  | none =>
      simp only [mehrSchnittSicht, hplan]
  | some pair =>
      rcases pair with ⟨objekt, body⟩
      dsimp only [mehrSchnittSicht]
      rw [hplan]
      by_cases hobj : q.handle.origin.object = objekt
      · rw [if_pos hobj]
        exact atomar_austauschSicht_sichtbar (p := p) (basis := h.politik.sicht u verlauf)
          (objekt := objekt) (body := body) hobj
      · rw [if_neg hobj]
        exact atomar_austauschSicht_verschieden (p := p) (basis := h.politik.sicht u verlauf)
          (objekt := objekt) (body := body) hobj

/-- **Nonrandom policy preserved.** A nonrandom question on every object disjoint from
    the scheduled exchange keeps its base atomic decision at every cut, by
    `KatalogErhalt`. The lift's nonrandom premise is carried but not needed beyond the
    disjointness; both are stated so the law is used in exactly the lift's shape. -/
theorem mehrSchnittUmgebung_nichtZufallErhalt {B : Zufallsbindung} {p : Plattform}
    {h : Umgebung} {plan : SchnittPlan} {u : Nat} {verlauf : AussenVerlauf} {q : Frage}
    (hd : ∀ objekt body, plan u = some (objekt, body) → q.handle.origin.object ≠ objekt)
    (hnat : ¬ Zufallsfrage B q) :
    atomar p (mehrSchnittSicht h.politik.sicht plan u verlauf) q =
      atomar p (h.politik.sicht u verlauf) q := by
  cases hplan : plan u with
  | none =>
      simp only [mehrSchnittSicht, hplan]
  | some pair =>
      rcases pair with ⟨objekt, body⟩
      dsimp only [mehrSchnittSicht]
      rw [hplan]
      exact atomar_austauschSicht_nichtZufall (B := B) (p := p)
        (basis := h.politik.sicht u verlauf) (objekt := objekt) (body := body)
        (hd objekt body hplan) hnat

/-- The draw index at a cut is the number of marked random answers in the earlier marked
    response prefix of the replay, i.e. `Teilbuendel`'s consumed-answer count. -/
def schnittIndex (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (u : Nat) : Nat := ziehungenBis B ρ u

/-- **Causality of the index.** Two replays agreeing on states up to `u` and traces below
    `u` have consumed the same number of marked answers, hence select the same draw. -/
theorem schnittIndex_stimmtÜberein (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ₁ ρ₂ : Maschine.Lauf E) (u : Nat) (h : StimmenBis E ρ₁ ρ₂ u) :
    schnittIndex B ρ₁ u = schnittIndex B ρ₂ u := by
  induction u with
  | zero => rfl
  | succ u ih =>
      have hprev : StimmenBis E ρ₁ ρ₂ u :=
        ⟨fun m hm => h.1 m (Nat.le_trans hm (Nat.le_succ u)),
         fun t ht => h.2 t (Nat.lt_trans ht (Nat.lt_succ_self u))⟩
      have hi : ziehungenBis B ρ₁ u = ziehungenBis B ρ₂ u := by
        simpa only [schnittIndex] using ih hprev
      have hspur : ρ₁.zeit.spur u = ρ₂.zeit.spur u := h.2 u (Nat.lt_succ_self u)
      simp only [schnittIndex, ziehungenBis, hi, antwortenBei, hspur]

/-- A shared plan with two distinct draw cuts on one object: the body at each cut is the
    code of the draw whose index is the earlier marked response prefix count. -/
def zweiSchnittPlan (B : Zufallsbindung) (code : Fin B.quelle.anz → List UInt8)
    (objekt : Objekt) {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (b : Band) (ρ : Maschine.Lauf E) : SchnittPlan
  | 0 => some (objekt, code (Ziehung B.quelle b (schnittIndex B ρ 0)))
  | 1 => some (objekt, code (Ziehung B.quelle b (schnittIndex B ρ 1)))
  | _ => none

/-- The first draw cut uses index `0`; after it has consumed its marked answer the second
    draw cut uses index `1`. The two indices are distinct. -/
theorem zweiSchnittPlan_indexVerschieden (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (a : AntwortEreignis) (spur : SchrittSpur Ort Wert)
    (hfrag : Zufallsfrage B a.question)
    (hspur : ρ.zeit.spur 0 = some (SchrittWahl.antwort (Wahl := Wahl) a, spur))
    (haussen : spur.aussen = [Ereignis.antwort a]) :
    schnittIndex B ρ 0 ≠ schnittIndex B ρ 1 := by
  have h0 : schnittIndex B ρ 0 = 0 := rfl
  have h1 : schnittIndex B ρ 1 = 1 := by
    simp only [schnittIndex, ziehungenBis, antwortenBei_anzahl B ρ 0 a spur hfrag hspur haussen]
  omega

/-- **Two distinct draw cuts on one shared policy.** Both cuts carry the draw-selected
    body on the exchange object, and at both the atomic decision is total in the same
    way: same object rewrites the body payload, other object is untouched. -/
theorem zweiSchnittPlan_atomarTotal {B : Zufallsbindung} (code : Fin B.quelle.anz → List UInt8)
    (objekt : Objekt) {p : Plattform} {h : Umgebung} (b : Band)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (verlauf : AussenVerlauf) (q0 q1 : Frage)
    (hobj0 : q0.handle.origin.object = objekt) (hobj1 : q1.handle.origin.object = objekt) :
    let plan := zweiSchnittPlan B code objekt b ρ
    atomar p (mehrSchnittSicht h.politik.sicht plan 0 verlauf) q0 =
        (match atomar p (h.politik.sicht 0 verlauf) q0 with
         | .antwort a => .antwort (antwortBody q0 (code (Ziehung B.quelle b (schnittIndex B ρ 0))) a)
         | .warten => .warten) ∧
    atomar p (mehrSchnittSicht h.politik.sicht plan 1 verlauf) q1 =
        (match atomar p (h.politik.sicht 1 verlauf) q1 with
         | .antwort a => .antwort (antwortBody q1 (code (Ziehung B.quelle b (schnittIndex B ρ 1))) a)
         | .warten => .warten) := by
  dsimp only
  constructor
  · rw [mehrSchnittUmgebung_atomarTotal]
    simp only [zweiSchnittPlan, hobj0, if_true]
  · rw [mehrSchnittUmgebung_atomarTotal]
    simp only [zweiSchnittPlan, hobj1, if_true]

/-- The nonrandom policy is preserved at both cuts of the shared plan. -/
theorem zweiSchnittPlan_nichtZufallErhalt {B : Zufallsbindung}
    (code : Fin B.quelle.anz → List UInt8) (objekt : Objekt)
    {p : Plattform} {h : Umgebung} (b : Band)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (verlauf : AussenVerlauf) (q : Frage)
    (hnat : ¬ Zufallsfrage B q) (hd : q.handle.origin.object ≠ objekt) :
    let plan := zweiSchnittPlan B code objekt b ρ
    atomar p (mehrSchnittSicht h.politik.sicht plan 0 verlauf) q =
        atomar p (h.politik.sicht 0 verlauf) q ∧
    atomar p (mehrSchnittSicht h.politik.sicht plan 1 verlauf) q =
        atomar p (h.politik.sicht 1 verlauf) q := by
  dsimp only
  constructor
  · apply mehrSchnittUmgebung_nichtZufallErhalt (B := B) (p := p) (q := q) ?_ hnat
    intro obj body hplan
    have hp : some (objekt, code (Ziehung B.quelle b (schnittIndex B ρ 0))) = some (obj, body) := by
      simpa only [zweiSchnittPlan] using hplan
    have ho : objekt = obj := congrArg Prod.fst (Option.some.inj hp)
    simpa only [ho] using hd
  · apply mehrSchnittUmgebung_nichtZufallErhalt (B := B) (p := p) (q := q) ?_ hnat
    intro obj body hplan
    have hp : some (objekt, code (Ziehung B.quelle b (schnittIndex B ρ 1))) = some (obj, body) := by
      simpa only [zweiSchnittPlan] using hplan
    have ho : objekt = obj := congrArg Prod.fst (Option.some.inj hp)
    simpa only [ho] using hd

end Gabbro.Core.Beobachtung
