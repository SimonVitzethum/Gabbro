/-
  Strong-waiting satisfiability from an empty lock. Three scheduled contexts draw
  tickets, the head takes, and two hand-offs precede the final release.
-/
module

public import Core.Fortschritt.Beweise.SperrStarkHalter4

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

def hw4 : HwLauf := Umgebung.referenzLauf Plattform.x86_64.katalog 3 sicht0

def h4 : Umgebung := Umgebung.referenz Plattform.x86_64.katalog 3 sicht0

theorem fair4 : FairLaeufe E_4.katalog h4 hw4 :=
  Umgebung.referenz_fair _ _ _ Plattform.x86_64.katalog_wohlgeformt (by decide)

theorem hw4_crash (t : Nat) : (hw4.angebot t).crash = false := rfl

theorem hw4_opp (t : Nat) : hw4.gelegenheit t (t % 3) := rfl

theorem e4_implStutter (t : Nat) (c : Kontext)
    (s : Zustand Unit Unit Unit Unit Bool Unit) (hr : KannSchreiten hw4 t c s) :
    ImplSchritt E_4.einrichtung E_4.system E_4.katalog hw4 t s
      (.kontext c (), ⟨[], []⟩) s :=
  .kontext (hw4_crash t) hr ⟨(), rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    ⟨e4_frame s, fun _ h => (List.not_mem_nil h).elim, [], s, .intern, .nil _, rfl⟩

theorem starkeWarteLauf4_erfuellbar : StarkeWarteLaufAussage := by
  obtain ⟨start, hstart⟩ := zulStart_erfuellbar fair4.hardware wBild_gueltig
  let s0 := s4_0
  have h1 : SperrSchritt .ticket A (s0.sperren ()) ⟨none, [A]⟩ := .ticket (fun h => nomatch h) List.not_mem_nil
  let s1 := { toggleUpdate A s0 with
    sperren := Function.update s0.sperren () ⟨none, [A]⟩ }
  have aus1 : FuehrtSchrittAus E_4.einrichtung 0 A s0 (toggleUpdate A s0) ticketPlan
      ⟨[], []⟩ s1 :=
    e4_sperrAus rfl rfl rfl (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) h1 (.nil _)
  have h2 : SperrSchritt .ticket B (s1.sperren ()) ⟨none, [A, B]⟩ := .ticket (fun h => nomatch h) (by decide)
  let s2 := { toggleUpdate B s1 with
    sperren := Function.update s1.sperren () ⟨none, [A, B]⟩ }
  have aus2 : FuehrtSchrittAus E_4.einrichtung 1 B s1 (toggleUpdate B s1) ticketPlan
      ⟨[], []⟩ s2 :=
    e4_sperrAus rfl rfl rfl (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) h2 (.nil _)
  have h3 : SperrSchritt .ticket C4 (s2.sperren ()) ⟨none, [A, B, C4]⟩ := .ticket (fun h => nomatch h) (by decide)
  let s3 := { toggleUpdate C4 s2 with
    sperren := Function.update s2.sperren () ⟨none, [A, B, C4]⟩ }
  have aus3 : FuehrtSchrittAus E_4.einrichtung 2 C4 s2 (toggleUpdate C4 s2) ticketPlan
      ⟨[], []⟩ s3 :=
    e4_sperrAus rfl rfl rfl (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) h3 (.nil _)
  have h4 : SperrSchritt .nehmen A (s3.sperren ()) ⟨some A, [B, C4]⟩ := .nehmen (.frei A [B, C4])
  obtain ⟨es4, g4, mem4⟩ := e4_sperrSpeicher s4_0_graph_gut.1 s4_0_graph_gut.2 A .rmw
  have good4 := mem4.viele.gut s4_0_graph_gut.1 s4_0_graph_gut.2
  let s4 := { s3 with
    sperren := Function.update s3.sperren () ⟨some A, [B, C4]⟩, graph := g4 }
  have aus4 : FuehrtSchrittAus E_4.einrichtung 3 A s3 (s3) nehmenPlan
      ⟨es4, []⟩ s4 :=
    e4_sperrAus rfl rfl rfl (e4_frame s3) h4 mem4
  have h7 : SperrSchritt .geben A (s4.sperren ()) ⟨some B, [C4]⟩ := .geben (.besitzer A [B, C4])
  obtain ⟨es7, g7, mem7⟩ := e4_sperrSpeicher good4.1 good4.2 A .rmw
  have good7 := mem7.viele.gut good4.1 good4.2
  let s7 := { s4 with
    sperren := Function.update s4.sperren () ⟨some B, [C4]⟩, graph := g7 }
  have aus7 : FuehrtSchrittAus E_4.einrichtung 6 A s4 (s4) wGebenPlan
      ⟨es7, []⟩ s7 :=
    e4_sperrAus rfl rfl rfl (e4_frame s4) h7 mem7
  have h8 : SperrSchritt .geben B (s7.sperren ()) ⟨some C4, []⟩ := .geben (.besitzer B [C4])
  obtain ⟨es8, g8, mem8⟩ := e4_sperrSpeicher good7.1 good7.2 B .rmw
  have good8 := mem8.viele.gut good7.1 good7.2
  let s8 := { s7 with
    sperren := Function.update s7.sperren () ⟨some C4, []⟩, graph := g8 }
  have aus8 : FuehrtSchrittAus E_4.einrichtung 7 B s7 (s7) wGebenPlan
      ⟨es8, []⟩ s8 :=
    e4_sperrAus rfl rfl rfl (e4_frame s7) h8 mem8
  have h9 : SperrSchritt .geben C4 (s8.sperren ()) .frei := .geben (.besitzer C4 [])
  obtain ⟨es9, g9, mem9⟩ := e4_sperrSpeicher good8.1 good8.2 C4 .schreiben
  let s9 := { s8 with
    sperren := Function.update s8.sperren () .frei, graph := g9 }
  have aus9 : FuehrtSchrittAus E_4.einrichtung 8 C4 s8 (s8) wGebenPlan
      ⟨es9, []⟩ s9 :=
    e4_sperrAus rfl rfl rfl (e4_frame s8) h9 mem9
  let z : Nat → Zustand Unit Unit Unit Unit Bool Unit
    | 0 => s0
    | 1 => s1
    | 2 => s2
    | 3 => s3
    | 4 => s4
    | 5 => s4
    | 6 => s4
    | 7 => s7
    | 8 => s8
    | _ + 9 => s9
  let tail (t : Nat) := if t % 3 = 0 then A else if t % 3 = 1 then B else C4
  let spur : Nat → SchrittWahl Unit × SchrittSpur Unit Unit
    | 0 => (.kontext A (), ⟨[], []⟩)
    | 1 => (.kontext B (), ⟨[], []⟩)
    | 2 => (.kontext C4 (), ⟨[], []⟩)
    | 3 => (.kontext A (), ⟨es4, []⟩)
    | 4 => (.kontext B (), ⟨[], []⟩)
    | 5 => (.kontext C4 (), ⟨[], []⟩)
    | 6 => (.kontext A (), ⟨es7, []⟩)
    | 7 => (.kontext B (), ⟨es8, []⟩)
    | 8 => (.kontext C4 (), ⟨es9, []⟩)
    | t + 9 => (.kontext (tail (t + 9)) (), ⟨[], []⟩)
  have tailReady (t : Nat) : KannSchreiten hw4 t (tail t) s9 := by
    refine ⟨t % 3, hw4_opp t, ?_, rfl⟩
    have hr : t % 3 < 3 := Nat.mod_lt _ (by decide)
    have hc : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases hc with h | h | h <;> simp only [tail, h, ↓reduceIte] <;> rfl
  have step (t : Nat) : ImplSchritt E_4.einrichtung E_4.system E_4.katalog hw4
      t (z t) (spur t) (z (t + 1)) := by
    match t with
    | 0 =>
      exact .kontext (c := A) (hw4_crash 0) ⟨0, hw4_opp 0, rfl, rfl⟩
        (e4_impl_ticket statisch4_A h1) aus1
    | 1 =>
      exact .kontext (c := B) (hw4_crash 1) ⟨1, hw4_opp 1, rfl, rfl⟩
        (e4_impl_ticket statisch4_B h2) aus2
    | 2 =>
      exact .kontext (c := C4) (hw4_crash 2) ⟨2, hw4_opp 2, rfl, rfl⟩
        (e4_impl_ticket statisch4_C h3) aus3
    | 3 =>
      exact .kontext (c := A) (hw4_crash 3) ⟨0, hw4_opp 3, rfl, rfl⟩
        (e4_impl_nehmen statisch4_A h4) aus4
    | 4 =>
      exact e4_implStutter 4 B s4 ⟨1, hw4_opp 4, rfl, rfl⟩
    | 5 =>
      exact e4_implStutter 5 C4 s4 ⟨2, hw4_opp 5, rfl, rfl⟩
    | 6 =>
      exact .kontext (c := A) (hw4_crash 6) ⟨0, hw4_opp 6, rfl, rfl⟩
        (e4_impl_geben (.besitzer A [B, C4])) aus7
    | 7 =>
      exact .kontext (c := B) (hw4_crash 7) ⟨1, hw4_opp 7, rfl, rfl⟩
        (e4_impl_geben (.besitzer B [C4])) aus8
    | 8 =>
      exact .kontext (c := C4) (hw4_crash 8) ⟨2, hw4_opp 8, rfl, rfl⟩
        (e4_impl_geben (.besitzer C4 [])) aus9
    | t + 9 => exact e4_implStutter (t + 9) (tail (t + 9)) s9 (tailReady _)
  let ρ : Maschine.Lauf E_4 := ⟨start, hw4, ⟨fun t => some (z t), fun t => some (spur t),
    fun t => .schritt rfl (.schritt (step t))⟩⟩
  have release (b : Nat) (c : Kontext) (own : ((z b).sperren ()).besitzer = some c) :
      ∃ r, b ≤ r ∧ r + 1 ≤ b + 3 ∧
        ((z r).sperren ()).Gibt c ((z (r + 1)).sperren ()) ∧
        ((z (r + 1)).sperren ()).besitzer ≠ some c := by
    revert own
    match b with
    | 0 => intro own; cases own
    | 1 => intro own; cases own
    | 2 => intro own; cases own
    | 3 => intro own; cases own
    | 4 =>
      intro own
      change some A = some c at own
      obtain rfl := Option.some.inj own
      exact ⟨6, by decide, by decide, .besitzer A [B, C4], by decide⟩
    | 5 =>
      intro own
      change some A = some c at own
      obtain rfl := Option.some.inj own
      exact ⟨6, by decide, by decide, .besitzer A [B, C4], by decide⟩
    | 6 =>
      intro own
      change some A = some c at own
      obtain rfl := Option.some.inj own
      exact ⟨6, by decide, by decide, .besitzer A [B, C4], by decide⟩
    | 7 =>
      intro own
      change some B = some c at own
      obtain rfl := Option.some.inj own
      exact ⟨7, by decide, by decide, .besitzer B [C4], by decide⟩
    | 8 =>
      intro own
      change some C4 = some c at own
      obtain rfl := Option.some.inj own
      exact ⟨8, by decide, by decide, .besitzer C4 [], by decide⟩
    | _ + 9 => intro own; cases own
  have state (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
      (eq : ρ.zeit.zustand t = some s) : z t = s := Option.some.inj eq
  have halteschranke : HalteSchranken E_4 ρ := by
    intro l c b n live
    cases l
    intro H hb
    have hH : H = 5 := Option.some.inj (hb.symm.trans e4halten)
    subst H
    have cost : Kontextkosten ρ c b n ≤ n := zaehle_le _ _ _
    by_contra! over
    obtain ⟨s, hs, ho⟩ := live b (Nat.le_refl _) (by omega)
    rw [← state b s hs] at ho
    obtain ⟨r, hr, hbound, _, hchange⟩ := release b c ho
    obtain ⟨s', hs', ho'⟩ := live (r + 1) (by omega) (by omega)
    rw [← state (r + 1) s' hs'] at ho'
    exact hchange ho'
  refine ⟨E_4, Gabbro.Core.Fortschritt.h4, ρ, C4, 5, 4, akzeptiert_E_4,
    ⟨fair4.hardware, fair4.konform, hstart, rfl⟩, fair4, halteschranke, e4halten,
    ⟨s4, rfl, ⟨A, rfl, by decide⟩, rfl⟩, ?_, ?_, ?_⟩
  · intro s hs
    rw [← state 4 s hs]
    exact (by decide : [B, C4].Nodup)
  · intro k _ hk
    have impossible : (spur k).1 ≠ .absturz := by
      match k with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | _ + 9 => intro hh; cases hh
    exact impossible (congrArg Prod.fst (Option.some.inj hk))
  · intro c b s _ hs ho
    rw [← state b s hs] at ho
    obtain ⟨r, hr, hb, hg, _⟩ := release b c ho
    exact ⟨r, hr, ⟨z r, z (r + 1), rfl, rfl, hg⟩,
      Nat.le_trans (zaehle_le _ _ _) (by omega)⟩

end Gabbro.Core.Fortschritt
