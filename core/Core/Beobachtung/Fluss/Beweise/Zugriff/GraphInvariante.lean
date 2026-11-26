/-
  The single-run invariant that closes `SpeicherGraphKopplungAussage`. For a public cell, `HatQuelle` of
  the graph at a cut equals a public write of that cell observed since the last crash boundary. The
  statement is pinned; this module proves it by induction over the cut. A step either only appends the
  writes of `spur.speicher` to the graph and to the trace (context, answer, interrupt), or resets both
  (crash), or appends nothing (pause).
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeobSchrittAnalyse
public import Core.Beobachtung.Fluss.Beweise.Zugriff.Hilfen
public import Core.Beobachtung.Fluss.Erfuellbar
public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl Plan)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L] [DecidableEq Ort]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- **The single-run memory-graph invariant**: for a cell at a cut, a recorded write in the graph
    exists exactly when the low trace contains a public write of that cell after the last crash
    boundary. The graph is rebuilt at every crash but the trace keeps its earlier writes, which is why
    the observation side counts only writes since the last boundary. -/
def SpeicherGraphInvariantAussage : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) {h : Umgebung} {ρ : Lauf (p.einheit plattform)},
    Laeufe (p.einheit plattform) h ρ → ∀ (predictor : Praediktor) (t : Nat) (x : Ast.Semantik.Zelle),
      match ρ.zeit.zustand t with
      | none => True
      | some s =>
        HatQuelle s.graph x ↔
          SchreibSeitAbsturz x (NiedrigeBeob (p.einheit plattform) ρ predictor t)

/-- The premises of the invariant occur jointly: an admitted fragment run exists. -/
theorem SpeicherGraphInvariantAussage_erfuellbar :
    ∃ (p : Fragment) (plattform : Plattform) (h : Umgebung) (ρ : Lauf (p.einheit plattform)),
      Laeufe (p.einheit plattform) h ρ := by
  obtain ⟨h, ρ, _vor, _, vergleich, _, _, _, _⟩ :=
    fragment_ni_form_erfuellbar (Befehl.literal 0 0)
      (by simp only [Befehl.Privat, Befehl.klasse, true_or])
  exact ⟨Fragment.einzel (Befehl.literal 0 0), .x86_64, h, ρ, vergleich.links⟩

/-- The bound to the last crash is necessary: a write before a crash is in the full trace but not
    counted after the boundary, exactly as the graph is rebuilt empty at the crash. -/
theorem SpeicherGraphInvariantAussage_nichtTrivial :
    ∃ (x : Ast.Semantik.Zelle)
      (schreib crash : NiedrigesEreignis Ast.Semantik.Zelle Int PUnit Befehl),
      SchreibBeob x schreib ∧ AbsturzBeob crash = true ∧
      ¬ SchreibSeitAbsturz x [schreib, crash] ∧
      ∃ e ∈ ([schreib, crash] : List (NiedrigesEreignis Ast.Semantik.Zelle Int PUnit Befehl)),
        SchreibBeob x e := by
  let x : Ast.Semantik.Zelle := .region 0 0
  let schreib : NiedrigesEreignis Ast.Semantik.Zelle Int PUnit Befehl :=
    .speicher (SpeicherAkteur.initial x) Gabbro.Core.Speicher.Art.schreiben x
      Gabbro.Core.Speicher.Modus.na none (some 0)
  let crash : NiedrigesEreignis Ast.Semantik.Zelle Int PUnit Befehl :=
    .katalog (.persistenz .crash)
  refine ⟨x, schreib, crash, ?_, ?_, ?_, ?_⟩
  · simp only [schreib, SchreibBeob]
  · simp only [crash, AbsturzBeob]
  · simp only [schreib, crash, SchreibSeitAbsturz, AbsturzBeob, HatAbsturz, SchreibBeob,
      Bool.true_or, Bool.false_or]
    intro hfalse
    exact hfalse
  · refine ⟨schreib, ?_, ?_⟩
    · simp only [List.mem_cons, eq_self_iff_true, true_or]
    · simp only [schreib, SchreibBeob]

/-- One non-crash step preserves the invariant: the graph gains exactly the writes of `spur.speicher`
    (`hatQuelle_nach_viele`) and the observation gains exactly those same writes
    (`schrittBeob_analyse`). -/
private theorem schritt_schliesst {ρ : Lauf E} {predictor : Praediktor} {t : Nat}
    {s n : Zustand L Ort Wert Raum Lok Grund} {wahl : SchrittWahl Wahl}
    {spur : SchrittSpur Ort Wert} {x : Ort}
    (hz : ρ.zeit.zustand t = some s) (hn : ρ.zeit.zustand (t + 1) = some n)
    (hspur : ρ.zeit.spur t = some (wahl, spur))
    (ihq : HatQuelle s.graph x ↔ SchreibSeitAbsturz x (NiedrigeBeob E ρ predictor t))
    (hv : s.graph.Viele spur.speicher n.graph)
    (hpub : ∀ y : Ort, oeffentlich (E.etiketten.ort y) = true)
    (hkeinCrash : ∀ e ∈ spur.aussen, e ≠ .persistenz .crash) :
    HatQuelle n.graph x ↔ SchreibSeitAbsturz x (NiedrigeBeob E ρ predictor (t + 1)) := by
  change HatQuelle n.graph x ↔
    SchreibSeitAbsturz x (NiedrigeBeob E ρ predictor t ++ schrittBeob ρ predictor t)
  have hq := hatQuelle_nach_viele hv x
  rw [hq, ihq]
  have han := schrittBeob_analyse (E := E) (ρ := ρ) (predictor := predictor) (t := t)
    (s := s) (n := n) (wahl := wahl) (spur := spur) (x := x) hz hn hspur hpub hkeinCrash
  rw [SchreibSeitAbsturz_append]
  constructor
  · intro h
    rcases h with hp | hW
    · exact Or.inr ⟨han.1, hp⟩
    · exact Or.inl (han.2.mpr hW)
  · intro h
    rcases h with hb | hrest
    · exact Or.inr (han.2.mp hb)
    · exact Or.inl hrest.2

theorem speicherGraphInvariant : SpeicherGraphInvariantAussage := by
  intro p plattform h ρ lauf predictor t
  induction t with
  | zero =>
    intro x
    let E := p.einheit plattform
    cases hz0 : ρ.zeit.zustand 0 with
    | none => simp only
    | some s =>
      have hload := lauf.2.2.2
      have hgel := fragment_geladen p plattform lauf.1 lauf.2.2.1
      have hs : s = (I.start E ρ.start).2 := Option.some.inj (hz0.symm.trans (hload.trans hgel))
      have hgraphLeer : s.graph = Speicher.Zustand.leer := by
        rw [hs]
        simp only [I.start, Zustand.start]
      simp only [NiedrigeBeob, NiedrigeBeob.praefix, hz0]
      rw [hgraphLeer]
      constructor
      · intro hq
        exfalso
        rcases hq with ⟨i, hi, _hs, _ho⟩
        simp only [Speicher.Zustand.leer] at hi
        exact (Nat.not_lt_zero i) hi
      · intro hs2
        exfalso
        simpa only [SchreibSeitAbsturz, AbsturzBeob, HatAbsturz, SchreibBeob, or_false] using hs2
  | succ t ih =>
    intro x
    cases hzt : ρ.zeit.zustand t with
    | none =>
      have takt := ρ.zeit.takt t
      rw [hzt] at takt
      cases takt with
      | wartet label gleich _ =>
        cases hnt : ρ.zeit.zustand (t + 1) with
        | none => simp only
        | some n =>
          rw [gleich] at hnt
          cases hnt
      | schritt label step =>
        cases step
    | some s =>
      cases hnt : ρ.zeit.zustand (t + 1) with
      | none => simp only
      | some n =>
        have ihq0 := ih x
        rw [hzt] at ihq0
        cases hspur : ρ.zeit.spur t with
        | none =>
          have hgle := ρ.zeit.wartet hspur
          rw [hnt, hzt] at hgle
          have hn_eq : n = s := Option.some.inj hgle.1
          rw [beob_pause ρ predictor t hspur]
          rw [hn_eq]
          exact ihq0
        | some ev =>
          rcases ev with ⟨wahl, spur⟩
          have takt := ρ.zeit.takt t
          rw [hspur, hzt, hnt] at takt
          cases takt with
          | wartet label _ _ => cases label
          | schritt label step =>
            cases label
            cases step with
            | schritt impl =>
              let E := p.einheit plattform
              have hpub : ∀ y : Ast.Semantik.Zelle,
                  oeffentlich (E.etiketten.ort y) = true :=
                fun y => fragment_zelle_oeffentlich p plattform y
              cases impl with
              | kontext keinAbsturz bereit regel aus =>
                rename_i uL planL cL wL
                have hv : s.graph.Viele spur.speicher n.graph := aus.viele
                rcases aus with ⟨_rahmen, _liest, _sperren, _v, faus, _folge, _state⟩
                have hkeinCrash : ∀ e ∈ spur.aussen, e ≠ .persistenz .crash := by
                  have haussen : spur.aussen = [] ∨ ∃ q, spur.aussen = [.frage q] := by
                    generalize hAktion : planL.aktion = aktion at faus
                    generalize hAus : spur.aussen = aussen at faus
                    cases faus with
                    | intern => exact Or.inl rfl
                    | warte => exact Or.inl rfl
                    | sperre => exact Or.inl rfl
                    | frage q => exact Or.inr ⟨_, rfl⟩
                    | verbrauche => exact Or.inl rfl
                    | rueckkehr => exact Or.inl rfl
                    | starte => exact Or.inl rfl
                    | verbinde => exact Or.inl rfl
                    | beende => exact Or.inl rfl
                    | wechsle => exact Or.inl rfl
                  rcases haussen with hleer | ⟨_q, hfrag⟩
                  · rw [hleer]
                    intro e he
                    cases he
                  · rw [hfrag]
                    intro e he hs
                    simp only [List.mem_singleton] at he
                    cases he
                    cases hs
                exact schritt_schliesst (E := E) (ρ := ρ) (predictor := predictor) (t := t)
                  hzt hnt hspur ihq0 hv hpub hkeinCrash
              | antwort keinAbsturz h =>
                have hv : s.graph.Viele spur.speicher n.graph := h.viele
                have hkeinCrash : ∀ e ∈ spur.aussen, e ≠ .persistenz .crash := by
                  obtain ⟨haussen, _⟩ := h.ankunft
                  rw [haussen]
                  intro e he hs
                  simp only [List.mem_singleton] at he
                  cases he
                  cases hs
                exact schritt_schliesst (E := E) (ρ := ρ) (predictor := predictor) (t := t)
                  hzt hnt hspur ihq0 hv hpub hkeinCrash
              | interrupt keinAbsturz h =>
                have hv : s.graph.Viele spur.speicher n.graph := h.viele
                rcases h with ⟨_k, _irq, _c, _nmi, _offer, _pending, _nimmt, _stat, haussen,
                  _folge, _state⟩
                have hkeinCrash : ∀ e ∈ spur.aussen, e ≠ .persistenz .crash := by
                  rw [haussen]
                  intro e he hs
                  simp only [List.mem_singleton] at he
                  cases he
                  cases hs
                exact schritt_schliesst (E := E) (ρ := ρ) (predictor := predictor) (t := t)
                  hzt hnt hspur ihq0 hv hpub hkeinCrash
              | absturz crash =>
                have hgraphLeer : n.graph = Speicher.Zustand.leer := by
                  rw [crash.genau.2]
                  simp only [Zustand.wiederanlauf, Zustand.start]
                have hqLeer : ¬ HatQuelle n.graph x := by
                  rw [hgraphLeer]
                  rintro ⟨i, hi, _hs, _ho⟩
                  simp only [Speicher.Zustand.leer] at hi
                  exact (Nat.not_lt_zero i) hi
                have hspurCrash : ρ.zeit.spur t = some (.absturz, absturzSpur) := by
                  rw [crash.genau.1] at hspur
                  exact hspur
                have hab := schrittBeob_absturz E (ρ := ρ) (predictor := predictor) (t := t)
                  hzt hnt hspurCrash (x := x)
                change HatQuelle n.graph x ↔
                  SchreibSeitAbsturz x (NiedrigeBeob E ρ predictor t ++ schrittBeob ρ predictor t)
                rw [SchreibSeitAbsturz_append]
                constructor
                · intro hq
                  exact False.elim (hqLeer hq)
                · intro h
                  rcases h with hb | hrest
                  · exact False.elim (hab.2 hb)
                  · exact False.elim (hrest.1 hab.1)

end Gabbro.Core.Beobachtung
