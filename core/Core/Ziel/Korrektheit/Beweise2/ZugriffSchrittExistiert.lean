/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/ZugriffSchrittExistiert.lean
  Subject:   THE PINNED LIVENESS STATEMENT `ZugriffSchrittExistiertAussage` (`Core/Ziel/
             Korrektheit/Zugriff`) DOES NOT HOLD as stated, and the missing premise is identified.
             The statement quantifies over every access form `z`. An update form at the plain mode
             (`tausche`, `holeUndAddiere` with `na`) is one such form: when the state grants the
             access, its only ideal step records an `rmw` event at `na`, which no RC11-consistent
             memory extension accepts (`Wohlgeformt.rmw_nicht_na`). The checker refuses those forms
             (`pruefeZugriffsform`), so adding `z.wohlgeformt` to the premise is the strengthening
             that makes the statement true. No statement is changed: the negation and a sharp
             obstruction theorem are new declarations only.
-/
module

public import Core.Ziel.Korrektheit.Zugriff
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Bestimmt
public import Core.Speicher.Graphmaschine

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Speicher
open Gabbro.Core.Speicher.Zustand (getElem_angehaengt_neu)

namespace ZugriffSchritt

variable {Ort Wert : Type}

/-- An `rmw` event at the plain mode cannot be appended to any consistent memory graph. This is the
    operational form of `Wohlgeformt.rmw_nicht_na`. -/
theorem rmw_na_keine_speicherfolge
    {anfang : Ort → Wert} {f : SpeicherAkteur Ort} {g : SpeicherGraph Ort Wert}
    {ort : Ort} {v w : Wert} {es : List (SpeicherAkteur Ort × Etikett Ort Wert)}
    {g' : SpeicherGraph Ort Wert}
    (h : Speicherfolge anfang f g [⟨.rmw, ort, .na, v, w⟩] es g') : False := by
  cases h with
  | @cons _ g₀ _ _ _ _ _ _ vor hs nach =>
    cases nach with
    | nil =>
      let n := g₀.ev.length
      have hlen : g'.ev.length = g₀.ev.length + 1 := by
        rw [hs.ev, List.length_append, List.length_singleton]
      have hn : n < g'.ev.length := by rw [hlen]; exact Nat.lt_succ_self _
      have evN : g'.ev[n]'hn = ⟨f, (⟨.rmw, ort, .na, v, w⟩ : Etikett Ort Wert)⟩ :=
        getElem_angehaengt_neu hs.ev (by rw [hlen]; exact Nat.lt_succ_self _)
      have labN : g'.graph.lab ⟨n, hn⟩ = (⟨.rmw, ort, .na, v, w⟩ : Etikett Ort Wert) :=
        congrArg Ereignis.lab evN
      have istRmw : g'.graph.istRmw ⟨n, hn⟩ := by
        change (g'.graph.lab ⟨n, hn⟩).art = .rmw
        rw [labN]
      have modusNa : g'.graph.modus ⟨n, hn⟩ = .na := by
        change (g'.graph.lab ⟨n, hn⟩).modus = .na
        rw [labN]
      exact (hs.konsistent.wf.rmw_nicht_na ⟨n, hn⟩ istRmw) modusNa

end ZugriffSchritt

open Gabbro.Core.Ast.Semantik

/-- The pinned liveness statement is false: a checker-refused update form at the plain mode is still a
    possible head, and with authority its granted ideal step records an event the memory model cannot
    append. The missing premise is `z.wohlgeformt`. -/
theorem zugriffSchrittExistiert_widerlegt : ¬ ZugriffSchrittExistiertAussage := by
  intro h
  let z : Zugriffsform := .tausche 0 0 0 0 (Ast.Ty.int 0 0) .na
  let p : Fragment := Fragment.einzel (.zugriff z)
  let platform : Katalog.Plattform := .x86_64
  let c : Kontext := eintritt
  let r : Rahmen := { Leerzustand.lokal c with
    temp := fun slot => if slot = 0 then anfangswert (Ast.Ty.int 0 0) else none
    arrivalRegions := [⟨0, 1⟩] }
  let s : Zustand := { Leerzustand with
    lokal := Function.update Leerzustand.lokal c r
    rechte := ⟨fun _ => true, fun _ => 0⟩
    buchung := { Leerzustand.buchung with
      umfang := fun o => if o = 0 then [Zelle.region 0 0] else []
      haelt := fun d g recht => d = c ∧ g.objekt = 0 ∧ (recht = .lesen ∨ recht = .schreiben) } }
  have gut : s.SpeicherGut := by
    change Speicher.Zustand.leer.graph.Konsistent ∧ Speicher.Zustand.leer.graph.Vollstaendig
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  have kopf : (p.einheit platform).system.kopf s c = some (.zugriff z) := by rfl
  obtain ⟨_, plan, u, es, g, step, folge⟩ := h p platform z s c kopf gut
  have hg : (Befehl.zugriff z).form.klasse.befugt
      ((Befehl.zugriff z).form.operand (s.lokal c)) s c := by
    change s.befugt c (Zelle.region 0 0) .lesen ∧ s.befugt c (Zelle.region 0 0) .schreiben
    constructor <;>
      refine ⟨⟨0, 0⟩, 0, ?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp only [s, r, Zustand.griff, Function.update_self, decide_true, Rechte.Gueltig,
        Leihe.Zugriff, List.getElem?_cons_zero, Zelle.objekt, List.length_singleton,
        Nat.reduceLT, ↓reduceIte, Leerzustand, Zustand.start, true_and, or_true, or_false, reduceCtorEq]
  have stepZ := (zugriff_ideal_zugriffsschritt z c s () [plan] u).1 step
  rcases stepZ with ⟨hng, _, _⟩ | ⟨_, v, _, hp, _⟩
  · exact (hng hg).elim
  have planEq : plan = (Befehl.zugriff z).form.plan (s.lokal c) v := (List.cons.inj hp).1
  rw [planEq] at folge
  simp only [z, Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.klasse,
    Zugriffsform.operand, Rahmen.zugriffOperand, Schrittform.plan,
    Wirkungsklasse.plan, Aenderung.art, Aenderung.schreibt, schreibEreignisse,
    List.filter_nil, List.map_nil, List.nil_append, List.append_nil] at folge
  exact ZugriffSchritt.rmw_na_keine_speicherfolge folge

end Gabbro.Core.Ziel.Korrektheit
