module

public import Core.Ast.Semantik.Elaborierung
public import Core.Annahme
public import Core.Ideal.Komposition
public import Core.Verfeinerung.Maschine
public import Core.Maschine.Einheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog
open Ideal (RegelBestimmt RegelFortschritt)

theorem Befehl.lokal (E : Einheit) (b : Befehl) (rule : E.system.regel b = b.regel)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) : RegelLokal E b := by
  intro c s u w p step
  rw [rule] at step
  obtain ⟨hplan, _⟩ := (b.ideal_privat h c s w [p] u).1 step
  have hp : p = b.plan (s.lokal c) 0 := (List.cons.inj hplan).1
  subst hp
  obtain ⟨hlesen, hfuss⟩ := b.plan_privat_leer h (s.lokal c)
  refine ⟨fun x hx => ?_, fun l hl => ?_⟩
  · rw [hfuss] at hx
    exact (List.not_mem_nil hx).elim
  · rw [hlesen] at hl
    exact (List.not_mem_nil hl).elim

theorem Befehl.bestimmt (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) : RegelBestimmt b.regel :=
  fun c s w es es' s1 s2 left right =>
    let l := (b.ideal_privat h c s w es s1).1 left
    let r := (b.ideal_privat h c s w es' s2).1 right
    ⟨l.1.trans r.1.symm, l.2.trans r.2.symm⟩

theorem Befehl.fortschritt (p : Fragment) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) :
    RegelFortschritt (system p.code) b :=
  fun s c _ => Or.inl ⟨(), [b.plan (s.lokal c) 0], b.nach c s,
    (b.ideal_privat h c s () [b.plan (s.lokal c) 0] (b.nach c s)).2 ⟨rfl, rfl⟩⟩

/-- A frame-only step composes with the protocol: the form supplies the frame and the plan, the
    machine runs the still protocol action of the plan with the empty trace. -/
theorem Befehl.vollzug (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit)
    (b : Befehl) (t : Nat) (c : Kontext) (s : Zustand) (h : b.Privat) :
    FuehrtSchrittAus e t c s (b.nach c s) (b.plan (s.lokal c) 0) ⟨[], []⟩
      (b.maschinennach c s (b.nach c s)) := by
  have hrahmen : Zustandsrahmen s (b.nach c s) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hlesen, hfuss⟩ := b.plan_privat_leer h (s.lokal c)
  have hlleer : ∀ l ∈ (b.plan (s.lokal c) 0).lesen, l.art.liest := by
    intro l hl
    rw [hlesen] at hl
    exact (List.not_mem_nil hl).elim
  have hmem : Speicherfolge s.initial (.kontext c) s.graph
      ([] ++ (b.plan (s.lokal c) 0).lesen ++
        schreibEreignisse (b.plan (s.lokal c) 0).fuss (b.plan (s.lokal c) 0).schreibt
          (b.plan (s.lokal c) 0).modus (b.plan (s.lokal c) 0).wert ++
        (⟨[], []⟩ : SchrittSpur Zelle Int).aussen.map (aussenEtikett e)) [] s.graph := by
    rw [hlesen, hfuss]
    exact Speicherfolge.nil _
  rcases b.plan_privat_aktion h (s.lokal c) with hakt | ⟨_, _, hakt⟩ | ⟨_, hakt⟩ | ⟨_, _, hakt⟩ |
    ⟨_, _, _, hakt⟩
  · unfold FuehrtSchrittAus Befehl.maschinennach
    rw [hakt]
    dsimp only
    exact ⟨hrahmen, hlleer, [], _, FuehrtAus.intern, hmem, rfl⟩
  · unfold FuehrtSchrittAus Befehl.maschinennach
    rw [hakt]
    dsimp only
    exact ⟨hrahmen, hlleer, [], _, FuehrtAus.maskiere _ _, hmem, rfl⟩
  · unfold FuehrtSchrittAus Befehl.maschinennach
    rw [hakt]
    dsimp only
    exact ⟨hrahmen, hlleer, [], _, FuehrtAus.prioritaet _, hmem, rfl⟩
  · unfold FuehrtSchrittAus Befehl.maschinennach
    rw [hakt]
    dsimp only
    exact ⟨hrahmen, hlleer, [], _, FuehrtAus.sende _ _, hmem, rfl⟩
  · unfold FuehrtSchrittAus Befehl.maschinennach
    rw [hakt]
    dsimp only
    exact ⟨hrahmen, hlleer, [], _, FuehrtAus.leite _ _ _, hmem, rfl⟩

theorem Befehl.komponierbar (p : Fragment) (platform : Plattform) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) :
    I.RegelKomponierbar (p.einheit platform).einrichtung (p.einheit platform).system b := by
  intro t s c w plans u _ _ step
  obtain ⟨same, after⟩ : plans = [b.plan (s.lokal c) 0] ∧ u = b.nach c s :=
    (b.ideal_privat h c s w plans u).1 step
  subst u
  exact ⟨b.plan (s.lokal c) 0, ⟨[], []⟩, b.maschinennach c s (b.nach c s), same, b.vollzug _ t c s h⟩

theorem Befehl.vollzug_genau (b : Befehl)
    (h : b.klasse = .lokal ∨ b.klasse = .ruf := by first | exact Or.inl rfl | exact Or.inr rfl)
    {e t c s u w p spur s'} (rule : b.impl c s w [p] u)
    (execute : FuehrtSchrittAus e t c s u p spur s') :
    spur = ⟨[], []⟩ ∧ s' = b.nach c s := by
  have hp : b.Privat := h.elim Or.inl (Or.inr ∘ Or.inl)
  obtain ⟨hplan, hnach⟩ := (b.impl_privat hp c s w [p] u).1 rule
  have hp0 : p = b.plan (s.lokal c) 0 := (List.cons.inj hplan).1
  subst hp0
  subst hnach
  have hakt : (b.plan (s.lokal c) 0).aktion = .intern := by
    rcases h with h | h <;>
      simp only [Befehl.plan, Befehl.form, Schrittform.plan, h, Wirkungsklasse.plan,
        Semantik.plan]
  have hleer : (b.plan (s.lokal c) 0).lesen = [] ∧ (b.plan (s.lokal c) 0).fuss = [] :=
    b.plan_privat_leer hp (s.lokal c)
  obtain ⟨_, _, _, _, action, memory, next⟩ := execute
  cases spur with
  | mk events outside =>
    rw [hakt] at action
    cases action
    rw [hleer.1, hleer.2] at memory
    simp only [schreibEreignisse, List.filter_nil, List.map_nil, List.nil_append, List.append_nil,
      List.map_nil] at memory
    have unchanged : ∀ {recorded graph},
        Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
          recorded = [] ∧ graph = s.graph := by
      intro _ _ run
      cases run
      exact ⟨rfl, rfl⟩
    have hmem := unchanged memory
    rw [hmem.1]
    rw [hmem.2] at next
    exact ⟨rfl, next⟩

/-- A frame-only step leaves the machine trace empty and keeps every still field of the form state:
    the local states, the questions, answers, consumption, history, initial content, graph, booking,
    rights, delivery and leases. The per-core state, the software queue and the routing table are the
    machine's (an interrupt-control step moves them). -/
theorem Befehl.vollzug_genau_privat (b : Befehl) (h : b.Privat)
    {e t c s u w p spur s'} (rule : b.impl c s w [p] u)
    (execute : FuehrtSchrittAus e t c s u p spur s') :
    spur = ⟨[], []⟩ ∧ s'.lokal = u.lokal ∧ s'.status = u.status ∧ s'.fragen = u.fragen ∧
      s'.antworten = u.antworten ∧ s'.verbraucht = u.verbraucht ∧ s'.verlauf = u.verlauf ∧
      s'.initial = u.initial ∧ s'.graph = u.graph ∧ s'.buchung = u.buchung ∧ s'.rechte = u.rechte ∧
      s'.geliefert = u.geliefert ∧ s'.leihen = u.leihen ∧ s'.epoche = u.epoche ∧
      s'.verworfen = u.verworfen ∧ s'.sperren = u.sperren := by
  obtain ⟨hplan, hnach⟩ := (b.impl_privat h c s w [p] u).1 rule
  have hp0 : p = b.plan (s.lokal c) 0 := (List.cons.inj hplan).1
  subst hp0
  subst hnach
  obtain ⟨hlesen, hfuss⟩ := b.plan_privat_leer h (s.lokal c)
  have hstill : (b.plan (s.lokal c) 0).aktion.Still :=
    (b.privat_still_leer h (s.lokal c)).1
  obtain ⟨rahmen, _, _, v, action, mem, stateEq⟩ := execute
  obtain ⟨hsperren, haussen, hlokal, hsperren2, hrechte, _, hfragen, hantworten, hverlauf, hverbraucht,
    hgeliefert, hleihen, hinitial, _, hepoche, hverworfen, hbuchung⟩ := action.still_erhaelt hstill
  have unchanged : ∀ {recorded graph},
      Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
        recorded = [] ∧ graph = s.graph := by
    intro _ _ run
    cases run
    exact ⟨rfl, rfl⟩
  have hsp : spur.speicher = [] ∧ s'.graph = s.graph := by
    rw [hsperren, hlesen, hfuss, haussen] at mem
    simp only [schreibEreignisse, List.filter_nil, List.map_nil, List.nil_append, List.append_nil,
      List.map_nil] at mem
    exact unchanged mem
  have haus : spur.aussen = [] := haussen
  have hgraph : s'.graph = (b.nach c s).graph := hsp.2.trans rahmen.graph.symm
  rcases spur with ⟨evs, aus⟩
  have hevs : evs = [] := hsp.1
  have haus2 : aus = [] := haus
  subst hevs
  subst haus2
  have hstatus : s'.status = (b.nach c s).status := by
    rcases b.plan_privat_aktion h (s.lokal c) with hakt | ⟨_, _, hakt⟩ | ⟨_, hakt⟩ | ⟨_, _, hakt⟩ |
      ⟨_, _, _, hakt⟩ <;>
      rw [hakt] at action <;> cases action <;> rw [stateEq]
  refine ⟨rfl, ?_, hstatus, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [stateEq] <;>
    assumption

theorem Befehl.abgleich (p : Fragment) (platform : Plattform) (b : Befehl) :
    I.RegelAbgleich (p.einheit platform) b := by
  intro hw t c w s u s' i stepPlan spur related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  exact Or.inl ⟨s', .kontext normal ready ⟨b, head, impl⟩ execute, I.ProtokollBezug.refl _, rfl⟩

/-- Every instruction is its unit's single linearisation point. The mover relations
    concern steps strictly before and after that point, so both are empty. -/
def Befehl.vor (_ : Befehl) : Zustand → Zustand → Prop := fun _ _ => False

def Befehl.danach (_ : Befehl) : Zustand → Zustand → Prop := fun _ _ => False

theorem Befehl.kommutation (b : Befehl) (andere : Zustand → Zustand → Prop) :
    Kommutation b.vor b.danach andere :=
  ⟨fun _ _ _ h _ => h.elim, fun _ _ _ _ h => h.elim⟩

theorem Fragment.fertig (p : Fragment) (platform : Plattform) :
    ∀ s c, (p.einheit platform).system.kopf s c = none → (p.einheit platform).system.fertig s c :=
  fun _ _ finished => finished

theorem Fragment.bereit_eindeutig (p : Fragment) (platform : Plattform)
    (step : (p.einheit platform).system.ISchritt c s w plans u) :
    ¬ (p.einheit platform).system.fertig s c ∧ ∀ reason, ¬ (p.einheit platform).system.blockiert s c reason := by
  obtain ⟨b, head, _⟩ := step
  exact ⟨fun finished => (Option.some_ne_none b) (head.symm.trans finished), fun _ blocked => blocked⟩

end Gabbro.Core.Ast.Semantik
