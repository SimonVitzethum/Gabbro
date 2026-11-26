module

public import Core.Linken.Offen
public import Core.Linken.Aussage
public import Core.Linken.DeckungsZustand
public import Core.Annahme.AussenLauf
public import Core.Annahme.Klauseln
public import Core.Annahme.Waechter
public import Core.Annahme.Schranken
public import Core.Beobachtung.Fluss.Quellfragment
public import Core.Ast.Semantik.Runtime.Mehrkontext.System

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- The open run surgery: every guard use of a run of the linked whole is covered by a run of some
    module that starts at an entry state and reports the same operation with the same operands.
    The projection of a whole run onto a module and the relocation of its entries is the missing
    step; it is pinned here and not proved. -/
def OffeneLaufChirurgieAussage (plan : Bauplan) : Prop :=
  ∀ (frag : Fragment), linke plan = some frag →
    ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
      (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
      (kanonischeVerwendung _).bedarf ρ t op args →
      ∃ m ∈ plan.module, ∃ (hw : HwLauf)
        (ρm : Zeitlauf (I.Schritt (m.fragment.einheit plan.plattform).einrichtung
          (m.fragment.einheit plan.plattform).system
          (m.fragment.einheit plan.plattform).katalog hw)),
        Eintrittszustand m (ρm.zustand 0) ∧
        ∃ (tm : ρm.Schnitt),
          (m.fragment.einheit plan.plattform).quelltabellen.guard (ρm.zustand tm.val) op args

/-- The guard conjunct from open parts: the surgery attributes every guard use of the whole to a
    run of some module starting at an entry state, and that module's open acceptance discharges it. -/
theorem offener_guard_haelt (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hoff : ∀ m ∈ plan.module, OffenAkzeptiertAussage m plan.plattform)
    (hchir : OffeneLaufChirurgieAussage plan)
    (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
    (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op)
    (need : (kanonischeVerwendung _).bedarf ρ t op args) :
    waechterBedarf op args := by
  obtain ⟨m, hm, hw, ρm, hentry, tm, needm⟩ := hchir frag hlink ρ hρ t op args need
  exact hoff m hm _ hentry _ ρm rfl tm op args needm

/-- A linked whole is accepted when every part is openly accepted: the catalogue, rule, outside,
    flow, bound and wait-free conjuncts hold for every sealed linked whole without any part
    acceptance, and the guard conjunct follows from the open run surgery. -/
theorem linker_akzeptiert_aus_offen (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat)
    (hoff : ∀ m ∈ plan.module, OffenAkzeptiertAussage m plan.plattform)
    (hchir : OffeneLaufChirurgieAussage plan) :
    Akzeptiert (frag.einheit plan.plattform) := by
  have hguard : ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
      (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
      (kanonischeVerwendung _).bedarf ρ t op args → waechterBedarf op args :=
    offener_guard_haelt plan frag hlink hoff hchir
  obtain ⟨hok, rfl⟩ := linke_eq_some hlink
  have hcompat : annahmenKompatibel plan = true := by
    simp only [bauplanOk] at hok
    rw [Bool.and_eq_true] at hok
    rw [Bool.and_eq_true] at hok
    exact hok.1.2
  have hklauseln : (verknuepfteFragmente plan).klauseln = .leer :=
    verknuepfte_klauseln_leer hcompat
  let E := (verknuepfteFragmente plan).einheit plan.plattform
  have hdom : DomaenenLokal E := by
    refine ⟨eineTabelle_akzeptiert,
      fun s c i hkopf _ _ _ _ _ w _ spur himpl haus => ?_⟩
    have head' : kopf (verknuepfteFragmente plan).code s c = some i := hkopf
    have hpriv_i := hpriv i (kopf_mem head')
    obtain ⟨rfl, _⟩ := i.vollzug_genau (w := w) himpl haus hpriv_i
    exact spurRespektiert_leer _ _ _
  refine ⟨⟨Plattform.katalog_wohlgeformt plan.plattform, fun b => Befehl.regelLokal _ _ b,
    ⟨Aussen.zulassung_m2 _, ?_⟩, Beobachtung.fragment_fluss_lokal _ _ hpriv,
    schrankenLokal_leer (E := E) rfl rfl rfl,
    abschnittWartefrei_ohne_blockade E (fun _ _ _ hb => hb), hdom⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, head, transfer⟩ := rule
      have head' : kopf (verknuepfteFragmente plan).code s c = some b := head
      obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) transfer execute
        (hpriv b (kopf_mem head'))
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · intro run conforms
    change (∀ pred ∈ (verknuepfteFragmente plan).klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ (verknuepfteFragmente plan).klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ (verknuepfteFragmente plan).klauseln.sicher, _
    rw [hklauseln]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t op args need
      exact hguard run conforms t op args need
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

/-- The defining module passes the open checker row: no guard past the definition header. -/
theorem modulDef_offenOk : modulOffenOk modulDef = true := by
  rfl

/-- The calling module passes the open checker row: a call carries no guard. -/
theorem modulCall_offenOk : modulOffenOk modulCall = true := by
  rfl

/-- The example parts are openly accepted: both pass the open checker row. -/
theorem beispiel_offen :
    ∀ m ∈ beispielPlan.module, OffenAkzeptiertAussage m beispielPlan.plattform := by
  intro m hm
  simp only [beispielPlan, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact modulOffenOk_korrekt modulDef _ modulDef_offenOk
  · exact modulOffenOk_korrekt modulCall _ modulCall_offenOk

/-- The open run surgery is satisfiable: the guard-free example plan has no guard use to cover. -/
theorem offeneLaufChirurgie_erfuellbar : ∃ plan, OffeneLaufChirurgieAussage plan := by
  refine ⟨beispielPlan, ?_⟩
  intro frag hlink ρ hρ t op args need
  obtain ⟨hok, hfrag⟩ := linke_eq_some hlink
  subst hfrag
  rw [bedarf_ist_zustandsBedarf] at need
  obtain ⟨c, b, head, g⟩ := need
  have hmem : b ∈ beispielFragment.code := kopf_mem head
  have gnone : b.guard ((ρ.zeit.zustand t.val).lokal c) = none :=
    beispielGuard b hmem _
  rw [gnone] at g
  cases g

end Gabbro.Core.Linken
