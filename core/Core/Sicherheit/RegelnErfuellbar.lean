module

public import Core.Sicherheit.Lauf
public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Semantik.Runtime.Praedikat
public import Core.Ast.Semantik.Runtime.Atom.Rein
import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog Ast Ast.Semantik

/-- The declared invariants of a checker-accepted table hold at a state whose memory content
    satisfies every declared predicate. -/
private theorem invariantenAusPruefung {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (s : Ast.Semantik.Zustand) (haelt : ∀ q ∈ ps, q.haelt s.initial) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) s := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden _
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  exact haelt q (List.mem_of_getElem? hsome)

/-- Invariants transport across a step that preserves memory content, lock bookings and
    running contexts: from the declared part at `vor` to the declared part at `nach`. -/
private theorem invariantenErhaltenInitial {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (vor nach : Ast.Semantik.Zustand) (hinit : nach.initial = vor.initial)
    (hbuch : nach.buchung = vor.buchung) (hstatus : nach.status = vor.status)
    (vorSicher : InvariantenAmSchnitt (p.sicherheitsEinheit platform) vor) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) nach := by
  obtain ⟨_, deklariert⟩ := vorSicher
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden writersNach
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  rw [← tab, ← List.getElem?_map] at vorhanden
  have writersVor : ∀ c, vor.status c = .laeuft → ¬ vor.buchung.schreibt c i := by
    intro c hc hcon
    have hc' : nach.status c = .laeuft := by
      rw [hstatus]
      exact hc
    have hcon' : nach.buchung.schreibt c i := by
      rw [hbuch]
      exact hcon
    exact writersNach c hc' hcon'
  have vorGilt : q.gilt vor := deklariert i _ vorhanden writersVor
  exact Praedikat.gilt_of_initial q vor nach hinit.symm vorGilt

/-- Invariants transport across an interrupt arrival: the fresh handler context was at rest,
    so its writer scope comes from the post-state alone. -/
private theorem invariantenErhaltenInterrupt {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (vor nach : Ast.Semantik.Zustand) (c : Kontext)
    (hinit : nach.initial = vor.initial) (hbuch : nach.buchung = vor.buchung)
    (hstatus : ∀ c', c' ≠ c → nach.status c' = vor.status c')
    (hnach : nach.status c = .laeuft)
    (vorSicher : InvariantenAmSchnitt (p.sicherheitsEinheit platform) vor) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) nach := by
  obtain ⟨_, deklariert⟩ := vorSicher
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden writersNach
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  rw [← tab, ← List.getElem?_map] at vorhanden
  have writersVor : ∀ c', vor.status c' = .laeuft → ¬ vor.buchung.schreibt c' i := by
    intro c' hc' hcon
    by_cases heq : c' = c
    · subst c'
      have hcon' : nach.buchung.schreibt c i := by
        rw [hbuch]
        exact hcon
      exact writersNach c hnach hcon'
    · have hcNach : nach.status c' = .laeuft := by
        rw [hstatus c' heq]
        exact hc'
      have hcon' : nach.buchung.schreibt c' i := by
        rw [hbuch]
        exact hcon
      exact writersNach c' hcNach hcon'
  have vorGilt : q.gilt vor := deklariert i _ vorhanden writersVor
  exact Praedikat.gilt_of_initial q vor nach hinit.symm vorGilt

private theorem arithmetik_grenzen {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (startOk : ∀ q ∈ ps, q.haelt p.speicher.initial)
    (restartOk : ∀ q ∈ ps, q.haelt (fun _ => 0)) :
    GrenzenSicher (p.sicherheitsEinheit platform) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H start s _ _ h
    change Ast.Semantik.laden p.eingang p.eintritte p.speicher platform start (H.lade Ast.Semantik.bild) = some s at h
    unfold Ast.Semantik.laden at h
    split at h
    · cases h
      refine ⟨rfl, rfl, rfl, ?_⟩
      exact invariantenAusPruefung platform tab _ (fun q hq => startOk q hq)
    · cases h
  · intro hw t a vor spur nach step vorSicher
    obtain ⟨_, _, _, heq⟩ := step
    have hinit : nach.initial = vor.initial := by
      rw [heq]
      try rfl
    have hbuch : nach.buchung = vor.buchung := by
      rw [heq]
      try rfl
    have hstatus : nach.status = vor.status := by
      rw [heq]
      try rfl
    exact invariantenErhaltenInitial platform tab vor nach hinit hbuch hstatus vorSicher
  · intro hw t id vor spur nach step vorSicher
    obtain ⟨k, irq, c, nmi, _, _, _, _, _, _, heq⟩ := step
    have hinit : nach.initial = vor.initial := by
      rw [heq]
      try rfl
    have hbuch : nach.buchung = vor.buchung := by
      rw [heq]
      try rfl
    have hstatus : ∀ c', c' ≠ c → nach.status c' = vor.status c' := by
      intro c' hne
      rw [heq]
      try rfl
      exact Function.update_of_ne hne _ _
    have hnach : nach.status c = .laeuft := by
      rw [heq]
      try rfl
      exact Function.update_self c .laeuft vor.status
    exact invariantenErhaltenInterrupt platform tab vor nach c hinit hbuch hstatus hnach
      vorSicher
  · intro hw t vor spur nach step vorSicher
    have hcrash := (AbsturzSchritt.neustart step).2.2.2.1
    have hwieder : (p.sicherheitsEinheit platform).maschine.einrichtung.wiederanlauf.initial =
        (fun _ _ => 0) := rfl
    have hinit : nach.initial = (fun _ => 0) := by
      rw [hcrash, hwieder]
    exact invariantenAusPruefung platform tab nach (fun q hq => by
      rw [hinit]
      exact restartOk q hq)

private theorem arithmetik_schritt
    (p : Fragment) (platform : Plattform) (hw : HwLauf) (t : Nat)
    (s : Ast.Semantik.Zustand) (b : Befehl)
    (normal : (hw.angebot t).crash = false) (bereit : KannSchreiten hw t eintritt s)
    (kopf : (p.einheit platform).system.kopf s eintritt = some b)
    (priv : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl) :
    Lauffolge (p.einheit platform) hw t (some s) (.kontext eintritt (), ⟨[], []⟩)
      (some (b.nach eintritt s)) :=
  .schritt (.kontext normal bereit
    ⟨b, kopf, (b.impl_privat priv eintritt s () [Ast.Semantik.plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩
    (b.vollzug _ t eintritt s))

/-- The rule and boundary obligations hold jointly for a loaded unit that actually
    executes literals, both binary operators and a local binding. -/
theorem sicherheit_aus_regeln_erfuellbar :
    ∃ (E : Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl)
      (H : Umgebung) (ρ : Lauf E),
      GrenzenSicher E ∧ (∀ f, RegelAntwortSicher E f) ∧ (∀ f, RegelSicher E f) ∧
      Maschine.Laeufe E.maschine H ρ ∧
      ∃ (s : Ast.Semantik.Zustand) (wert : Zahl 7 7), ρ.zeit.zustand 6 = some s ∧
        (s.lokal eintritt).lokale.head? = some (some ⟨.int 7 7, wert⟩) ∧ wert.wert = 7 := by
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : name.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro eq
    cases eq
  let tree := Stmt.letValue (result := none) (scope := []) name ordinary
    (.binary .add (.lit 1) (.binary .mul (.lit 2) (.lit 3)))
  let p := stmt tree
  have keine : p.klauseln.invariant = [] := stmt_keine_invarianten tree
  have tab : p.klauseln.invariant = [].map Praedikat.gilt := by
    simp only [keine, List.map_nil]
  have leer : ∀ q ∈ ([] : List Praedikat), q.haelt p.speicher.initial :=
    fun q hq => (List.not_mem_nil hq).elim
  have leerStart : ∀ q ∈ ([] : List Praedikat), q.haelt (fun _ => 0) :=
    fun q hq => (List.not_mem_nil hq).elim
  have okAll : ∀ b ∈ p.code, pruefeBefehlErhalt [] b = true := by
    intro b _
    rfl
  have okStart : pruefeStart p.speicher.initial [] = true := rfl
  have okRestart : pruefeNeustart [] = true := rfl
  have okCode : p.code.all (pruefeBefehlErhalt []) = true :=
    List.all_eq_true.mpr (fun b _ => rfl)
  have ok : pruefeEinheit p [] = true := by
    simp only [pruefeEinheit, Bool.and_eq_true]
    exact ⟨⟨okStart, okRestart⟩, okCode⟩
  let platform := Plattform.x86_64
  let E := p.sicherheitsEinheit platform
  let H := Umgebung.referenz platform.katalog 1 Laufkonstruktion.leer
  let hw := Umgebung.referenzLauf platform.katalog 1 Laufkonstruktion.leer
  have fair : FairLaeufe platform.katalog H hw :=
    Umgebung.referenz_fair _ _ _ platform.katalog_wohlgeformt (Nat.zero_lt_succ 0)
  obtain ⟨start, admissible⟩ := zulStart_erfuellbar fair.hardware Laufkonstruktion.bild_gueltig
  obtain ⟨kern, zugeordnet⟩ := admissible.2.2.1 0 (Nat.zero_lt_succ 0)
  have kernNull : kern = 0 := Nat.lt_one_iff.mp (admissible.2.2.2.1 0 kern zugeordnet).2
  have assignment : start.assignment 0 = some 0 := kernNull ▸ zugeordnet
  let d := startdaten p.eingang p.eintritte (some 0) platform start.regions
  let z₀ : Ast.Semantik.Zustand := Maschine.Zustand.start d.lokal d.status d.kerne d.rechte
    (Ast.Semantik.einrichtung p.eingang p.eintritte p.speicher).initial
    (.leer (startmedium start))
  have geladen : E.maschine.laden start (H.lade E.maschine.bild) = some z₀ := by
    change Ast.Semantik.laden p.eingang p.eintritte p.speicher platform start (Ast.Semantik.bild.lade) = some z₀
    have image : Ast.Semantik.bild.lade.starts 0 = some 0 ∧
        Ast.Semantik.bild.lade.bytes 0 = some 0 := ⟨rfl, rfl⟩
    rw [Ast.Semantik.laden, if_pos image, assignment]
  let z₁ := (Befehl.literal 0 1).nach eintritt z₀
  let z₂ := (Befehl.literal 1 2).nach eintritt z₁
  let z₃ := (Befehl.literal 2 3).nach eintritt z₂
  let z₄ := (Befehl.binaer .mul 1).nach eintritt z₃
  let z₅ := (Befehl.binaer .add 0).nach eintritt z₄
  let z₆ := (Befehl.binden name 0).nach eintritt z₅
  have z6kopf : ∀ c, E.maschine.system.kopf z₆ c = none := by
    intro c
    by_cases hc : c = Ast.Semantik.eintritt
    · subst hc
      decide
    · have hst : z₆.status c = .ruht := by
        show (if c = Ast.Semantik.eintritt then Status.laeuft else Status.ruht) = _
        rw [if_neg hc]
      simp only [Ast.Semantik.kopf, hst]
  have z6fragen : z₆.fragen = [] := by rfl
  have hwRuhig (t : Nat) : (hw.angebot t).interrupts = [] := rfl
  have hwKeinAbsturz (t : Nat) : (hw.angebot t).crash = false := rfl
  have keinAb6 : ∀ t, KeinSchritt (Lauffolge E.maschine hw) (t + 6) (some z₆) := by
    intro t event next step
    cases step with
    | schritt step =>
      cases step with
      | kontext _ _ regel _ =>
        obtain ⟨_, kopf, _⟩ := regel
        rw [z6kopf _] at kopf
        cases kopf
      | antwort _ arrives =>
        have hq := arrives.1.2.2.2.1
        obtain ⟨q, hmem, _⟩ := hq
        rw [z6fragen] at hmem
        exact List.not_mem_nil hmem
      | interrupt _ enters =>
        obtain ⟨_, _, _, _, _, haus, _⟩ := enters
        have hinter := haus.2.2.1
        rw [hwRuhig _] at hinter
        simp only [List.getElem?_nil, reduceCtorEq] at hinter
      | absturz crash => exact Bool.false_ne_true (hwKeinAbsturz _ |>.symm.trans crash.1.2)
  let rest : Zeitlauf (fun t => Lauffolge E.maschine hw (t + 6)) :=
    { zustand := fun _ => some z₆
      spur := fun _ => none
      takt := fun t => .wartet rfl rfl (keinAb6 t) }
  have ende : rest.zustand 0 = some z₆ := rfl
  have still6 : ∀ t, 6 ≤ t → ∀ s, ρ.zeit.zustand t = some s →
      KeinSchritt (Lauffolge E.maschine hw) t (some s) := by
    intro t ht s hs ev next step
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 6 := ⟨t - 6, by omega⟩
    have hss : s = z₆ := (Option.some.inj hs).symm
    subst hss
    exact keinAb6 m ev next step
  have s₀ := arithmetik_schritt p platform hw 0 z₀ (.literal 0 1) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₁ := arithmetik_schritt p platform hw 1 z₁ (.literal 1 2) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₂ := arithmetik_schritt p platform hw 2 z₂ (.literal 2 3) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₃ := arithmetik_schritt p platform hw 3 z₃ (.binaer .mul 1) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₄ := arithmetik_schritt p platform hw 4 z₄ (.binaer .add 0) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  have s₅ := arithmetik_schritt p platform hw 5 z₅ (.binden name 0) rfl ⟨0, rfl, rfl, rfl⟩ rfl
  let schritt := Lauffolge E.maschine hw
  let abFuenf := voran (schritt := fun t => schritt (t + 5)) rest (some z₅) _ (ende.symm ▸ s₅)
  let abVier := voran (schritt := fun t => schritt (t + 4)) abFuenf (some z₄) _ s₄
  let abDrei := voran (schritt := fun t => schritt (t + 3)) abVier (some z₃) _ s₃
  let abZwei := voran (schritt := fun t => schritt (t + 2)) abDrei (some z₂) _ s₂
  let abEins := voran (schritt := fun t => schritt (t + 1)) abZwei (some z₁) _ s₁
  let zeit := voran (schritt := schritt) abEins (some z₀) _ s₀
  let ρ : Lauf E := ⟨start, hw, zeit⟩
  have rein : ∀ b ∈ p.code, b.Privat := stmt_rein tree
  exact ⟨E, H, ρ, arithmetik_grenzen platform tab leer leerStart,
    fun f => (Fragment.sicherheitsPflichten_alle p platform [] tab okAll rein f).2,
    fun f => (Fragment.sicherheitsPflichten_alle p platform [] tab okAll rein f).1,
    ⟨fair.hardware, fair.konform, admissible, geladen.symm,
      SchedulerFair_aus_stillstand_ab E.maschine ρ 6 still6⟩,
    z₆, ⟨7, Int.le_refl _, Int.le_refl _⟩, ende, rfl, rfl⟩

/-- Every concrete run of a checker-accepted frame-only fragment with predicate invariants
    is safe. The checker verdict supplies the loader, crash-recovery and per-command premises;
    purity supplies the frame-only step. -/
theorem fragment_sicher (p : Fragment) (platform : Plattform) (ps : List Praedikat)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (ok : pruefeEinheit p ps = true)
    (rein : ∀ b ∈ p.code, b.Privat) :
    ∀ H (ρ : Lauf (p.sicherheitsEinheit platform)),
      Maschine.Laeufe (p.einheit platform) H ρ →
      Speichersicher (p.sicherheitsEinheit platform) H ρ ∧
        InvariantenErhalten (p.sicherheitsEinheit platform) H ρ ∧
        Rennfrei (p.sicherheitsEinheit platform) H ρ ∧
        ToctouFrei (p.sicherheitsEinheit platform) H ρ :=
  sicherheit_aus_regeln (arithmetik_grenzen platform tab
    (pruefeEinheit_start p ps ok) (pruefeEinheit_neustart p ps ok))
    (Fragment.sicherheitsPflichten_alle p platform ps tab
      (fun b hmem => pruefeEinheit_befehl p ps b hmem ok) rein)

end Gabbro.Core.Sicherheit
