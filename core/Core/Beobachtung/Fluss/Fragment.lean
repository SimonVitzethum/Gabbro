module

public import Core.Beobachtung.Satz
public import Core.Beobachtung.Fluss.Quellfragment
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl LokalFamilie)

def FamilienNI (familie : LokalFamilie) : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) (f : Befehl), f.familie = familie →
    RegelFluss (p.einheit plattform) f → RegelNIPflicht (p.einheit plattform) f

/-- **Information flow of the access instructions** (MK-04, open): a load, a store and an atomic update keep the
    coupling of two runs when the unit's flow rule holds for them. The flow rule of the labelled unit refuses an
    access instruction (`Befehl.FlussRegel`: the label rule of a memory event is MK-13), so this statement is
    about the unit that labels nothing; a load whose cell label the observer sees is covered only through that
    premise. Difficulty: schwer. Sketch: the step of a store records its written cell in the plan, which
    `PlanSicht` shows for a public cell, and the successor frame is `uebertrag` of publicly equal frames; a load
    puts the value of its reads-from source into the frame, which the coupled runs choose equal for a public
    cell (the graph-level coupling of MK-13). -/
def ZugriffNIAussage : Prop :=
  FamilienNI .zugriff

def ProtokollwahlNI (form : SchrittWahl PUnit → Prop) : Prop :=
  ∀ (p : Fragment) (plattform : Plattform),
    let E := p.einheit plattform
    ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ → ∀ predictor t w spur,
      ρ₁.zeit.spur t = some (w, spur) → form w →
      Kopplung E ρ₁ ρ₂ predictor t t → Kopplung E ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- The selected loader row yields the canonical initial state of this fragment. -/
theorem fragment_geladen (p : Fragment) (plattform : Plattform) {h : Umgebung}
    {s : AussenStart} (hardware : Hardware (p.einheit plattform).katalog h)
    (zul : (p.einheit plattform).ZulStart h s) :
    (p.einheit plattform).laden s (h.lade (p.einheit plattform).bild) =
      some (I.start (p.einheit plattform) s).2 := by
  have gueltig : Ast.Semantik.bild.gueltig h.ziel := hardware.ziel.symm ▸ zul.1
  have zeile := hardware.lader Ast.Semantik.bild gueltig
  have start : (h.lade Ast.Semantik.bild).starts 0 = some 0 := lader_start zeile 0
  have byte : (h.lade Ast.Semantik.bild).bytes 0 = some 0 := (zeile.2.1 0 0 rfl).2
  change Ast.Semantik.laden p.eingang p.eintritte p.speicher plattform s (h.lade Ast.Semantik.bild) = _
  rw [Ast.Semantik.laden, if_pos ⟨start, byte⟩]
  rfl

/-- Admitted fragment runs always have a state: the loader succeeds and steps
    preserve definedness. Supplies the right-hand state for coupling proofs. -/
theorem fragment_zustand_some {p : Fragment} {plattform : Plattform}
    {h : Umgebung} {ρ : Lauf (p.einheit plattform)} (lauf : Laeufe (p.einheit plattform) h ρ) (t : Nat) :
    ∃ s, ρ.zeit.zustand t = some s := by
  induction t with
  | zero =>
    refine ⟨(I.start (p.einheit plattform) ρ.start).2, ?_⟩
    rw [lauf.2.2.2]
    exact fragment_geladen p plattform lauf.1 lauf.2.2.1
  | succ t ih =>
    obtain ⟨s, hs⟩ := ih
    have ht := ρ.zeit.takt t
    rw [hs] at ht
    cases ht with
    | schritt _ step =>
      cases hn : ρ.zeit.zustand (t + 1) with
      | none =>
        rw [hn] at step
        cases step
      | some n =>
        rw [hn] at step
        cases step with
        | schritt _ => exact ⟨n, rfl⟩
    | wartet _ gleich _ =>
      exact ⟨s, gleich⟩

-- (shared silence computation lives in `fragment_kontext_schritt_still` below)

/-- The head a run steps at time `t` is frame-only, when the head of the stepping state is. -/
theorem privat_am_kopf {p : Fragment} {plattform : Plattform} {ρ : Lauf (p.einheit plattform)} {t : Nat}
    {c : Kontext} {s0 : Ast.Semantik.Zustand} {f : Befehl}
    (zustand : ρ.zeit.zustand t = some s0) (kopf : (p.einheit plattform).system.kopf s0 c = some f)
    (privat : f.Privat) :
    ∀ s b, ρ.zeit.zustand t = some s → (p.einheit plattform).system.kopf s c = some b → b.Privat := by
  intro s b hs hb
  rw [zustand] at hs
  have gleich := Option.some.inj hs
  subst gleich
  rw [kopf] at hb
  exact (Option.some.inj hb) ▸ privat

/-- A context step of a frame-only form takes the internal plan, which records no memory access
    and no outside action, and changes only the local frame. Such a step emits no low event. -/
theorem fragment_kontext_schritt_still
    (p : Fragment) (plattform : Plattform)
    {ρ : Lauf (p.einheit plattform)} {predictor t c w spur}
    (privat : ∀ s b, ρ.zeit.zustand t = some s → (p.einheit plattform).system.kopf s c = some b → b.Privat)
    (tick : ρ.zeit.spur t = some (.kontext c w, spur)) :
    schrittBeob ρ predictor t = [] := by
  classical
  cases spur with
  | mk speicher aussen =>
    have recorded := ρ.zeit.takt t
    generalize hS : ρ.zeit.zustand t = sOpt at recorded
    generalize hN : ρ.zeit.zustand (t + 1) = nOpt at recorded
    cases recorded with
    | wartet label _ _ =>
      cases label.symm.trans tick
    | schritt label transition =>
      rw [tick] at label
      injection label with evEq
      subst evEq
      cases transition with
      | schritt impl =>
        rename_i s0 n0
        cases impl with
        | kontext _ _ regel aus =>
          unfold System.ImplSchritt at regel
          rcases regel with ⟨b, kopfB, implB⟩
          change Befehl.impl b c s0 w _ _ at implB
          obtain ⟨hspur, _, hstatus, _, _, _, _, _, hgraph, hbuchung, _, _, _, _, _, _⟩ :=
            b.vollzug_genau_privat (privat s0 b hS kopfB) (w := w) implB aus
          cases hspur
          obtain ⟨_, hnach⟩ := (b.impl_privat (privat s0 b hS kopfB) c s0 w _ _).1 implB
          have nBuchung : n0.buchung = s0.buchung := by
            rw [hbuchung, hnach]; rfl
          have hStatus : ∀ d, n0.status d = s0.status d := by
            intro d
            rw [hstatus, hnach]; rfl
          have hCommit : commitBeob (Form := Befehl) (p.einheit plattform).katalog.plattform s0 n0 = [] := by
            rw [commitBeob, nBuchung, List.drop_length, List.filterMap_nil]
          have hAusgabe : ausgabeBeob (p.einheit plattform) c (s0.lokal c) (n0.lokal c) = [] := by
            rfl
          have hZeit : zeitBeob ρ c (s0.lokal c) (n0.lokal c) = [] := by
            rfl
          have hKontext : kontextBeob ρ predictor t c s0 n0 ⟨[], []⟩ = [] := by
            rw [kontextBeob]
            dsimp only
            rw [hCommit, hAusgabe, hZeit, kopfB]
            have hSpek : (p.einheit plattform).katalog.plattform.spekulationshuelle.zugriffe
                ((p.einheit plattform).fluss.spekulativ b (s0.lokal c) predictor) = [] := by
              cases plattform <;> rfl
            have hKonstant : (p.einheit plattform).fluss.konstantzeit b = false := by
              rfl
            simp only [hSpek, hKonstant, Bool.false_eq_true, if_false, List.map_nil,
              List.nil_append, List.append_nil]
          have hEnde : ∀ d, (neuBeendet s0 n0 (p.einheit plattform).etiketten d).isSome = false := by
            intro d
            rw [neuBeendet, hStatus d]
            cases hst : s0.status d <;> rfl
          have hKeinEnde : ¬ ∃ d, (neuBeendet s0 n0 (p.einheit plattform).etiketten d).isSome = true := by
            rintro ⟨d, hd⟩
            rw [hEnde d] at hd
            cases hd
          rw [schrittBeob, tick, hS, hN]
          simp only [List.filterMap_nil, List.flatMap_nil, List.nil_append, hKontext,
            hKeinEnde, if_false]

/-- A silent fragment step preserves the coupling. Same-cut offers coincide, so the
    right run provably takes the same silent step (lockstep through step kinds); both
    sides advance to publicly equal post-states with empty observations. -/
theorem stummer_schritt_koppelt
    {p : Fragment} {plattform : Plattform} {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (p.einheit plattform)}
    (vergleich : Vergleich (p.einheit plattform) h₁ h₂ ρ₁ ρ₂)
    {f : Befehl} {predictor : Praediktor} {t : Nat} {c : Kontext} {w : PUnit}
    {spur : SchrittSpur Ast.Semantik.Zelle Int} {vor : Ast.Semantik.Zustand}
    (zustand : ρ₁.zeit.zustand t = some vor)
    (kopf : (p.einheit plattform).system.kopf vor c = some f)
    (spurGlied : ρ₁.zeit.spur t = some (.kontext c w, spur))
    (keineAntwort₂ : ∀ a sp, ρ₂.zeit.spur t ≠ some (.antwort a, sp))
    (privat : f.Privat)
    (kopplung : Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor t t) :
    Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor (t + 1) (t + 1) := by
  classical
  obtain ⟨cov, st, len⟩ := kopplung
  obtain ⟨w₂, zustand₂⟩ := fragment_zustand_some vergleich.rechts t
  obtain ⟨⟨lokGleich, _, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩,
    epocheEq, geliefertEq, kerneEq, statusEq⟩ := st vor w₂ zustand zustand₂
  -- public frame: full local equality
  have lokEqFun : vor.lokal = w₂.lokal := by
    funext d
    have hpub : oeffentlich (((p.einheit plattform).fluss.lokal d).etikett ⟨0, Nat.zero_lt_one⟩) = true :=
      rfl
    exact lokGleich d ⟨0, Nat.zero_lt_one⟩ hpub
  have sysKopf : ∀ s d, (p.einheit plattform).system.kopf s d = Ast.Semantik.kopf p.code s d :=
    fun s d => rfl
  -- head congruence through the coupled state
  have kopf₂ : (p.einheit plattform).system.kopf w₂ c = some f := by
    have h : Ast.Semantik.kopf p.code w₂ c = Ast.Semantik.kopf p.code vor c := by
      simp only [Ast.Semantik.kopf, lokEqFun.symm, statusEq.symm]
    rw [sysKopf, h, ← sysKopf]
    exact kopf
  -- left step analysis
  have takt₁ := ρ₁.zeit.takt t
  rw [spurGlied, zustand] at takt₁
  generalize nachEq₁ : ρ₁.zeit.zustand (t + 1) = nach₁ at takt₁
  cases takt₁ with
  | wartet label _ _ => cases label
  | schritt label step =>
    cases label
    cases step with
    | schritt impl =>
      cases impl with
      | kontext keinAbsturz₁ bereit₁ regel₁ aus₁ =>
        rename_i left_u left_plan
        obtain ⟨f₁, kopf₁, impl₁rule⟩ := regel₁
        have ff : f = f₁ := Option.some.inj (kopf.symm.trans kopf₁)
        subst ff
        obtain ⟨hspur₁, hlokal₁, hstatus₁, _, hantworten₁, hverbraucht₁, _, hinitial₁, _,
          hbuchung₁, hrechte₁, hgeliefert₁, hleihen₁, hepoche₁, hverworfen₁, _⟩ :=
          f.vollzug_genau_privat privat (w := w) impl₁rule aus₁
        have transfer₁ := (f.impl_privat privat c vor w _ _).1 impl₁rule
        obtain ⟨_, hnach₁⟩ := transfer₁
        subst hnach₁
        -- same-index offers
        have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
          congrArg (fun p => (p.1 t).2.2.2.2.2.1) vergleich.politik
        have coreEq : (ρ₁.hw.angebot t).core = (ρ₂.hw.angebot t).core :=
          congrArg (fun p => (p.1 t).1) vergleich.politik
        have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl = (ρ₂.hw.angebot t).interruptAuswahl := by
          have signale : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
            congrArg (fun p => (p.1 t).2.2.1) vergleich.politik
          simp only [Gelegenheit.interruptAuswahl, signale]
        have crash₂ : (ρ₂.hw.angebot t).crash = false := by
          rw [← crashEq]; exact keinAbsturz₁
        have bereit₂ : KannSchreiten ρ₂.hw t c w₂ := by
          obtain ⟨k, geleg₁, kern₁, stat₁⟩ := bereit₁
          refine ⟨k, ?_, ?_, ?_⟩
          · show (ρ₂.hw.angebot t).core = some k
            rw [← coreEq]; exact geleg₁
          · show (w₂.kerne k).laeuft = some c
            rw [← kerneEq]; exact kern₁
          · show w₂.status c = .laeuft
            rw [← statusEq]; exact stat₁
        have aus₂ : FuehrtSchrittAus (p.einheit plattform).einrichtung t c w₂ (f.nach c w₂)
            (f.plan (w₂.lokal c) 0) ⟨[], []⟩ (f.maschinennach c w₂ (f.nach c w₂)) :=
          f.vollzug _ t c w₂ privat
        have regel₂ : (p.einheit plattform).system.ImplSchritt c w₂ w [f.plan (w₂.lokal c) 0]
            (f.nach c w₂) :=
          ⟨f, kopf₂, (f.impl_privat privat c w₂ w [f.plan (w₂.lokal c) 0] (f.nach c w₂)).2 ⟨rfl, rfl⟩⟩
        have step₂ : ImplSchritt (p.einheit plattform).einrichtung (p.einheit plattform).system
            (p.einheit plattform).katalog ρ₂.hw t w₂
            (.kontext c w, ⟨[], []⟩) (f.maschinennach c w₂ (f.nach c w₂)) :=
          .kontext crash₂ bereit₂ regel₂ aus₂
        -- no interrupt offer on either side: a core opportunity is present
        have auswahl₁none : (ρ₁.hw.angebot t).interruptAuswahl = none := by
          obtain ⟨k, geleg₁, _, _⟩ := bereit₁
          have core₁ : (ρ₁.hw.angebot t).core = some k := geleg₁
          cases haus : (ρ₁.hw.angebot t).interruptAuswahl with
          | some _ =>
            have res := (vergleich.links.2.1.2 t).interrupt_reserviert haus
            rw [res.2.1] at core₁
            cases core₁
          | none => rfl
        have auswahl₂none : (ρ₂.hw.angebot t).interruptAuswahl = none := by
          rw [← auswahlEq]; exact auswahl₁none
        -- right tick: pause is impossible, kinds other than context are ruled out
        have takt₂ := ρ₂.zeit.takt t
        rw [zustand₂] at takt₂
        generalize nachEq₂ : ρ₂.zeit.zustand (t + 1) = nach₂ at takt₂
        cases takt₂ with
        | wartet _ _ hp =>
          exact (hp _ _ (Lauffolge.schritt step₂)).elim
        | schritt label₂ step₂' =>
          rename_i ev₂
          cases ev₂ with
          | mk wahl₂ sp₂ =>
            cases wahl₂ with
            | kontext c₂ w₂' =>
              cases step₂' with
              | schritt impl₂' =>
                cases impl₂' with
                | kontext _ bereit₂' regel₂' aus₂' =>
                  obtain ⟨f₂, kopf₂', impl₂'rule⟩ := regel₂'
                  -- both sides run the context the same core runs: the opportunities and the cores coincide
                  have c_eq : c₂ = c := by
                    obtain ⟨k₁, geleg₁, kern₁, _⟩ := bereit₁
                    obtain ⟨k₂, geleg₂, kern₂, _⟩ := bereit₂'
                    have core₁ : (ρ₁.hw.angebot t).core = some k₁ := geleg₁
                    have core₂ : (ρ₂.hw.angebot t).core = some k₂ := geleg₂
                    have kk : k₁ = k₂ := Option.some.inj (core₁.symm.trans (coreEq.trans core₂))
                    have gleich : (w₂.kerne k₂).laeuft = some c := by
                      rw [← kk, ← kerneEq]
                      exact kern₁
                    exact Option.some.inj (kern₂.symm.trans gleich)
                  rw [c_eq] at kopf₂' impl₂'rule aus₂'
                  have ff₂ : f = f₂ := Option.some.inj (kopf₂.symm.trans kopf₂')
                  subst ff₂
                  obtain ⟨hspur₂, hlokal₂, hstatus₂, _, hantworten₂, hverbraucht₂, _, hinitial₂, _,
                  hbuchung₂, hrechte₂, hgeliefert₂, hleihen₂, hepoche₂, hverworfen₂, _⟩ :=
                  f.vollzug_genau_privat privat (w := w₂') impl₂'rule aus₂'
                  have htrans₂ := (f.impl_privat privat c w₂ w₂' _ _).1 impl₂'rule
                  obtain ⟨_, hnach₂⟩ := htrans₂
                  subst hnach₂
                  have still₂ : schrittBeob ρ₂ predictor t = [] :=
                    fragment_kontext_schritt_still p plattform
                      (fun s b hs hk => privat_am_kopf zustand₂ kopf₂ privat s b hs (c_eq ▸ hk)) label₂
                  have e₁ : NiedrigeBeob (p.einheit plattform) ρ₁ predictor (t + 1) =
                      NiedrigeBeob (p.einheit plattform) ρ₁ predictor t := by
                    change NiedrigeBeob _ ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
                    rw [fragment_kontext_schritt_still p plattform (privat_am_kopf zustand kopf privat) spurGlied, List.append_nil]
                  have e₂ : NiedrigeBeob (p.einheit plattform) ρ₂ predictor (t + 1) =
                      NiedrigeBeob (p.einheit plattform) ρ₂ predictor t := by
                    change NiedrigeBeob _ ρ₂ predictor t ++ schrittBeob ρ₂ predictor t = _
                    rw [still₂, List.append_nil]
                  -- post-state equality from the coupled pre-states
                  have regionEq : Ast.Semantik.Zustand.regionLive vor =
                      Ast.Semantik.Zustand.regionLive w₂ := by
                    funext slot
                    simp only [Ast.Semantik.Zustand.regionLive, rechteGleich, leihenGleich]
                  have lokPost : (f.nach c vor).lokal = (f.nach c w₂).lokal := by
                    show Function.update vor.lokal c
                        (f.auswerten (vor.lokal c) (Ast.Semantik.Zustand.regionLive vor)) =
                      Function.update w₂.lokal c
                        (f.auswerten (w₂.lokal c) (Ast.Semantik.Zustand.regionLive w₂))
                    rw [lokEqFun, regionEq]
                  refine ⟨?_, ?_, ?_⟩
                  · -- prefix: both sides append nothing
                    rw [e₁, e₂]
                    exact cov
                  · -- state: publicly equal post-states, preserved machine fields
                    intro a b ha hb
                    rw [nachEq₁] at ha
                    rw [nachEq₂] at hb
                    have lokPost' : a.lokal = b.lokal := by
                      rw [(Option.some.inj ha).symm, (Option.some.inj hb).symm, hlokal₁, hlokal₂]
                      exact lokPost
                    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
                    · intro d p hp
                      exact congrFun lokPost' d
                    · intro d
                      have s1 : a.status d = vor.status d := by rw [(Option.some.inj ha).symm, hstatus₁]; rfl
                      have s2 : b.status d = w₂.status d := by rw [(Option.some.inj hb).symm, hstatus₂]; rfl
                      simp only [s1, s2, statusEq]
                    · intro x
                      have i1 : a.initial = vor.initial := by rw [(Option.some.inj ha).symm, hinitial₁]; rfl
                      have i2 : b.initial = w₂.initial := by rw [(Option.some.inj hb).symm, hinitial₂]; rfl
                      simp only [i1, i2]
                      exact initialGleich x
                    · have r1 : a.rechte = vor.rechte := by rw [hrechte₁]; rfl
                      have r2 : b.rechte = w₂.rechte := by rw [(Option.some.inj hb).symm, hrechte₂]; rfl
                      simp only [r1, r2]
                      exact rechteGleich
                    · have l1 : a.leihen = vor.leihen := by rw [hleihen₁]; rfl
                      have l2 : b.leihen = w₂.leihen := by rw [(Option.some.inj hb).symm, hleihen₂]; rfl
                      simp only [l1, l2]
                      exact leihenGleich
                    · intro d
                      simp only [AntwortSicht]
                      have q1 : a.naechsteAntwort d = vor.naechsteAntwort d := by
                        have e1 : a.antworten = vor.antworten := by rw [(Option.some.inj ha).symm, hantworten₁]; rfl
                        have e2 : a.verworfen = vor.verworfen := by rw [(Option.some.inj ha).symm, hverworfen₁]; rfl
                        have e3 : a.verbraucht = vor.verbraucht := by rw [(Option.some.inj ha).symm, hverbraucht₁]; rfl
                        simp only [Zustand.naechsteAntwort, Zustand.angekommen, e1, e2, e3]
                      have q2 : b.naechsteAntwort d = w₂.naechsteAntwort d := by
                        have e1 : b.antworten = w₂.antworten := by rw [(Option.some.inj hb).symm, hantworten₂]; rfl
                        have e2 : b.verworfen = w₂.verworfen := by rw [(Option.some.inj hb).symm, hverworfen₂]; rfl
                        have e3 : b.verbraucht = w₂.verbraucht := by rw [(Option.some.inj hb).symm, hverbraucht₂]; rfl
                        simp only [Zustand.naechsteAntwort, Zustand.angekommen, e1, e2, e3]
                      rw [q1, q2]
                      exact antwortGleich d
                    · have e1 : a.epoche = vor.epoche := by rw [hepoche₁]; rfl
                      have e2 : b.epoche = w₂.epoche := by rw [(Option.some.inj hb).symm, hepoche₂]; rfl
                      simp only [e1, e2, epocheEq]
                    · have g1 : a.geliefert = vor.geliefert := by rw [hgeliefert₁]; rfl
                      have g2 : b.geliefert = w₂.geliefert := by rw [(Option.some.inj hb).symm, hgeliefert₂]; rfl
                      simp only [g1, g2, geliefertEq]
                    · have haktEq : (f.plan (vor.lokal c) 0).aktion = (f.plan (w₂.lokal c) 0).aktion := by
                        rw [lokEqFun]
                      obtain ⟨_, _, _, v₁, aktion₁, _, stateEq₁⟩ := aus₁
                      obtain ⟨_, _, _, v₂, aktion₂, _, stateEq₂⟩ := aus₂'
                      subst hspur₁
                      subst hspur₂
                      rcases f.plan_privat_aktion privat (vor.lokal c) with hL | ⟨v1, a1, hL⟩ | ⟨g1, hL⟩ |
                        ⟨v2, k2, hL⟩ | ⟨l3, k3, p3, hL⟩
                      · rw [hL] at aktion₁
                        have hR : (f.plan (w₂.lokal c) 0).aktion = .intern := haktEq.symm.trans hL
                        rw [hR] at aktion₂
                        cases aktion₁
                        cases aktion₂
                        rw [stateEq₁, stateEq₂]
                        rfl
                      · rw [hL] at aktion₁
                        have hR : (f.plan (w₂.lokal c) 0).aktion = .maskiere v1 a1 := haktEq.symm.trans hL
                        rw [hR] at aktion₂
                        cases aktion₁
                        cases aktion₂
                        rw [stateEq₁, stateEq₂]
                        funext k
                        have hb : ((f.nach c vor).kerne k) = ((f.nach c w₂).kerne k) := congrFun kerneEq k
                        have hc : ((vor.kerne k).laeuft = some c) = ((w₂.kerne k).laeuft = some c) := by
                          rw [kerneEq]
                        rw [hc]
                        by_cases h : (w₂.kerne k).laeuft = some c <;> simp only [h, hb]
                      · rw [hL] at aktion₁
                        have hR : (f.plan (w₂.lokal c) 0).aktion = .prioritaet g1 := haktEq.symm.trans hL
                        rw [hR] at aktion₂
                        cases aktion₁
                        cases aktion₂
                        rw [stateEq₁, stateEq₂]
                        funext k
                        have hb : ((f.nach c vor).kerne k) = ((f.nach c w₂).kerne k) := congrFun kerneEq k
                        have hc : ((vor.kerne k).laeuft = some c) = ((w₂.kerne k).laeuft = some c) := by
                          rw [kerneEq]
                        rw [hc]
                        by_cases h : (w₂.kerne k).laeuft = some c <;> simp only [h, hb]
                      · rw [hL] at aktion₁
                        have hR : (f.plan (w₂.lokal c) 0).aktion = .sende v2 k2 := haktEq.symm.trans hL
                        rw [hR] at aktion₂
                        cases aktion₁
                        cases aktion₂
                        rw [stateEq₁, stateEq₂]
                        rfl
                      · rw [hL] at aktion₁
                        have hR : (f.plan (w₂.lokal c) 0).aktion = .leite l3 k3 p3 := haktEq.symm.trans hL
                        rw [hR] at aktion₂
                        cases aktion₁
                        cases aktion₂
                        rw [stateEq₁, stateEq₂]
                    · have s1 : a.status = vor.status := by rw [hstatus₁]; rfl
                      have s2 : b.status = w₂.status := by rw [(Option.some.inj hb).symm, hstatus₂]; rfl
                      simp only [s1, s2, statusEq]
                  · -- length: both sides append nothing
                    rw [e₁, e₂]
                    exact len
            | antwort a =>
              exact (keineAntwort₂ a sp₂ label₂).elim
            | interrupt id =>
              cases step₂' with
              | schritt impl₂' =>
                cases impl₂' with
                | interrupt _ h₂' =>
                  obtain ⟨_, _, _, _, _, pending₂, _, _, _, _, _⟩ := h₂'
                  have contra := pending₂.2.2.2.2
                  rw [auswahl₂none] at contra
                  cases contra
            | absturz =>
              cases step₂' with
              | schritt impl₂' =>
                cases impl₂' with
                | absturz h₂' =>
                  obtain ⟨offer₂, _, _⟩ := h₂'
                  have crash₂true : (ρ₂.hw.angebot t).crash = true := offer₂.2
                  rw [crash₂true] at crash₂
                  cases crash₂

/-- Pauses coincide under the coupling: lockstep through step kinds forces the right
    run to idle along. Stated for frame-only fragments: the argument has the left run take the very step the right
    run takes, which a frame-only form always has; the step of an access instruction exists only when the memory
    model accepts its read (`ZugriffKomponierbarAussage`), and the information flow of such a fragment is
    `ZugriffNIAussage` (MK-13). -/
def PauseNIAussage : Prop :=
  ∀ (p : Fragment) (plattform : Plattform), (∀ b ∈ p.code, b.Privat) → ∀ {h₁ h₂ ρ₁ ρ₂},
    Vergleich (p.einheit plattform) h₁ h₂ ρ₁ ρ₂ → ∀ predictor t,
      ρ₁.zeit.spur t = none →
      Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor t t →
      Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- The coupling starts: loader states are canonical, source states publicly equal,
    machine fields agree, and both initial observations are singletons. -/
theorem fragment_start_ni (p : Fragment) (plattform : Plattform) :
    StartFlussLokal (p.einheit plattform) → StartNIPflicht (p.einheit plattform) := by
  intro quelle h₁ h₂ ρ₁ ρ₂ vergleich predictor
  have lad₁ := fragment_geladen p plattform vergleich.links.1 vergleich.links.2.2.1
  have lad₂ := fragment_geladen p plattform vergleich.rechts.1 vergleich.rechts.2.2.1
  have z₁ : ρ₁.zeit.zustand 0 = some (I.start (p.einheit plattform) ρ₁.start).2 := by
    rw [vergleich.links.2.2.2, lad₁]
  have z₂ : ρ₂.zeit.zustand 0 = some (I.start (p.einheit plattform) ρ₂.start).2 := by
    rw [vergleich.rechts.2.2.2, lad₂]
  have q := quelle ρ₁.start ρ₂.start vergleich.start
  have assignEq : ρ₁.start.assignment = ρ₂.start.assignment :=
    congrArg (fun proj => proj.2.1) vergleich.start
  have regionsEq : ρ₁.start.regions = ρ₂.start.regions :=
    congrArg (fun proj => proj.2.2.1) vergleich.start
  have startdatenEq : (p.einheit plattform).startdaten ρ₁.start =
      (p.einheit plattform).startdaten ρ₂.start := by
    simp only [Fragment.einheit]
    rw [congrFun assignEq 0, regionsEq]
  have laderEq : LaderSicht (p.einheit plattform) h₁ ρ₁.start =
      LaderSicht (p.einheit plattform) h₂ ρ₂.start := by
    rw [LaderSicht, LaderSicht, lad₁, lad₂]
    exact congrArg some (funext fun x => q.2.2.1 x)
  have anf₁ := anfangsbeob (p.einheit plattform) ρ₁ h₁ vergleich.links predictor
  have anf₂ := anfangsbeob (p.einheit plattform) ρ₂ h₂ vergleich.rechts predictor
  refine ⟨?_, ?_, ?_⟩
  · rw [anf₁, anf₂, laderEq, List.take_length]
    exact .cons (.gleich _) .nil
  · intro v w hv hw
    rw [z₁] at hv
    rw [z₂] at hw
    obtain rfl := Option.some.inj hv
    obtain rfl := Option.some.inj hw
    have kerneEq : (I.start (p.einheit plattform) ρ₁.start).2.kerne =
        (I.start (p.einheit plattform) ρ₂.start).2.kerne := by
      show ((p.einheit plattform).startdaten ρ₁.start).kerne =
        ((p.einheit plattform).startdaten ρ₂.start).kerne
      rw [startdatenEq]
    refine ⟨q, rfl, rfl, kerneEq, rfl⟩
  · rw [anf₁, anf₂, laderEq]

end Gabbro.Core.Beobachtung
