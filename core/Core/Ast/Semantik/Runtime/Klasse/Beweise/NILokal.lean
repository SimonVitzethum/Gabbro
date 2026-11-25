/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/NILokal.lean
  Subject:   INFORMATION FLOW OF THE SILENT CLASSES (MK-03). The flow duty of a form of class `lokal`
             or `ruf`: a step of such a form is silent, so a coupled pair of runs stays coupled across
             the step. The helper `antwortNI`, which in the fragment package is tied to `p.einheit`,
             is generalised here to an arbitrary `Klasseneinheit`: a unit whose forms never issue a
             question never records an answer. The generalisation is supplied first as its own lemma.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Beobachtung.Fluss.Beweise.Antwort
public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung

/-- A unit is question-free if none of its forms issues a question in an implementation step and
    its loader begins with no pending question. These are the two properties the fragment package
    gets from `Befehl.impl_privat` and the canonical loader; they are not consequences of embedding
    a single silent form. -/
def Klasseneinheit.Fragenfrei {ι : Type} (E : Klasseneinheit ι) : Prop :=
  (∀ (i : ι) (c : Kontext) (s : Zustand) (w : PUnit) (p : Plan) (u : Zustand),
      (E.system.regel i).impl c s w [p] u → ∀ q : Frage, p.aktion ≠ .frage q) ∧
  (∀ (h : Katalog.Umgebung) (s : AussenStart) (z : Zustand),
      E.laden s (h.lade E.bild) = some z → z.fragen = [])

/-- A protocol action other than a question leaves the pending-question ledger unchanged. -/
theorem klassen_antwort_fuehrt_aus_fragen_leer {ι : Type} (E : Klasseneinheit ι)
    {t : Nat} {c : Kontext} {s u v : Zustand} {aktion : Aktion Nat PUnit}
    {sperren : List (Speicher.Etikett Zelle Int)} {aussen : List Ereignis}
    (aktionStep : FuehrtAus E.einrichtung t c s u aktion sperren aussen v)
    (uLeer : u.fragen = []) (keinFrage : ∀ q, aktion ≠ .frage q) : v.fragen = [] := by
  cases aktionStep with
  | frage q => exact (keinFrage q rfl).elim
  | intern | warte _ | sperre _ _ | verbrauche _ | rueckkehr _ _ =>
      change u.fragen = []
      exact uLeer

/-- A machine step of a question-free unit never creates a pending question. -/
theorem klassen_antwort_schritt_fragen {ι : Type} (E : Klasseneinheit ι) (frei : E.Fragenfrei)
    {hw : HwLauf} {t : Nat} {s s' : Zustand} {label : SchrittWahl PUnit × SchrittSpur Zelle Int}
    (step : ImplSchritt E.einrichtung E.system E.katalog hw t s label s')
    (leer : s.fragen = []) : s'.fragen = [] := by
  cases step with
  | kontext _ _ regel aus =>
      obtain ⟨i, _, impl⟩ := regel
      have keinFrage := frei.1 i _ _ _ _ _ impl
      obtain ⟨frame, _, _, _, fuehrtAus, _, s'Eq⟩ := aus
      have uLeer := frame.fragen.trans leer
      have vLeer := klassen_antwort_fuehrt_aus_fragen_leer E fuehrtAus uLeer keinFrage
      rw [s'Eq]
      exact vLeer
  | antwort _ arrives =>
      obtain ⟨_, _, _, stateEq⟩ := arrives
      rw [stateEq]
      change s.fragen = []
      exact leer
  | interrupt _ enters =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, stateEq⟩ := enters
      rw [stateEq]
      change s.fragen = []
      exact leer
  | absturz crash =>
      obtain ⟨_, _, _, _, stateEq⟩ := crash
      rw [stateEq]
      change s.fragen = []
      exact leer

/-- By induction over the cuts, a question-free unit has no pending question at any loaded cut. -/
theorem klassen_antwort_fragen_leer {ι : Type} (E : Klasseneinheit ι) (frei : E.Fragenfrei)
    {h : Katalog.Umgebung} {ρ : Lauf E} (lauf : Laeufe E h ρ) :
    ∀ t, ρ.zeit.zustand t = none ∨ ∃ z, ρ.zeit.zustand t = some z ∧ z.fragen = [] := by
  intro t
  induction t with
  | zero =>
      rw [lauf.2.2.2]
      cases hlad : E.laden ρ.start (h.lade E.bild) with
      | none =>
          exact Or.inl rfl
      | some z =>
          exact Or.inr ⟨z, rfl, frei.2 h ρ.start z hlad⟩
  | succ t ih =>
      cases ih with
      | inl noneq =>
          have tick := ρ.zeit.takt t
          rw [noneq] at tick
          cases tick with
          | schritt _ step => cases step
          | wartet _ eq _ => exact Or.inl eq
      | inr gefunden =>
          obtain ⟨z, atZ, fragenLeer⟩ := gefunden
          have tick := ρ.zeit.takt t
          rw [atZ] at tick
          cases tick with
          | schritt _ step =>
              cases after : ρ.zeit.zustand (t + 1) with
              | none =>
                  rw [after] at step
                  cases step
              | some next =>
                  right
                  refine ⟨next, rfl, ?_⟩
                  rw [after] at step
                  cases step with
                  | schritt impl => exact klassen_antwort_schritt_fragen E frei impl fragenLeer
          | wartet _ eq _ =>
              right
              exact ⟨z, eq, fragenLeer⟩

/-- The pending-question fact at a named loaded cut. -/
theorem klassen_antwort_fragen_leer_an {ι : Type} (E : Klasseneinheit ι) (frei : E.Fragenfrei)
    {h : Katalog.Umgebung} {ρ : Lauf E} (lauf : Laeufe E h ρ)
    (t : Nat) {z : Zustand} (atZ : ρ.zeit.zustand t = some z) : z.fragen = [] := by
  have alle := klassen_antwort_fragen_leer E frei lauf t
  cases alle with
  | inl noneq => cases (atZ.symm.trans noneq)
  | inr gefunden =>
      obtain ⟨z', eq, leer⟩ := gefunden
      have zz : z = z' := Option.some.inj (atZ.symm.trans eq)
      cases zz
      exact leer

/-- **Generalised `antwortNI`**: a question-free `Klasseneinheit` never records an answer. -/
theorem antwortNI_klasseneinheit {ι : Type} (E : Klasseneinheit ι) (frei : E.Fragenfrei) :
    ∀ (h : Katalog.Umgebung) (ρ : Lauf E), Laeufe E h ρ → ∀ t a spur,
      ρ.zeit.spur t ≠ some (.antwort a, spur) := by
  intro h ρ lauf t a spur gleich
  have tick := ρ.zeit.takt t
  rw [gleich] at tick
  cases tick with
  | wartet label _ _ => cases label
  | schritt label step =>
      rename_i event
      have evEq := Option.some.inj label
      rw [← evEq] at step
      cases before : ρ.zeit.zustand t with
      | none =>
          rw [before] at step
          cases step
      | some z =>
          cases after : ρ.zeit.zustand (t + 1) with
          | none =>
              rw [before] at step
              rw [after] at step
              cases step
          | some next =>
              rw [before] at step
              rw [after] at step
              cases step with
              | schritt impl =>
                  cases impl with
                  | antwort _ arrives =>
                      obtain ⟨angebot, _, _, _⟩ := arrives
                      have zLeer := klassen_antwort_fragen_leer_an E frei lauf t before
                      obtain ⟨q, qmem, _⟩ := angebot.2.2.2.1
                      rw [zLeer] at qmem
                      cases qmem

/-! ### State-level flow of a silent form

    The two pieces below are the state-level part of the flow duty: a step of a silent form is the
    private plan and a frame update, and `RegelFluss` transfers public equality of the pre-states
    to public equality of the post-states. Lifting this to `RegelNIPflicht` is the open step; see the
    closing note of this file. -/

/-- Public source-state equality is reflexive. -/
theorem quellzustandGleich_refl {ι : Type} (E : Klasseneinheit ι) (v : Zustand) :
    Beobachtung.QuellzustandGleich E v v := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro c p hp
    rfl
  · intro c
    rfl
  · intro x
    rfl
  · intro c
    rfl

/-- Public source-state equality is symmetric. -/
theorem quellzustandGleich_symm {ι : Type} (E : Klasseneinheit ι) {v u : Zustand}
    (h : Beobachtung.QuellzustandGleich E v u) : Beobachtung.QuellzustandGleich E u v := by
  rcases h with ⟨lok, ende, initial, rechte, leihen, antwort⟩
  refine ⟨?_, ?_, ?_, rechte.symm, leihen.symm, ?_⟩
  · intro c p hp
    exact (lok c p hp).symm
  · intro c
    exact (ende c).symm
  · intro x
    exact (initial x).symm
  · intro c
    exact (antwort c).symm

/-- Public source-state equality is transitive. -/
theorem quellzustandGleich_trans {ι : Type} (E : Klasseneinheit ι) {v u w : Zustand}
    (hvu : Beobachtung.QuellzustandGleich E v u)
    (huw : Beobachtung.QuellzustandGleich E u w) : Beobachtung.QuellzustandGleich E v w := by
  rcases hvu with ⟨lokvu, endvu, initvu, rechtevu, leihenvu, antvu⟩
  rcases huw with ⟨lokuw, enduw, inituw, rechteuw, leihenuw, antuw⟩
  refine ⟨?_, ?_, ?_, rechtevu.trans rechteuw, leihenvu.trans leihenuw, ?_⟩
  · intro c p hp
    exact (lokvu c p hp).trans (lokuw c p hp)
  · intro c
    exact (endvu c).trans (enduw c)
  · intro x
    exact (initvu x).trans (inituw x)
  · intro c
    exact (antvu c).trans (antuw c)

/-- The step relation of a silent form is its ideal relation with the private plan. -/
theorem klassen_stummer_ideal {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform)
    (emb : F.Eingebettet E f) (hk : F.klasse = .lokal ∨ F.klasse = .ruf)
    {c : Kontext} {s : Zustand} {w : PUnit} {p : Plan} {u : Zustand}
    (step : (E.system.regel f).ideal c s w [p] u) :
    p = Semantik.plan ∧ u = F.nach c s 0 := by
  obtain ⟨k, o, t⟩ := F
  rw [emb.regel] at step
  change Schrittform.ideal ⟨k, o, t⟩ c s w [p] u at step
  rcases hk with rfl | rfl
  · simp only [Schrittform.ideal] at step
    exact ⟨(List.cons.inj step.1).1, step.2⟩
  · simp only [Schrittform.ideal] at step
    exact ⟨(List.cons.inj step.1).1, step.2⟩

/-- An implementation step of a silent form at a head is a source step with the private plan. -/
theorem klassen_stummer_formschritt {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform)
    (emb : F.Eingebettet E f) (hk : F.klasse = .lokal ∨ F.klasse = .ruf)
    {c : Kontext} {s : Zustand} {w : PUnit} {p : Plan} {u : Zustand}
    (kopf : E.system.kopf s c = some f) (step : (E.system.regel f).impl c s w [p] u) :
    Beobachtung.FormSchritt E f c s w p u := by
  obtain ⟨k, o, t⟩ := F
  refine ⟨kopf, ?_⟩
  rw [emb.regel]
  rw [emb.regel] at step
  change Schrittform.ideal ⟨k, o, t⟩ c s w [p] u at step
  change Schrittform.ideal ⟨k, o, t⟩ c s w [p] u
  exact step

/-- **State-level flow of a silent form**: two steps of the same embedded silent form from
    publicly equal pre-states leave the post-states publicly equal. This is the flow premise at
    the source level; the run-level coupling additionally needs the head function to respect the
    public state and the step to be observationally silent. -/
theorem klassen_stummer_fluss_nach {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform)
    (emb : F.Eingebettet E f) (hk : F.klasse = .lokal ∨ F.klasse = .ruf)
    (fluss : Beobachtung.RegelFluss E f) {c : Kontext} {v₁ v₂ : Zustand}
    (kopf₁ : E.system.kopf v₁ c = some f) (kopf₂ : E.system.kopf v₂ c = some f)
    (gleich : Beobachtung.QuellzustandGleich E v₁ v₂) :
    Beobachtung.QuellzustandGleich E (F.nach c v₁ 0) (F.nach c v₂ 0) := by
  obtain ⟨k, o, t⟩ := F
  have fs1 : Beobachtung.FormSchritt E f c v₁ () Semantik.plan
      ((⟨k, o, t⟩ : Schrittform).nach c v₁ 0) := by
    refine ⟨kopf₁, ?_⟩
    rw [emb.regel]
    change Schrittform.ideal ⟨k, o, t⟩ c v₁ () [Semantik.plan]
      ((⟨k, o, t⟩ : Schrittform).nach c v₁ 0)
    rcases hk with rfl | rfl <;> exact ⟨rfl, rfl⟩
  have fs2 : Beobachtung.FormSchritt E f c v₂ () Semantik.plan
      ((⟨k, o, t⟩ : Schrittform).nach c v₂ 0) := by
    refine ⟨kopf₂, ?_⟩
    rw [emb.regel]
    change Schrittform.ideal ⟨k, o, t⟩ c v₂ () [Semantik.plan]
      ((⟨k, o, t⟩ : Schrittform).nach c v₂ 0)
    rcases hk with rfl | rfl <;> exact ⟨rfl, rfl⟩
  by_cases hp : oeffentlich (E.fluss.kontrolle f) = true
  · exact (fluss.2 hp c v₁ () Semantik.plan ((⟨k, o, t⟩ : Schrittform).nach c v₁ 0)
      v₂ () Semantik.plan ((⟨k, o, t⟩ : Schrittform).nach c v₂ 0) gleich fs1 fs2).1
  · have hfalse : oeffentlich (E.fluss.kontrolle f) = false := by
      cases hpub : oeffentlich (E.fluss.kontrolle f) <;> simp_all
    have n1 := (fluss.1 c v₁ () Semantik.plan ((⟨k, o, t⟩ : Schrittform).nach c v₁ 0) fs1).2 hfalse
    have n2 := (fluss.1 c v₂ () Semantik.plan ((⟨k, o, t⟩ : Schrittform).nach c v₂ 0) fs2).2 hfalse
    exact quellzustandGleich_trans E (quellzustandGleich_symm E n1.1)
      (quellzustandGleich_trans E gleich n2.1)

/-! ### Run-level flow, with the extra premises named

    The pinned duty quantifies over every `Klasseneinheit` that embeds one silent form. For such an
    arbitrary unit the run-level step is not determined by the premises: the head function need not
    respect the public state, other forms may issue questions, and the form may record speculative
    or constant-time events. The theorem below proves the run-level duty under exactly these extra
    premises. They are listed here so the missing step of the unpinned statement is concrete. -/

/-- Every cut of an admitted run with a successful loader carries a state. -/
theorem einheit_zustand_some {ι : Type} {E : Klasseneinheit ι}
    (geladen : ∀ (h : Katalog.Umgebung) (s : AussenStart), ∃ z, E.laden s (h.lade E.bild) = some z)
    {h : Katalog.Umgebung} {ρ : Lauf E} (lauf : Laeufe E h ρ) (t : Nat) :
    ∃ s, ρ.zeit.zustand t = some s := by
  induction t with
  | zero =>
      obtain ⟨z, hz⟩ := geladen h ρ.start
      refine ⟨z, ?_⟩
      rw [lauf.2.2.2, hz]
  | succ t ih =>
      obtain ⟨z, hz⟩ := ih
      have tick := ρ.zeit.takt t
      rw [hz] at tick
      cases tick with
      | schritt _ step =>
          cases hn : ρ.zeit.zustand (t + 1) with
          | none =>
              rw [hn] at step
              cases step
          | some n => exact ⟨n, rfl⟩
      | wartet _ eq _ => exact ⟨z, eq⟩

/-- A context step of an embedded silent form leaves the machine state at its frame transfer. -/
theorem klassen_stummer_nach {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform)
    (emb : F.Eingebettet E f) (hk : F.klasse = .lokal ∨ F.klasse = .ruf)
    {t : Nat} {c : Kontext} {s : Zustand} {w : PUnit} {p : Plan} {u : Zustand}
    {spur : SchrittSpur Zelle Int} {s' : Zustand}
    (impl : (E.system.regel f).impl c s w [p] u)
    (aus : FuehrtSchrittAus E.einrichtung t c s u p spur s') :
    s' = F.nach c s 0 ∧ spur = ⟨[], []⟩ := by
  have step : (E.system.regel f).ideal c s w [p] u := by
    rw [emb.regel]
    change F.ideal c s w [p] u
    rw [emb.regel] at impl
    change F.ideal c s w [p] u at impl
    exact impl
  obtain ⟨hp, hu⟩ := klassen_stummer_ideal E f F emb hk step
  subst p
  subst u
  obtain ⟨_, _, _, _, fuehrtAus, speicherfolge, s'Eq⟩ := aus
  generalize hsA : spur.aussen = aussen at fuehrtAus speicherfolge
  generalize hsS : spur.speicher = speicherlist at speicherfolge
  cases fuehrtAus
  generalize hG : s'.graph = gEnd at speicherfolge s'Eq
  cases speicherfolge
  have spurEq : spur = ⟨[], []⟩ := by
    cases spur
    simp_all
  exact ⟨s'Eq, spurEq⟩

/-- **Run-level flow of a silent form, under the extra premises.** Besides the pinned premises
    (`Eingebettet`, `RegelFluss`, `Operandensicht`) this needs: the unit is question-free, its loader
    succeeds, its head function respects public state equality, and its steps append nothing to the
    low trace. These are not consequences of the pinned premises for an arbitrary `Klasseneinheit`. -/
theorem klassenNI_stumm_unter {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform)
    (emb : F.Eingebettet E f) (hk : F.klasse = .lokal ∨ F.klasse = .ruf)
    (fluss : Beobachtung.RegelFluss E f) (_sicht : F.Operandensicht E)
    (frei : E.Fragenfrei)
    (geladen : ∀ (h : Katalog.Umgebung) (s : AussenStart), ∃ z, E.laden s (h.lade E.bild) = some z)
    (kopfSicht : ∀ (c : Kontext) (v w : Zustand), Beobachtung.QuellzustandGleich E v w →
      E.system.kopf v c = some f → E.system.kopf w c = some f)
    (still : ∀ (ρ : Lauf E) (pred : Praediktor) (t : Nat), schrittBeob ρ pred t = []) :
    Beobachtung.RegelNIPflicht E f := by
  classical
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  obtain ⟨cov, st, len⟩ := kopplung
  obtain ⟨w₂, zustand₂⟩ := einheit_zustand_some geladen vergleich.rechts t
  obtain ⟨qgleich, epocheEq, geliefertEq, kerneEq, statusEq⟩ := st vor w₂ zustand zustand₂
  obtain ⟨lokGleich, endGleich, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩ := qgleich
  have kopf₂ : E.system.kopf w₂ c = some f :=
    kopfSicht c vor w₂ ⟨lokGleich, endGleich, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩ kopf
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
              obtain ⟨f₁, kopf₁, impl₁rule⟩ := regel₁
              have ff : f = f₁ := Option.some.inj (kopf.symm.trans kopf₁)
              subst ff
              obtain ⟨nach₁Eq, spurEq₁⟩ :=
                klassen_stummer_nach E f F emb hk impl₁rule aus₁
              have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
                congrArg (fun p => (p.1 t).2.2.2.2.2.1) vergleich.politik
              have coreEq : (ρ₁.hw.angebot t).core = (ρ₂.hw.angebot t).core :=
                congrArg (fun p => (p.1 t).1) vergleich.politik
              have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl = (ρ₂.hw.angebot t).interruptAuswahl := by
                have signale : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
                  congrArg (fun p => (p.1 t).2.2.1) vergleich.politik
                simp only [Gelegenheit.interruptAuswahl, signale]
              have crash₂ : (ρ₂.hw.angebot t).crash = false := by
                rw [← crashEq]
                exact keinAbsturz₁
              have bereit₂ : KannSchreiten ρ₂.hw t c w₂ := by
                obtain ⟨k, geleg₁, kern₁, stat₁⟩ := bereit₁
                refine ⟨k, ?_, ?_, ?_⟩
                · show (ρ₂.hw.angebot t).core = some k
                  rw [← coreEq]
                  exact geleg₁
                · show (w₂.kerne k).laeuft = some c
                  rw [← kerneEq]
                  exact kern₁
                · show w₂.status c = .laeuft
                  rw [← statusEq]
                  exact stat₁
              have rahmen₂ : Zustandsrahmen w₂ (F.nach c w₂ 0) := by
                refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              have speicher₂ : Speicherfolge w₂.initial (.kontext c) w₂.graph _ [] w₂.graph :=
                Speicherfolge.nil _
              have aus₂ : FuehrtSchrittAus E.einrichtung t c w₂ (F.nach c w₂ 0)
                  Semantik.plan ⟨[], []⟩ (F.nach c w₂ 0) := by
                refine ⟨rahmen₂, ?_, ?_⟩
                · intro l hl
                  cases hl
                · refine ⟨[], F.nach c w₂ 0, ?_, speicher₂, rfl⟩
                  exact FuehrtAus.intern
              have regel₂ : E.system.ImplSchritt c w₂ w [Semantik.plan] (F.nach c w₂ 0) := by
                obtain ⟨k, o, tr⟩ := F
                refine ⟨f, kopf₂, ?_⟩
                rw [emb.regel]
                change Schrittform.impl ⟨k, o, tr⟩ c w₂ w [Semantik.plan]
                  ((⟨k, o, tr⟩ : Schrittform).nach c w₂ 0)
                change Schrittform.ideal ⟨k, o, tr⟩ c w₂ w [Semantik.plan]
                  ((⟨k, o, tr⟩ : Schrittform).nach c w₂ 0)
                rcases hk with rfl | rfl <;> exact ⟨rfl, rfl⟩
              have step₂ : ImplSchritt E.einrichtung E.system E.katalog ρ₂.hw t w₂
                  (.kontext c w, ⟨[], []⟩) (F.nach c w₂ 0) :=
                .kontext crash₂ bereit₂ regel₂ aus₂
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
                rw [← auswahlEq]
                exact auswahl₁none
              have takt₂ := ρ₂.zeit.takt t
              rw [zustand₂] at takt₂
              generalize nachEq₂ : ρ₂.zeit.zustand (t + 1) = nach₂ at takt₂
              cases takt₂ with
              | wartet _ _ hp => exact (hp _ _ (Lauffolge.schritt step₂)).elim
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
                                  obtain ⟨nach₂Eq, spurEq₂⟩ :=
                                    klassen_stummer_nach E f F emb hk impl₂'rule aus₂'
                                  have still₁ : schrittBeob ρ₁ predictor t = [] :=
                                    still ρ₁ predictor t
                                  have still₂ : schrittBeob ρ₂ predictor t = [] :=
                                    still ρ₂ predictor t
                                  have e₁ : NiedrigeBeob E ρ₁ predictor (t + 1) =
                                      NiedrigeBeob E ρ₁ predictor t := by
                                    change NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
                                    rw [still₁, List.append_nil]
                                  have e₂ : NiedrigeBeob E ρ₂ predictor (t + 1) =
                                      NiedrigeBeob E ρ₂ predictor t := by
                                    change NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t = _
                                    rw [still₂, List.append_nil]
                                  have postGleich : Beobachtung.QuellzustandGleich E
                                      (F.nach c vor 0) (F.nach c w₂ 0) :=
                                    klassen_stummer_fluss_nach E f F emb hk fluss kopf kopf₂
                                      ⟨lokGleich, endGleich, initialGleich, rechteGleich,
                                        leihenGleich, antwortGleich⟩
                                  refine ⟨?_, ?_, ?_⟩
                                  · rw [e₁, e₂]
                                    exact cov
                                  · intro a b ha hb
                                    rw [nachEq₁, nach₁Eq] at ha
                                    rw [nachEq₂, nach₂Eq] at hb
                                    obtain rfl := Option.some.inj ha
                                    obtain rfl := Option.some.inj hb
                                    refine ⟨postGleich, ?_, ?_, ?_, ?_⟩
                                    · simp only [Schrittform.nach, epocheEq]
                                    · simp only [Schrittform.nach, geliefertEq]
                                    · simp only [Schrittform.nach, kerneEq]
                                    · simp only [Schrittform.nach, statusEq]
                                  · rw [e₁, e₂]
                                    exact len
                      | antwort a =>
                          exact (antwortNI_klasseneinheit E frei h₂ ρ₂ vergleich.rechts t a sp₂ label₂).elim
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

end Gabbro.Core.Ast.Semantik
