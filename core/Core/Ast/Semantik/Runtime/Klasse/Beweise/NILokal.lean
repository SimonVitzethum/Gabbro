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
  | intern | warte _ | sperre _ _ | verbrauche _ | rueckkehr _ _ | starte _ | verbinde _ _ | beende _
    | wechsle _ _ _ _ =>
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
      rw [lauf.2.2.2.1]
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

end Gabbro.Core.Ast.Semantik
