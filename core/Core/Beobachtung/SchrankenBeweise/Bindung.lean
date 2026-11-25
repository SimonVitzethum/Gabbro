/-
  File:      Core/Beobachtung/SchrankenBeweise/Bindung.lean
  Subject:   DECLARED BOUNDS ARE BOUND INTO ELABORATION (M9, Designer step 1).

  `SchrankenAkzeptiertAussage` (`Core/Ziel/Korrektheit/Zusammensetzung.lean`) is vacuous as long as
  `einheitVon P t` always binds `Schrankendaten.leer`: no declared cost, hold, time, stack, memory or
  per-pass ceiling ever reaches `Einheit.schranken`. This file binds them.

  The source (`Ast`) carries no bounds declaration yet, so the declaration is a minimal carrier beside
  the tree (`UnitMitSchranken`, the mirror image of `UnitMitInvarianten` in
  `Core/Ast/Semantik/Elaborierung.lean`): closed numbers for cost, memory and stack, closed lookup
  lists for hold (`halten`), per-pass ceilings (`durchlauf`) and time (`zeit`). No new `Ast`
  constructor, nothing in the middle of an existing inductive. `einheitMitSchranken` elaborates the
  tree exactly as `einheitVon` does and overrides only `schranken`. Every field is set explicitly
  (no structure defaults, so every binding fact is `rfl`). The local-measure side is fixed:
  `stapelTiefe` counts continuation frames, the mark stands stay empty until the per-pass elaboration
  (MK-19/MK-21) opens them.

  Proved here (`SchrankenbindungAussage`, pinned): the binding itself (every ceiling and lookup of
  the unit is the declared one, stands empty, depth is the frame count), `ProtokollMarkenErhaltend`
  for every bound unit (stands are empty, so the premise of `durchlaufProtokoll` holds
  unconditionally), the start duties that need no per-form work (`KHStartPflicht`,
  `ZeitStartPflicht`, and the generic `durchlaufStart`), and soundness of the decidable recovery
  line: `pruefeProtokollMarken` (every listed stand is empty; the loader evaluates it on the stands
  read from the restart data, so no protocol transition can introduce a back-dated mark).

  Open, handed to Hy4 as ONE pinned statement (`SchrankenbindungOffenAussage`): the per-form duties
  over bound elaborated units (`KHRegelPflicht`, `ZeitRegelPflicht`, `DurchlaufRegelPflicht`,
  the checker row `Annahme.RegelSchranken` with `ressourcenRegelAussage`), the protocol duties
  (`KHProtokollPflicht`, `ZeitProtokollPflicht`, `ressourcenProtokollAussage`) and the resource
  start duty (`ressourcenStartAussage`, which needs the loader's start-state facts for real bounds).
  With it, `b8_kh_aus_pflichten`, `durchlauf_aus_pflichten`, `b9_b21_aus_pflichten` and the time
  composition close `ImSchranken` for bound units. The companions beside it are binding-level:
  `schrankenbindung_erfuellbar` (a declared bound below infinity elaborates, the recovery line
  passes, the mark premise holds) and `schrankenbindung_nichtTrivial` (the recovery line refuses a
  nonempty stand, and ceiling zero against need one fails the per-pass line and falsifies the
  bound).
-/
module

public import Core.Ast.Semantik.Elaborierung
public import Core.Beobachtung.SchrankenB9B21
public import Core.Beobachtung.SchrankenBeweise.DurchlaufEinheit
public import Core.Annahme.Schranken

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The declared bounds beside a source unit: closed numbers for cost, memory and stack, closed
    lookup lists for hold, per-pass ceilings and time. The stands stay empty here; they are local
    state read at runtime, opened only by the per-pass elaboration. -/
structure Schrankendeklaration where
  kosten : Option Nat := none
  speicher : Option Nat := none
  stapel : Option Nat := none
  halten : List (Nat × Nat) := []
  durchlauf : List (Nat × Nat) := []
  zeit : List (Nat × Zeitdeklaration) := []

/-- The empty declaration binds nothing. -/
def Schrankendeklaration.leer : Schrankendeklaration :=
  ⟨none, none, none, [], [], []⟩

/-- Closed lookup in a declaration list: the first entry for the key wins. -/
def Schrankendeklaration.haltenVon (d : Schrankendeklaration) (l : Nat) : Option Nat :=
  (d.halten.find? (fun p => p.1 == l)).map Prod.snd

def Schrankendeklaration.durchlaufVon (d : Schrankendeklaration) (b : Nat) : Option Nat :=
  (d.durchlauf.find? (fun p => p.1 == b)).map Prod.snd

def Schrankendeklaration.zeitVon (d : Schrankendeklaration) (b : Nat) : Option Zeitdeklaration :=
  (d.zeit.find? (fun p => p.1 == b)).map Prod.snd

/-- The declared bounds as unit data: ceilings and lookups from the declaration, continuation
    frames as the depth measure, empty mark stands. Every field is set, so every binding fact
    below is `rfl`. -/
def schrankenAusDeklaration (d : Schrankendeklaration) : Schrankendaten Nat Rahmen where
  kosten := d.kosten
  speicher := d.speicher
  stapel := d.stapel
  halten := d.haltenVon
  stapelTiefe := fun r => r.fortsetzungen.length
  zeit := d.zeitVon
  zeitstand := fun _ => []
  durchlauf := d.durchlaufVon
  durchlaufstand := fun _ => []

/-- A source unit together with the bounds it declares. The mirror image of `UnitMitInvarianten`:
    until the source carries bounds declarations, the carrier stands beside the tree. -/
structure UnitMitSchranken where
  baum : Ast.Unit
  deklaration : Schrankendeklaration

/-- Elaboration binds the declared bounds: the tree elaborates exactly as `einheitVon` does, only
    `schranken` is the declared data. -/
def einheitMitSchranken (platform : Katalog.Plattform) (u : UnitMitSchranken) : Einheit :=
  { (programm u.baum).einheit platform with schranken := schrankenAusDeklaration u.deklaration }

/-- The bound unit declares exactly the declared ceilings. -/
theorem einheitMitSchranken_kosten (P : Katalog.Plattform) (u : UnitMitSchranken) :
    (einheitMitSchranken P u).schranken.kosten = u.deklaration.kosten :=
  rfl

theorem einheitMitSchranken_speicher (P : Katalog.Plattform) (u : UnitMitSchranken) :
    (einheitMitSchranken P u).schranken.speicher = u.deklaration.speicher :=
  rfl

theorem einheitMitSchranken_stapel (P : Katalog.Plattform) (u : UnitMitSchranken) :
    (einheitMitSchranken P u).schranken.stapel = u.deklaration.stapel :=
  rfl

theorem einheitMitSchranken_halten (P : Katalog.Plattform) (u : UnitMitSchranken) (l : Nat) :
    (einheitMitSchranken P u).schranken.halten l = u.deklaration.haltenVon l :=
  rfl

theorem einheitMitSchranken_durchlauf (P : Katalog.Plattform) (u : UnitMitSchranken) (b : Nat) :
    (einheitMitSchranken P u).schranken.durchlauf b = u.deklaration.durchlaufVon b :=
  rfl

theorem einheitMitSchranken_zeit (P : Katalog.Plattform) (u : UnitMitSchranken) (b : Nat) :
    (einheitMitSchranken P u).schranken.zeit b = u.deklaration.zeitVon b :=
  rfl

/-- No mark stand is ever visible on a bound unit: the per-pass elaboration has not opened any. -/
theorem einheitMitSchranken_standLeer (P : Katalog.Plattform) (u : UnitMitSchranken)
    (lok : Rahmen) :
    (einheitMitSchranken P u).schranken.durchlaufstand lok = [] ∧
      (einheitMitSchranken P u).schranken.zeitstand lok = [] :=
  ⟨rfl, rfl⟩

/-- The depth measure of a bound unit counts continuation frames. -/
theorem einheitMitSchranken_tiefe (P : Katalog.Plattform) (u : UnitMitSchranken) (r : Rahmen) :
    (einheitMitSchranken P u).schranken.stapelTiefe r = r.fortsetzungen.length :=
  rfl

/-- The empty declaration binds nothing: every lookup is open. -/
theorem schrankenAusDeklaration_leer :
    (schrankenAusDeklaration Schrankendeklaration.leer).kosten = none ∧
      (schrankenAusDeklaration Schrankendeklaration.leer).speicher = none ∧
      (schrankenAusDeklaration Schrankendeklaration.leer).stapel = none ∧
      (∀ l, (schrankenAusDeklaration Schrankendeklaration.leer).halten l = none) ∧
        (∀ b, (schrankenAusDeklaration Schrankendeklaration.leer).durchlauf b = none) ∧
          ∀ b, (schrankenAusDeklaration Schrankendeklaration.leer).zeit b = none :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Every bound unit keeps the mark-stand premise: both stands are empty, so a mark of the
    successor stand is impossible and the disjunction holds vacuously. This is the premise of
    `durchlaufProtokoll` for bound units. -/
theorem markenErhaltend_aus_bindung (P : Katalog.Plattform) (u : UnitMitSchranken) :
    ProtokollMarkenErhaltend (einheitMitSchranken P u) := by
  intro h ρ t w spur vor nach lauf vorEq spurEq wahl nachEq c m hmem
  have leer : (einheitMitSchranken P u).schranken.durchlaufstand (nach.lokal c) = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The cost and hold start duty holds for every bound unit: at cut zero the cost window is empty
    and no hold interval fits inside it. -/
theorem khStart_aus_bindung (P : Katalog.Plattform) (u : UnitMitSchranken) :
    KHStartPflicht (einheitMitSchranken P u) := by
  intro h ρ lauf
  refine ⟨?_, ?_⟩
  · intro n _
    simp only [KostenPrefix, Laufkosten, I.zaehle]
    exact Nat.zero_le n
  · intro l c a n bound _
    have ha : a = 0 := by omega
    have hn : n = 0 := by omega
    subst ha
    subst hn
    simp only [Kontextkosten, I.zaehle]
    intro n _
    exact Nat.zero_le n

/-- The time start duty holds for every bound unit: no mark is ever visible. -/
theorem zeitStart_aus_bindung (P : Katalog.Plattform) (u : UnitMitSchranken) :
    ZeitStartPflicht (einheitMitSchranken P u) := by
  intro h ρ lauf t' s hle sEq c m hmem
  have ht0 : t' = 0 := by omega
  subst ht0
  have leer : (einheitMitSchranken P u).schranken.zeitstand (s.lokal c) = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The checker's recovery line: every listed stand is empty. The loader evaluates it on the
    stands read from the restart data; with empty stands no protocol transition can introduce a
    back-dated mark. -/
def pruefeProtokollMarken (staende : List (List (Nat × Nat))) : Bool :=
  staende.all fun s => s.isEmpty

/-- SOUNDNESS of the recovery line: a passing stand list holds no mark anywhere. -/
theorem pruefeProtokollMarken_korrekt (staende : List (List (Nat × Nat)))
    (ok : pruefeProtokollMarken staende = true) :
    ∀ s ∈ staende, s = [] := by
  intro s mem
  cases s with
  | nil => rfl
  | cons x xs =>
    have h : (x :: xs).isEmpty = true := (List.all_eq_true.mp ok) _ mem
    have falsch : (x :: xs).isEmpty = false := rfl
    rw [falsch] at h
    exact False.elim (Bool.false_ne_true h)

/-- **The bound elaboration, in one pinned statement**: the unit carries exactly the declared
    ceilings and lookups with empty stands and the frame-count depth; the mark-stand premise and
    the start duties that need no per-form work hold for every bound unit; the decidable recovery
    line is sound. -/
def SchrankenbindungAussage : Prop :=
  (∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
    (einheitMitSchranken P u).schranken.kosten = u.deklaration.kosten ∧
      (einheitMitSchranken P u).schranken.speicher = u.deklaration.speicher ∧
      (einheitMitSchranken P u).schranken.stapel = u.deklaration.stapel ∧
      ((∀ l, (einheitMitSchranken P u).schranken.halten l = u.deklaration.haltenVon l) ∧
        (∀ b, (einheitMitSchranken P u).schranken.durchlauf b = u.deklaration.durchlaufVon b) ∧
        (∀ b, (einheitMitSchranken P u).schranken.zeit b = u.deklaration.zeitVon b) ∧
        (∀ lok : Rahmen, (einheitMitSchranken P u).schranken.durchlaufstand lok = [] ∧
          (einheitMitSchranken P u).schranken.zeitstand lok = []) ∧
        ∀ r : Rahmen, (einheitMitSchranken P u).schranken.stapelTiefe r = r.fortsetzungen.length))
  ∧ (∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
      ProtokollMarkenErhaltend (einheitMitSchranken P u))
  ∧ (∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
      KHStartPflicht (einheitMitSchranken P u) ∧ ZeitStartPflicht (einheitMitSchranken P u) ∧
        DurchlaufStartPflicht (einheitMitSchranken P u))
  ∧ ∀ staende : List (List (Nat × Nat)), pruefeProtokollMarken staende = true →
      ∀ s ∈ staende, s = []

/-- The bound elaboration holds as stated. -/
theorem schrankenbindung : SchrankenbindungAussage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P u
    exact ⟨rfl, rfl, rfl, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
      (fun _ => ⟨rfl, rfl⟩), (fun _ => rfl)⟩
  · intro P u
    exact markenErhaltend_aus_bindung P u
  · intro P u
    exact ⟨khStart_aus_bindung P u, zeitStart_aus_bindung P u, durchlaufStart⟩
  · intro staende ok
    exact pruefeProtokollMarken_korrekt staende ok

/-- **The exactly missing duties over bound units, in one pinned statement for Hy4** (M9
    prover side): the per-form duties for every source form (`KHRegelPflicht`,
    `ZeitRegelPflicht`, `DurchlaufRegelPflicht`, the checker row `Annahme.RegelSchranken` with
    `ressourcenRegelAussage`), the protocol duties (`KHProtokollPflicht`, `ZeitProtokollPflicht`,
    `ressourcenProtokollAussage`) and the resource start duty (`ressourcenStartAussage`, which
    needs the loader's start-state facts for real bounds). With it, `b8_kh_aus_pflichten`,
    `durchlauf_aus_pflichten`, `b9_b21_aus_pflichten` and the time composition close
    `ImSchranken` for bound units. -/
def SchrankenbindungOffenAussage : Prop :=
  (∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl),
    KHRegelPflicht (einheitMitSchranken P u) f)
  ∧ (∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl),
      ZeitRegelPflicht (einheitMitSchranken P u) f)
  ∧ (∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl),
      DurchlaufRegelPflicht (einheitMitSchranken P u) f)
  ∧ (∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl),
      Annahme.RegelSchranken (einheitMitSchranken P u) f ∧
        ressourcenRegelAussage (einheitMitSchranken P u) f)
  ∧ (∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
      KHProtokollPflicht (einheitMitSchranken P u) ∧
        ZeitProtokollPflicht (einheitMitSchranken P u) ∧
        ressourcenProtokollAussage (einheitMitSchranken P u))
  ∧ ∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
      ressourcenStartAussage (einheitMitSchranken P u)

/-- The empty source tree, for the binding witness below. -/
private def leerBaum : Ast.Unit := ⟨[], Ast.UnitBody.done⟩

/-- Joint satisfiability of the binding: a declared bound below infinity elaborates, the
    recovery line passes, and the mark-stand premise holds on the bound unit. -/
theorem schrankenbindung_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken),
      (einheitMitSchranken P u).schranken.kosten = some 5 ∧
        (einheitMitSchranken P u).schranken.speicher = some 7 ∧
        (einheitMitSchranken P u).schranken.stapel = some 3 ∧
        pruefeProtokollMarken [[], []] = true ∧
        ProtokollMarkenErhaltend (einheitMitSchranken P u) := by
  refine ⟨Katalog.Plattform.x86_64,
    ⟨leerBaum, ⟨some 5, some 7, some 3, [], [], []⟩⟩,
    rfl, rfl, rfl, by decide, markenErhaltend_aus_bindung _ _⟩

/-- Sharpness of the binding: the recovery line refuses a nonempty stand, and ceiling zero
    against need one fails the per-pass line and falsifies the bound. With the line soundness
    above, an overrunning unit is refused; the per-form refusal (`¬ Akzeptiert` from a violated
    declared bound) is the Hy4 step through `SchrankenbindungOffenAussage`. -/
theorem schrankenbindung_nichtTrivial :
    (∃ staende : List (List (Nat × Nat)), pruefeProtokollMarken staende = false) ∧
      ∃ (grenze : Option Nat) (bedarf : Nat),
        pruefeDurchlauf grenze bedarf = false ∧ ¬ UnterGrenze grenze bedarf := by
  refine ⟨⟨[[(0, 0)]], by decide⟩, (some 0), 1, by decide, ?_⟩
  intro h
  exact (by decide : ¬ 1 ≤ 0) (h 0 rfl)

end Gabbro.Core.Beobachtung
