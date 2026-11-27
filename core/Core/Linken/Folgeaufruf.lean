module

public import Core.Linken.Aussage
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

def folgeEinheit : Ast.Semantik.Einheit :=
  beispielFragment.einheit beispielPlan.plattform

def folgeHw (h : Umgebung) (k : Nat) : HwLauf :=
  ⟨fun _ => ⟨some k, fun _ => false, [], fun _ => false, false, false, 0⟩, h.politik⟩

theorem folgeHw_konform (h : Umgebung) (s : AussenStart) (zul : folgeEinheit.ZulStart h s)
    (k : Nat) (assigned : s.assignment 0 = some k) :
    (folgeHw h k).konform folgeEinheit.katalog h := by
  refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro core hc
    cases hc
    exact (zul.2.2.2.1 0 k assigned).2
  · intro _ hc
    cases hc
  · intro _ hmem
    exact (List.not_mem_nil hmem).elim
  · intro _ hd
    cases hd
  · rintro (hmed | hcrash) <;> cases ‹false = true›

def folgeSchritt (b : Befehl) (s : Zustand) : Zustand :=
  b.maschinennach eintritt s (b.nach eintritt s)

def folgeZustand (s : AussenStart) (t : Nat) : Zustand :=
  let boot := (I.start folgeEinheit s).2
  let library := folgeSchritt (.definiere mainName [] none 0 3 false [] none) boot
  let caller := folgeSchritt (.springe 1) library
  let callee := folgeSchritt (.rufe mainName [] none) caller
  let returnPoint := folgeSchritt (.blockEnde 0) callee
  match t with
  | 0 => boot
  | 1 => library
  | 2 => caller
  | 3 => callee
  | 4 => returnPoint
  | _ + 5 => folgeSchritt .rueckVoid returnPoint

def folgeSpur : Nat → Option (SchrittWahl PUnit × SchrittSpur Zelle Int)
  | t => if t < 5 then some (.kontext eintritt (), ⟨[], []⟩) else none

theorem folge_tat (h : Umgebung) (s : AussenStart) (k : Nat)
    (t : Nat) (b : Befehl)
    (klass : b.Privat)
    (head : folgeEinheit.system.kopf (folgeZustand s t) eintritt = some b)
    (live : (folgeZustand s t).status eintritt = .laeuft)
    (dispatch : ((folgeZustand s t).kerne k).laeuft = some eintritt) :
    I.Schritt folgeEinheit.einrichtung folgeEinheit.system folgeEinheit.katalog (folgeHw h k) t
      (folgeZustand s t) (.kontext eintritt (), ⟨[], []⟩)
      (folgeSchritt b (folgeZustand s t)) :=
  .kontext rfl ⟨k, rfl, dispatch, live⟩
    ⟨b, head, (b.ideal_privat klass _ _ () [_] _).2 ⟨rfl, rfl⟩⟩
    (b.vollzug folgeEinheit.einrichtung _ _ _ klass)

theorem folge_dispatch (s : AussenStart) (k : Nat) (assigned : s.assignment 0 = some k) :
    (if some k = s.assignment 0 then some eintritt else none) = some eintritt := by
  rw [assigned, if_pos rfl]

theorem folge_fertig (h : Umgebung) (s : AussenStart) (k t : Nat) :
    KeinSchritt (I.Schritt folgeEinheit.einrichtung folgeEinheit.system folgeEinheit.katalog
      (folgeHw h k)) t (folgeZustand s 5) := by
  intro event next step
  cases step with
  | kontext normal bereit regel aus =>
    rename_i post plan spur c w
    obtain ⟨b, head, _⟩ := regel
    by_cases hc : c = eintritt
    · subst c
      have absent : folgeEinheit.system.kopf (folgeZustand s 5) eintritt = none := by rfl
      rw [absent] at head
      cases head
    · have rest : (folgeZustand s 5).status c = .ruht := by
        change (if c = eintritt then Status.laeuft else Status.ruht) = .ruht
        exact if_neg hc
      change kopf _ _ _ = _ at head
      simp only [kopf, rest] at head
      cases head
  | antwort _ reply =>
    obtain ⟨offered, _, _, _⟩ := reply
    obtain ⟨q, hmem, _, _⟩ := offered.2.2.2.1
    have empty : (folgeZustand s 5).fragen = [] := by rfl
    rw [empty] at hmem
    exact List.not_mem_nil hmem
  | interrupt _ enters =>
    obtain ⟨_, _, _, _, _, haus, _, _, _, _, _⟩ := enters
    obtain ⟨_, _, hoffer, _, _⟩ := haus
    cases hoffer
  | absturz crash => exact Bool.false_ne_true crash.1.2

def folgeZeit (h : Umgebung) (s : AussenStart) (k : Nat) (assigned : s.assignment 0 = some k) :
    Zeitlauf (I.Schritt folgeEinheit.einrichtung folgeEinheit.system folgeEinheit.katalog
      (folgeHw h k)) where
  zustand := folgeZustand s
  spur := folgeSpur
  takt t := by
    have dispatch := folge_dispatch s k assigned
    match t with
    | 0 => exact .schritt rfl (folge_tat h s k 0 _ (Or.inl rfl) (by rfl) (by rfl) (by exact dispatch))
    | 1 => exact .schritt rfl (folge_tat h s k 1 _ (Or.inl rfl) (by rfl) (by rfl) (by exact dispatch))
    | 2 => exact .schritt rfl (folge_tat h s k 2 _ (Or.inr (Or.inl rfl)) (by rfl) (by rfl) (by exact dispatch))
    | 3 => exact .schritt rfl (folge_tat h s k 3 _ (Or.inl rfl) (by rfl) (by rfl) (by exact dispatch))
    | 4 => exact .schritt rfl (folge_tat h s k 4 _ (Or.inl rfl) (by rfl) (by rfl) (by exact dispatch))
    | n + 5 =>
      exact .wartet (if_neg (by omega)) rfl (folge_fertig h s k (n + 5))

/-- The accepted two-module plan enters the second module, calls the library function and
    returns to the second module with its call stack restored. The five transitions form a
    maximal ideal run under a conformant hardware offer and an admitted start. -/
theorem folgeaufruf_erfuellbar :
    BauplanAkzeptiert beispielPlan ∧
      ∃ ρ : I.Lauf folgeEinheit, I.Laeufe folgeEinheit ρ ∧
        (∀ t < 5, ρ.zeit.spur t = some (.kontext eintritt (), ⟨[], []⟩)) ∧
        (∀ t, 5 ≤ t → ρ.zeit.spur t = none) ∧
        folgeEinheit.system.kopf (ρ.zeit.zustand 2) eintritt = some (.rufe mainName [] none) ∧
        ((ρ.zeit.zustand 2).lokal eintritt).pc = modulDef.fragment.code.length ∧
        ((ρ.zeit.zustand 3).lokal eintritt).pc = 1 ∧
        folgeEinheit.system.kopf (ρ.zeit.zustand 4) eintritt = some .rueckVoid ∧
        ((ρ.zeit.zustand 5).lokal eintritt).pc = modulDef.fragment.code.length + 1 ∧
        folgeEinheit.system.kopf (ρ.zeit.zustand 5) eintritt = none := by
  refine ⟨⟨beispielFragment, beispielLinke, beispielAkzeptiert⟩, ?_⟩
  obtain ⟨h, _, hardware, _⟩ :=
    katalog_nichtLeer folgeEinheit.katalog (Plattform.katalog_wohlgeformt .x86_64)
  have bild : folgeEinheit.bild.gueltig folgeEinheit.katalog.plattform.ziel :=
    Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hardware bild
  obtain ⟨k, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ _)
  let zeit := folgeZeit h s k assigned
  have pause : ∀ t z, KeinSchritt (I.Schritt folgeEinheit.einrichtung folgeEinheit.system
      folgeEinheit.katalog (folgeHw h k)) t z → ¬ AbsturzAngeboten folgeEinheit.katalog (folgeHw h k) t :=
    fun _ _ _ offer => Bool.false_ne_true offer.2
  let ρ : I.Lauf folgeEinheit := ⟨s, h, folgeHw h k, zeit.erlaubePausen pause, fun _ => none⟩
  refine ⟨ρ, ⟨hardware, folgeHw_konform h s zul k assigned, zul, rfl,
    zeit.erlaubePausen_maximal pause _ (fun _ => rfl), fun _ _ h => nomatch h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact if_pos ht
  · intro t ht
    exact if_neg (Nat.not_lt.mpr ht)
  all_goals rfl

end Gabbro.Core.Linken
