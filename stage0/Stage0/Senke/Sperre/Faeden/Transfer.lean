/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Transfer.lean
  Subject:   THE EMITTED LOCK UNDER THE GOAL STATEMENT. `GabbroZielLeben` speaks about the runs of machine G with a
             ticket-lock queue (`FifoLauf`, Logik/Fortschritt/PlanLauf.lean). Here a scheduled run `R` of machine G
             is COUPLED with the abstract locks `a L` of the emitted locks (one per lock `L`):
             * `AbsLauf R.akt (a L)` -- each G step of thread `u` is what one G step can do to the lock (`Weg`),
               a stutter changes nothing; for an emitted lock this is PROVED from its run (`Lauf.absLauf`, under
               the window condition `Fenster`);
             * `GSicht R L (a L)` -- what G sees of `L` is the emitted lock: the threads standing at `locks L` are
               the waiting threads, the threads holding `L` are the holder. This is the simulation of the emitted
               code by machine G at this lock, NAMED here as a premise: it is not proved (the runner and the GX
               thread machine are not connected, Spec.lean (3)).
             Then `fifoAus`: the coupled run IS a `FifoLauf` (its queue is the emitted lock's), and
             `gabbroZielLeben_emittiert` is `gabbro_ziel_leben` applied to it, read back through the coupling: a
             thread waiting at an emitted lock becomes its holder, or some thread holds it from some step on for ever.
             The scope is explicit:
             * per lock: one emitted run per lock, all coupled with the SAME G run, so nesting and cross-lock
               waiting are the G run's (its holder-for-ever case, and `GabbroZiel`'s deadlock freedom);
             * threads: an emitted lock run has `N` threads `Fin N`; G's threads are unbounded and spawned at run
               time; the coupling makes only threads `< N` use the lock (`GSicht.unter`), a thread spawned later
               with a number `< N` is a thread of the emitted run that stayed outside until then;
             * the thread bound `N ≤ 2147483647` and `ScheinbarEndlich` are premises of the emitted run's OWN
               liveness (`Lauf.leben`), not of this transfer, whose fairness is G's (`Fair`).
-/
module
public import Stage0.Senke.Sperre.Faeden.Fenster
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Voll
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik (Deklaration Programm Orakel PlanLauf FifoLauf AnSperre offen RufStartG Speicher Env Faden
  sperre_schritt)
open Gabbro.Grammatik.Zielsatz (PrueferX NutzerPflichtA HardwareAnnahmen Laufzeit Einheit Aufzaehlung
  gabbro_ziel_leben)

section

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **What machine G sees of the lock `L` is the abstract lock `a`** (the simulation premise of the coupling). -/
structure GSicht (R : PlanLauf P O passes) (L : D.Lock) (a : Nat → Abs Nat) : Prop where
  glied : ∀ n u, u ∈ (a n).queue ↔ AnSperre (R.M n) u L
  halter : ∀ n u, (a n).holder = some u ↔ L ∈ offen ((R.M n).faeden u).spur

/-- A G step of a thread standing at `locks L` makes it the holder. -/
theorem GSicht.nimmt {R : PlanLauf P O passes} {L : D.Lock} {a : Nat → Abs Nat} (hS : GSicht R L a) {n : Nat}
    {u : Nat} (hk : R.akt n = some u) (hA : AnSperre (R.M n) u L) : (a (n + 1)).holder = some u := by
  refine (hS.halter (n + 1) u).2 ?_
  rw [(sperre_schritt hA (R.schritt n u hk)).2]
  simp only [offen]
  exact List.mem_cons_self

/-- **The coupled run is a run of the ticket lock**: its queue of `L` is the emitted lock's. -/
def fifoAus (R : PlanLauf P O passes) (a : D.Lock → Nat → Abs Nat) (hA : ∀ L, AbsLauf R.akt (a L))
    (hS : ∀ L, GSicht R L (a L)) : FifoLauf P O passes where
  toPlanLauf := R
  q := fun n L => (a L n).queue
  glied := fun n L u => (hS L).glied n u
  eindeutig := fun n L => (hA L).eindeutig n
  kopf := fun n u L hk hA' => (hA L).kopf hk (((hS L).glied n u).2 hA') ((hS L).nimmt hk hA')
  ordnung := fun n L => (hA L).ordnung n

/-- **Only the threads of the emitted run use the lock**: a G thread at `locks L` or holding `L` is one of the
    `N` threads of the emitted run of `L`. -/
theorem GSicht.unter {N : Nat} {R : PlanLauf P O passes} {L : D.Lock} {F : Lauf N} {φ : Nat → Nat}
    (hS : GSicht R L (F.bei φ)) {n u : Nat} (h : AnSperre (R.M n) u L ∨ L ∈ offen ((R.M n).faeden u).spur) :
    u < N := by
  rcases h with h | h
  · have hm : u ∈ (bild (F.z (φ n))).queue.map Fin.val := (hS.glied n u).2 h
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hm
    exact t.isLt
  · have hm : (bild (F.z (φ n))).holder.map Fin.val = some u := (hS.halter n u).2 h
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.1 hm
    exact t.isLt

end

/-- **GABBRO_ZIEL_LEBEN FOR THE EMITTED LOCKS.** Under the four premise groups of `GabbroZielLeben`, on every weakly
    fair scheduled run `R` of machine G from the runtime's start that is coupled with abstract locks `a L` (each a
    run at G granularity, `AbsLauf`, and what G sees of `L`, `GSicht`): a thread waiting at the lock `L` becomes its
    holder, or some thread holds `L` from some step on for ever. An instance of `gabbro_ziel_leben` (on the
    `FifoLauf` `fifoAus R a`), not an analog. -/
theorem gabbroZielLeben_emittiert (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E) (O : Orakel D) (hH : HardwareAnnahmen O E.Q)
    (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) (hL : Laufzeit E sp init)
    (R : PlanLauf E.P.mitRuhe O.mitRuhe passes) (a : D.mitRuhe.Lock → Nat → Abs Nat)
    (hA : ∀ L, AbsLauf R.akt (a L)) (hS : ∀ L, GSicht R L (a L))
    (hR0 : R.M 0 = RufStartG E.P.mitRuhe sp init) (hF : Gabbro.Grammatik.Fair E.P.mitRuhe O.mitRuhe passes R)
    (n : Nat) (t : Nat) (L : D.mitRuhe.Lock) (ht : t ∈ (a L n).queue) :
    (∃ j, n ≤ j ∧ (a L (j + 1)).holder = some t) ∨ ∃ u m, ∀ j, m ≤ j → (a L j).holder = some u := by
  rcases gabbro_ziel_leben C D E fs ls cs hC hN O hH passes sp init hL (fifoAus R a hA hS) hR0 hF n t L
      (((hS L).glied n t).1 ht) with ⟨j, hj, hk, hAj⟩ | ⟨u, m, hu⟩
  · exact Or.inl ⟨j, hj, (hS L).nimmt hk hAj⟩
  · exact Or.inr ⟨u, m, fun j hj => ((hS L).halter j u).2 (hu j hj)⟩

/-- **The same, for emitted lock runs**: each lock `L` has a run `F L` of the emitted lock with `N L` threads, read
    at G's steps through the window map `φ L` (`Fenster`); the coupling's G-step half (`AbsLauf`) is then proved,
    only `GSicht` stays a premise. A thread waiting at the emitted lock `L` (holding a ticket, not the lock) at G's
    step `n` holds it at some later G step, or some thread holds it from some G step on for ever. -/
theorem gabbroZielLeben_faeden (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E) (O : Orakel D) (hH : HardwareAnnahmen O E.Q)
    (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) (hL : Laufzeit E sp init)
    (R : PlanLauf E.P.mitRuhe O.mitRuhe passes) (Nf : D.mitRuhe.Lock → Nat) (F : ∀ L, Lauf (Nf L))
    (φ : D.mitRuhe.Lock → Nat → Nat) (hNf : ∀ L, Nf L ≤ 2147483647) (h0 : ∀ L, Inv (Nf L) ((F L).z 0))
    (hW : ∀ L, Fenster (F L) (φ L) R.akt) (hS : ∀ L, GSicht R L ((F L).bei (φ L)))
    (hR0 : R.M 0 = RufStartG E.P.mitRuhe sp init) (hF : Gabbro.Grammatik.Fair E.P.mitRuhe O.mitRuhe passes R)
    (n : Nat) (L : D.mitRuhe.Lock) (t : Fin (Nf L))
    (ht : (((F L).z (φ L n)).pc t).ticket.isSome = true ∧ (((F L).z (φ L n)).pc t).haelt = false) :
    (∃ j, n ≤ j ∧ (((F L).z (φ L (j + 1))).pc t).haelt = true) ∨
      ∃ u : Fin (Nf L), ∃ m, ∀ j, m ≤ j → (((F L).z (φ L j)).pc u).haelt = true := by
  have hm : t.val ∈ (bild ((F L).z (φ L n))).queue.map Fin.val :=
    List.mem_map.2 ⟨t, (bild_glied (Inv.lauf (hNf L) (F L) (h0 L) (φ L n)) t).2 ht, rfl⟩
  rcases gabbroZielLeben_emittiert C D E fs ls cs hC hN O hH passes sp init hL R (fun L => (F L).bei (φ L))
      (fun L => (F L).absLauf (hNf L) (h0 L) (hW L)) hS hR0 hF n t.val L hm with ⟨j, hj, hh⟩ | ⟨u, m, hu⟩
  · exact Or.inl ⟨j, hj, ((F L).bei_halter (hNf L) (h0 L) (φ L) (j + 1) t).1 hh⟩
  · have hlt : u < Nf L := (hS L).unter (n := m) (Or.inr (((hS L).halter m u).1 (hu m (Nat.le_refl m))))
    refine Or.inr ⟨⟨u, hlt⟩, m, fun j hj => ?_⟩
    exact ((F L).bei_halter (hNf L) (h0 L) (φ L) j ⟨u, hlt⟩).1 (hu j hj)

end Gabbro.Stage0.Senke.Faeden
