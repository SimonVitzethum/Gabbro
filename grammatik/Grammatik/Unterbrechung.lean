/-
  File:       Grammatik/Unterbrechung.lean
  Subject:    **INTERRUPTION, as a sentence** -- SYNTAX.md section 16.2 item 7, turned from
              a mapping into theorems: a handler is a thread in the run model.

  The mapping said: WHEN a handler runs (`entry ... dispatch`, `via idt`) stays a
  scheduling fact; a handler is a thread in the run model; `masks irqs` is a declaration
  the run's well-formedness may use; `H102` stays a pass. What stands here is that
  mapping WITH its proof burden carried: a handler step is a run step (one `Schritt`
  is one `Ereignis`), so the happens-before coverage of `Wettlauf.lean` extends to
  handlers -- two accesses, one of them by a handler, are HB-ordered, through lock
  release/acquire edges (`handler_nach_freigabe`) or excluded upfront by priority
  masking (`maske_schliesst_handler_aus`).

  SOURCE: `dokumente/SYNTAX.md` section 16.2 item 7 (split since <<SG-22>>, section 18).
  No import from `crates/`, `programmlogik/`, `passlogik/`, or `Body.lean`: like every
  file here, this one holds against THIS grammar, whatever the current `.rs` code
  does or leaves. Core Lean only, no mathlib.

  PREMISES, each named and each read by a proof below:
    (K) `Korngrenze` -- the atomicity boundary to Koernung (event granularity):
        preemption happens only BETWEEN events, never inside one. Every step of the
        run, handler or not, is exactly one whole, good event fitting its thread
        trace. Discharged from `Gesittet` by `korngrenze_aus_gesittet`; taken as an
        explicit premise wherever a handler step is read, not as a footnote.
    (M) `MaskenOrdnung` -- priority masking, named explicitly: while a thread holds
        a lock with `masks irqs` (`D.maskiert`), no foreign handler thread takes a
        step. The declaration side (WHICH lock masks; `H102` as a pass) stays
        outside; the run side is this predicate.
    (W3-W5) booked from `Wettlauf.lean`: exclusion (the lock primitive's promise),
        one thread per mark (linearity), one thread per unshared carrier (the
        `shared` declaration). The sentence theorems take `Gesittet`, which bundles
        them; `H` (which threads are handlers) travels as an explicit argument, not
        a section variable, so the existing theorems keep quantifying over every
        interleaving (same shape as `Nebeneinander` in `Wettlauf.lean` section 6).

  CUTS, booked here so nobody has to guess them later (shrunk, not faked):
    (C1) WHEN a handler runs stays a scheduling fact: `entry`/`dispatch`/`via idt`
        have no constructor here; the run-side SHAPE is section 4 below
        (`HandlerSchritt`, `HandlerEintritt`, `HandlerVersand`): the theorems
        quantify over runs in which the handler DID run as a thread, and dispatch
        admissibility is the mask-state face of (M)
        (`versand_gibt_maskenordnung`). What stays booked is the syntax
        constructor, not the shape.
    (C2) No priority levels IN THE DECLARATION: masking stays one boolean per lock
        (`D.maskiert`), not a priority lattice. The run-side SHAPE is section 5
        below (`EbenenOrdnung`, `MaskenEbene`, `EbenenPlan`): the boolean mask is
        the 0/1 case of levels (`ebenenplan_gibt_versand`). Preemption AMONG
        handlers themselves stays plain threads -- covered by the sentence,
        HB-ordered like any pair.
    (C3) The Owicki-Gries step is not here: that valid sequential logic survives
        interleaving needs the joint model (see the honesty note at the end of
        `Wettlauf.lean` section 5). Race-freedom extends to handlers; the logic
        proof does not follow it here.
    (C4) Handler bodies contribute traces like any thread (`IstVerschraenkung`
        covers them without a handler case); what makes a handler body `Brav` is
        `exec_gut` (`Satz.lean`), unchanged and unrepeated here.
-/
import Grammatik.Wettlauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Which threads of the run are interrupt handlers: the `entry ... dispatch` /
    `via idt` scheduling fact, as a predicate over run threads. WHEN such a thread
    runs is the scheduler's business (cut C1); THAT it runs as a thread is this file. -/
abbrev Handler : Type := Faden → Prop

/-! ## 1. The atomicity boundary (K): preemption only between events -/

/-- (K) Every step of the run -- handler or not -- is exactly one whole event: good,
    and fitting its thread trace. A handler never observes, and never leaves, a torn
    event: the preemption granularity (Koernung) is the event. -/
def Korngrenze (l : Lauf D) : Prop :=
  ∀ (j : Nat) (f : Faden) (e : Ereignis D),
    l[j]? = some (Schritt.mk f e) → e.gut ∧ e.passt (l.spur f j)

/-- (K) discharged: a well-formed run respects the boundary -- goodness is (W2) and
    fit is the recorded lock state (W1). -/
theorem korngrenze_aus_gesittet (l : Lauf D) (hg : Gesittet l) : Korngrenze (D := D) l := by
  intro j f e he
  exact ⟨hg.gut f (j + 1) e (by rw [l.spur_succ_eigen f j e he]; exact List.mem_cons_self),
    l.aufzeichnung hg f j e he⟩

/-! ## 2. Priority masking (M): a held masking lock admits no foreign handler step -/

/-- (M) While thread `f` holds a lock with `masks irqs`, no foreign handler thread
    steps: the run side of the `masks irqs` declaration (whose checking stays a pass,
    `H102`). -/
def MaskenOrdnung (H : Handler) (l : Lauf D) : Prop :=
  ∀ (j : Nat) (f g : Faden) (L : D.Lock) (e : Ereignis D),
    l[j]? = some (Schritt.mk g e) → H g → g ≠ f →
    l.haelt f L j → D.maskiert L = true → False

/-! ## 3. The sentence: HB coverage extends to handlers -/

/-- **A handler is a thread in the run model, table case.** Two accesses to the same
    table by different threads, one of them a handler, are ordered by happens-before.
    The handler premise names the reading; the order is `kein_wettlauf`, which never
    excluded handlers -- they were always threads. The boundary premise (K) is read
    at both steps: each is one whole event. -/
theorem handler_wettlauf_frei (l : Lauf D) (hg : Gesittet l) (H : Handler)
    (K : Korngrenze (D := D) l)
    (i j : Nat) (hij : i < j) (f g : Faden) (hfg : f ≠ g)
    (hH : H f ∨ H g) (t : D.Tab) (w w' : Bool)
    (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.zugriff t w Λ h)))
    (hj : l[j]? = some (Schritt.mk g (.zugriff t w' Λ' h'))) :
    HB l i j := by
  have _ := K i f _ hi
  have _ := K j g _ hj
  rcases hH with _ | _ <;>
    exact kein_wettlauf l hg i j hij f g hfg t w w' Λ Λ' h h' hi hj

/-- **A handler is a thread in the run model, global case.** Two accesses to the same
    global by different threads, one of them a handler, are HB-ordered -- or the
    global is `atomic`, and then the machine orders it (A10). There is no third
    case for handlers either. -/
theorem handler_wettlauf_frei_global (l : Lauf D) (hg : Gesittet l) (H : Handler)
    (K : Korngrenze (D := D) l)
    (i j : Nat) (hij : i < j) (f g : Faden) (hfg : f ≠ g)
    (hH : H f ∨ H g) (x : D.Glob) (w w' : Bool)
    (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.gzugriff x w Λ h)))
    (hj : l[j]? = some (Schritt.mk g (.gzugriff x w' Λ' h'))) :
    HB l i j ∨ D.atomar x = true := by
  have _ := K i f _ hi
  have _ := K j g _ hj
  rcases hH with _ | _ <;>
    exact kein_wettlauf_global l hg i j hij f g hfg x w w' Λ Λ' h h' hi hj

/-- **Through lock release/acquire edges.** Thread `f` touches `t` at `i` holding `L`,
    handler `g` touches `t` at `j > i` holding `L` (each recorded guard names `L`):
    between the accesses lies `f`'s release and `g`'s acquire, and the HB path runs
    through that sync edge. The handler rides it like any thread -- `H g` names the
    pair, and the proof needs nothing more, which is the sentence. -/
theorem handler_nach_freigabe (l : Lauf D) (hg : Gesittet l) (H : Handler)
    (K : Korngrenze (D := D) l)
    (f g : Faden) (hfg : f ≠ g) (hHg : H g)
    (L : D.Lock) (t : D.Tab) (w w' : Bool)
    (Λ Λ' : List (Res D)) (hh hh' : List D.Lock)
    (i j : Nat) (hij : i < j)
    (hi : l[i]? = some (Schritt.mk f (.zugriff t w Λ hh)))
    (hj : l[j]? = some (Schritt.mk g (.zugriff t w' Λ' hh')))
    (hLi : Res.held L ∈ Λ) (hLj : Res.held L ∈ Λ') :
    H g ∧ HB l i j := by
  have _ := K j g _ hj
  exact ⟨hHg, geordnet_durch_sperre l hg f g L i j hij hfg _ _ (by intro L' hc; cases hc)
    hi hj
    (l.haelt_bei_zugriff hg f i L _ hi hLi (by simp [Ereignis.traeger]))
    (l.haelt_bei_zugriff hg g j L _ hj hLj (by simp [Ereignis.traeger]))⟩

/-- **... or excluded upfront by priority masking.** Thread `f` takes a masking lock
    `L` at `k'` and does not release it before `k`; then no foreign handler step
    happens at `k`: the handler cannot cut into the masked section. Every handler
    access to a carrier `f` touches under `L` therefore lies after `f`'s release --
    where the lock-edge sentence above takes over. -/
theorem maske_schliesst_handler_aus (l : Lauf D) (H : Handler)
    (M : MaskenOrdnung (D := D) H l)
    (f g : Faden) (hfg : g ≠ f) (hHg : H g)
    (L : D.Lock) (hmask : D.maskiert L = true)
    (k k' : Nat) (hh : List D.Lock)
    (hnk' : l[k']? = some (Schritt.mk f (.nimmt L hh))) (hlt : k' < k)
    (hfrei : ∀ r, k' < r → r < k → l[r]? ≠ some (Schritt.mk f (.gibt L)))
    (e : Ereignis D) (hk : l[k]? = some (Schritt.mk g e)) : False :=
  M k f g L e hk hHg hfg (l.haelt_von f L k' hh hnk' k hlt hfrei) hmask

#print axioms Gabbro.Grammatik.korngrenze_aus_gesittet
#print axioms Gabbro.Grammatik.handler_wettlauf_frei
#print axioms Gabbro.Grammatik.handler_wettlauf_frei_global
#print axioms Gabbro.Grammatik.handler_nach_freigabe
#print axioms Gabbro.Grammatik.maske_schliesst_handler_aus

/-! ## 4. Schedule shape (C1, narrowed): WHEN a handler runs, as run predicates -/

/-- (C1-shape) Position `j` carries a handler step by `g`: the run-side reading of
    `entry ... dispatch` / `via idt`. WHEN the scheduler puts `g` there stays the
    scheduler's business (no constructor here); THAT it is a thread step is this
    predicate. -/
def HandlerSchritt (H : Handler) (l : Lauf D) (j : Nat) (g : Faden) : Prop :=
  ∃ e, l[j]? = some (Schritt.mk g e) ∧ H g

/-- (C1-shape) Entry at the boundary: the handler step at `j` is one whole event --
    good, and fitting its thread trace (the K condition read at that point).
    Preemption lands BETWEEN events because entry says so here, one position at
    a time. -/
def HandlerEintritt (H : Handler) (l : Lauf D) (j : Nat) (g : Faden) : Prop :=
  HandlerSchritt (D := D) H l j g ∧
    ∀ e, l[j]? = some (Schritt.mk g e) → e.gut ∧ e.passt (l.spur g j)

/-- (C1-shape) Mask-state-driven dispatch: handler `g` takes position `j` only where
    no foreign thread holds a masking lock. This is the schedule-admissibility face
    of (M): the scheduler may place `g` at `j` exactly where the mask state admits
    it (`versand_gibt_maskenordnung` says they are the same condition). -/
def HandlerVersand (H : Handler) (l : Lauf D) (j : Nat) (g : Faden) : Prop :=
  HandlerSchritt (D := D) H l j g ∧
    ∀ (f : Faden) (L : D.Lock), l.haelt f L j → f = g ∨ D.maskiert L = false

/-- (C1-shape) Entry is what K discharges: any handler step in a K-run is a
    boundary entry. The mirror of `korngrenze_aus_gesittet`, one position at a
    time. -/
theorem handler_eintritt_aus_korngrenze (H : Handler) (l : Lauf D)
    (K : Korngrenze (D := D) l) (j : Nat) (g : Faden)
    (hS : HandlerSchritt (D := D) H l j g) :
    HandlerEintritt (D := D) H l j g :=
  ⟨hS, fun e he => K j g e he⟩

/-- (C1-shape) An entry step is one whole, good event. -/
theorem handler_eintritt_ganzes_ereignis (H : Handler) (l : Lauf D)
    (j : Nat) (g : Faden)
    (hE : HandlerEintritt (D := D) H l j g)
    (e : Ereignis D) (he : l[j]? = some (Schritt.mk g e)) : e.gut :=
  (hE.2 e he).1

/-- (C1-shape) Dispatch admissibility IS the run-side masking order: where every
    dispatch respects the mask state, no foreign handler step cuts into a held
    masking lock. -/
theorem versand_gibt_maskenordnung (H : Handler) (l : Lauf D)
    (hV : ∀ (j : Nat) (g : Faden),
      HandlerSchritt (D := D) H l j g → HandlerVersand (D := D) H l j g) :
    MaskenOrdnung (D := D) H l := by
  intro j f g L e hk hHg hfg hhaelt hmask
  have hS : HandlerSchritt (D := D) H l j g := ⟨e, hk, hHg⟩
  have hd := (hV j g hS).2 f L hhaelt
  rcases hd with hgg | hcon
  · exact hfg hgg.symm
  · rw [hmask] at hcon
    exact Bool.noConfusion hcon

/-- (C1-shape) Masking-path corollary: `f` takes a masking lock `L` at `k'` and holds
    it through `k`; then no foreign handler `g` is dispatched at `k`. The admitted
    schedule never cuts the masked section -- where the lock-edge sentence takes
    over after `f`'s release. -/
theorem versand_nach_nahme_ausgeschlossen (H : Handler) (l : Lauf D)
    (hV : ∀ (j : Nat) (g : Faden),
      HandlerSchritt (D := D) H l j g → HandlerVersand (D := D) H l j g)
    (f g : Faden) (hfg : g ≠ f) (hHg : H g)
    (L : D.Lock) (hmask : D.maskiert L = true)
    (k k' : Nat) (hh : List D.Lock)
    (hnk' : l[k']? = some (Schritt.mk f (.nimmt L hh))) (hlt : k' < k)
    (hfrei : ∀ r, k' < r → r < k → l[r]? ≠ some (Schritt.mk f (.gibt L)))
    (e : Ereignis D) (hk : l[k]? = some (Schritt.mk g e)) : False :=
  maske_schliesst_handler_aus l H (versand_gibt_maskenordnung H l hV) f g hfg hHg
    L hmask k k' hh hnk' hlt hfrei e hk

/-! ## 5. Priority levels (C2, narrowed): the boolean mask as the 0/1 case -/

/-- (C2-shape) Level order: levels are natural numbers, and the HIGHER number
    preempts the LOWER one. Stated as a def so `EbenenPlan` reads it by name. -/
def EbenenOrdnung (a b : Nat) : Prop := a < b

/-- (C2-shape) The boolean mask read as a level: `masks irqs` is level 1, anything
    else level 0. The DECLARATION stays boolean (`D.maskiert`); this is the run
    side generalized, so handlers THEMSELVES can be ordered against held locks. -/
def MaskenEbene (b : Bool) : Nat :=
  if b then 1 else 0

/-- (C2-shape) Level-driven dispatch: `g` at priority `prio g` takes position `j`
    only where every held foreign lock sits BELOW its level. The boolean
    `HandlerVersand` is the 0/1 instance (`ebenenplan_gibt_versand`). -/
def EbenenPlan (stufe : D.Lock → Nat) (prio : Faden → Nat) (l : Lauf D)
    (j : Nat) (g : Faden) : Prop :=
  ∀ (f : Faden) (L : D.Lock), l.haelt f L j → f = g ∨ EbenenOrdnung (stufe L) (prio g)

/-- (C2-shape) The 0/1 embedding is strict where the declaration says so: a masking
    lock outranks a non-masking one. -/
theorem maskenebene_monoton (L M : D.Lock)
    (hL : D.maskiert L = true) (hM : D.maskiert M = false) :
    EbenenOrdnung (MaskenEbene (D.maskiert M)) (MaskenEbene (D.maskiert L)) := by
  show (if D.maskiert M then (1 : Nat) else 0) < (if D.maskiert L then 1 else 0)
  rw [hM, hL]
  exact Nat.zero_lt_succ 0

/-- (C2-shape) Levels specialize to the boolean mask: a level-1 handler admitted by
    the level plan at `j` is admitted by the mask-state dispatch. The boolean C2
    cut is the 0/1 case, not a second rule. -/
theorem ebenenplan_gibt_versand (H : Handler) (l : Lauf D)
    (prio : Faden → Nat) (hP : ∀ g, H g → prio g = 1)
    (j : Nat) (g : Faden)
    (hS : HandlerSchritt (D := D) H l j g)
    (hE : EbenenPlan (D := D) (fun L => MaskenEbene (D.maskiert L)) prio l j g) :
    HandlerVersand (D := D) H l j g := by
  obtain ⟨e, hk, hHg⟩ := hS
  refine ⟨⟨e, hk, hHg⟩, fun f L hhaelt => ?_⟩
  rcases hE f L hhaelt with hgg | hlt
  · exact Or.inl hgg
  · right
    have hpg : prio g = 1 := hP g hHg
    rw [hpg] at hlt
    change MaskenEbene (D.maskiert L) < 1 at hlt
    cases hm : D.maskiert L with
    | true =>
        have h1 : MaskenEbene true = 1 := rfl
        rw [hm, h1] at hlt
        exact absurd hlt (Nat.lt_irrefl 1)
    | false => rfl

#print axioms Gabbro.Grammatik.handler_eintritt_aus_korngrenze
#print axioms Gabbro.Grammatik.handler_eintritt_ganzes_ereignis
#print axioms Gabbro.Grammatik.versand_gibt_maskenordnung
#print axioms Gabbro.Grammatik.versand_nach_nahme_ausgeschlossen
#print axioms Gabbro.Grammatik.maskenebene_monoton
#print axioms Gabbro.Grammatik.ebenenplan_gibt_versand

end Gabbro.Grammatik
