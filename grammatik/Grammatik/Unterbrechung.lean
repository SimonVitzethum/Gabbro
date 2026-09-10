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
        have no constructor here; the theorems quantify over runs in which the
        handler DID run as a thread.
    (C2) No priority levels: masking is one boolean per lock (`D.maskiert`), not a
        priority lattice. Preemption AMONG handlers themselves is plain threads --
        covered by the sentence, HB-ordered like any pair.
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

end Gabbro.Grammatik
