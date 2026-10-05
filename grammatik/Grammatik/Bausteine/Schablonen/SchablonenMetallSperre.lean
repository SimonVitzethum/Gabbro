/-
  File:      Grammatik/SchablonenMetallSperre.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md): the GENERATED locks and rcu read
             sides of the bare-metal image (C-free lane, C3 slice 2, 2026-10-05).

  Rows of `crates/gabbro-check/src/schablonen.rs`, all three written by the generator into
  `<metall_sperren.h>` (`treiber.rs::METALL_SPERREN`; until 2026-10-05 handwritten in
  `laufzeit/metall/metall.h`):

  * `sperre.metall` -- `METALL_SPERRE(L)` / `_GETEILT(L)`: the ticket lock of `CTicket.lean`
    whose spin, every `METALL_SPIN` passes, gives the core away (`metall_abgeben`) -- but ONLY
    when the caller's IF was 1 at the call (`darf_abgeben`, read once before the spin);
  * `sperre.maskiert` -- `METALL_SPERRE_MASKIERT(L)` / `_MASKIERT_GETEILT(L)`: IF is cleared
    (`metall_ia_aus`, the old flags kept in a local) BEFORE the ticket is drawn; after the
    acquire the holder stores the old flags in the lock's own word `metall_flaggen_L`; the
    release reads that word back, releases, and restores the flags (`metall_ia_her`);
  * `rcu.metall` -- `METALL_RCU(R)`: a reader count per domain, `+1` at `R_lese_start`, `-1` at
    `R_lese_ende`, and the grace wait `metall_rcu_gnade_R` that returns once it reads zero.

  ABSTRACT CORES like `faden.laufzeit` (SchablonenFaden.lean). What is proved:

  * `mschritt_ticket_oder_stotter`, `minv_erreichbar`, `metall_ausschluss`: a step of the metal
    spin is a step of `CTicket.lean`'s ticket lock or changes NO word of any lock and is
    invisible to the abstract semantics (the yield is a stutter) -- so the invariant `TInv`,
    mutual exclusion `ticket_ausschluss` and the refinement `ticketLP_sperrAbstrakt` carry over
    to every run of the generated lock; `abgabe_nur_mit_if`: with IF = 0 at the call the spin
    takes no yield at all -- every step is a plain ticket step;
  * `maskiert_inv_erreichbar`, `maskiert_keine_zustellung`, `maskiert_flaggen_zurueck`: on the
    holder's core IF is 0 from the instruction that clears it until the instruction that
    restores it -- through the draw, the whole spin, the critical section and the release --
    so neither an interrupt (delivered only with IF = 1) nor a yield or a timer preemption
    (both only with IF = 1) can take the core in between; and after the release IF is exactly
    the caller's;
  * `flaggen_eigen`: the lock's flag word, shared by every core, hands each holder back the
    value IT stored -- under the abstract lock (`sperrAbstrakt`, which the ticket refines), no
    other thread writes the word between a holder's store and its read;
  * `rcu_inv_erreichbar`, `rcu_gnade_korrekt`: the count is the sum of the readers' nesting
    depths in every reachable state, so a grace wait that reads zero has seen a moment at which
    no reader stood inside any read section; `rcu_ende_ohne_start_waere_falsch` shows that the
    pairing premise is not decoration.

  NOT proved: the C11 orderings (the acquire spin, the release store, the acq_rel reader count)
  -- the memory model is the C and the hardware, the trust every target names; that the
  counters do not wrap (`CTicket.lean`'s 2^32 note, and 2^32 nested readers); starvation of a
  grace wait under a never-empty reader population (OFFEN O32).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL its
  premises jointly.
-/
import Grammatik.CBackend.Semantik.CTicket
namespace Gabbro.Grammatik

namespace MetallSperre

/-! ## 1. `sperre.metall`: the ticket lock with a yield taken only with IF = 1 -/

/-- **ONE STEP OF THE GENERATED SPIN**, by thread `t`. Either an instruction of
    `CTicket.lean`'s ticket lock, or the yield `metall_abgeben` -- which the template takes
    only while `t` waits on a drawn ticket and only when `darf` (the caller's IF was 1 when
    `metall_sperre_nimm` read it, once, before the spin). The yield writes no lock word: the
    state is unchanged. -/
inductive MSchritt (darf : Bool) : TZust → Faden → Option SperrOp → TZust → Prop where
  | ticket {Z Z' : TZust} {t : Faden} {o : Option SperrOp} (hs : TSchritt Z t o Z') :
      MSchritt darf Z t o Z'
  | gibtAb (Z : TZust) (t : Faden) (L m : Nat) (hz : Z.zieht t = some (L, m))
      (hd : darf = true) : MSchritt darf Z t none Z

/-- **THE YIELD IS A STUTTER**: every step is a ticket step, or invisible (`none`) and
    changes nothing. -/
theorem mschritt_ticket_oder_stotter {darf : Bool} {Z Z' : TZust} {t : Faden}
    {o : Option SperrOp} (h : MSchritt darf Z t o Z') :
    TSchritt Z t o Z' ∨ (o = none ∧ Z' = Z) := by
  cases h with
  | ticket hs => exact Or.inl hs
  | gibtAb => exact Or.inr ⟨rfl, rfl⟩

/-- **WITH IF = 0 THERE IS NO YIELD**: every step of the spin is a plain ticket step. -/
theorem abgabe_nur_mit_if {Z Z' : TZust} {t : Faden} {o : Option SperrOp}
    (h : MSchritt false Z t o Z') : TSchritt Z t o Z' := by
  cases h with
  | ticket hs => exact hs
  | gibtAb => contradiction

/-- The invariant survives one step of the generated spin. -/
theorem minv_schritt {darf : Bool} {Z Z' : TZust} {t : Faden} {o : Option SperrOp}
    (hI : TInv Z) (h : MSchritt darf Z t o Z') : TInv Z' := by
  rcases mschritt_ticket_oder_stotter h with hs | ⟨_, rfl⟩
  · exact tinv_schritt hI hs
  · exact hI

/-- Runs of the generated lock: any thread, any step, each thread with its own `darf`. -/
inductive MErreichbar (Z0 : TZust) : TZust → Prop where
  | start : MErreichbar Z0 Z0
  | schritt {Z Z' : TZust} (darf : Faden → Bool) (t : Faden) (o : Option SperrOp) :
      MErreichbar Z0 Z → MSchritt (darf t) Z t o Z' → MErreichbar Z0 Z'

theorem minv_erreichbar {Z0 Z : TZust} (h0 : TInv Z0) (h : MErreichbar Z0 Z) : TInv Z := by
  induction h with
  | start => exact h0
  | schritt darf t o _ hs ih => exact minv_schritt ih hs

/-- **MUTUAL EXCLUSION FOR THE GENERATED LOCK**, on every reachable state. -/
theorem metall_ausschluss {Z0 Z : TZust} (h0 : TInv Z0) (h : MErreichbar Z0 Z)
    {t u L : Faden} (ht : L ∈ Z.haelt t) (hu : L ∈ Z.haelt u) : t = u :=
  ticket_ausschluss (minv_erreichbar h0 h) ht hu

/-- **THE ABSTRACT SEMANTICS SEES ONLY TICKET STEPS**: a visible step (`some op`) of the
    generated spin is a ticket step, so `ticketLP` -- and with it `ticketLP_sperrAbstrakt` --
    covers it unchanged. -/
theorem metall_sichtbar_ist_ticket {darf : Bool} {Z Z' : TZust} {t : Faden} {op : SperrOp}
    (h : MSchritt darf Z t (some op) Z') : TSchritt Z t (some op) Z' := by
  rcases mschritt_ticket_oder_stotter h with hs | ⟨he, _⟩
  · exact hs
  · cases he

/-- A free lock with nobody drawing or holding. -/
def frei : TZust := ⟨fun _ => 0, fun _ => 0, fun _ => none, fun _ => []⟩

theorem frei_inv : TInv frei := by
  refine ⟨fun _ => Nat.le_refl 0, ?_, ?_, ?_, ?_⟩
  · intro t u L m h; cases h
  · intro t L m h; cases h
  · intro t L h; cases h
  · intro t u L h; cases h

/-- **Witness**: thread 1 draws ticket 0 of lock 0, thread 2 draws ticket 1 and YIELDS (its
    IF is 1) -- a real yield step on a reachable state with the invariant. -/
theorem sperre_metall_zeuge :
    let Z1 := zieheT frei 1 0
    let Z2 := zieheT Z1 2 0
    MErreichbar frei Z2 ∧ MSchritt true Z2 2 none Z2 ∧ TInv Z2 := by
  intro Z1 Z2
  have h1 : MErreichbar frei Z1 :=
    MErreichbar.schritt (fun _ => true) 1 none MErreichbar.start
      (MSchritt.ticket (TSchritt.zieht frei 1 0 rfl))
  have h2 : MErreichbar frei Z2 :=
    MErreichbar.schritt (fun _ => true) 2 none h1
      (MSchritt.ticket (TSchritt.zieht Z1 2 0 rfl))
  have hy : MSchritt true Z2 2 none Z2 := MSchritt.gibtAb Z2 2 0 1 rfl rfl
  exact ⟨h2, hy, minv_erreichbar frei_inv h2⟩

/-! ## 2. `sperre.maskiert`: IF = 0 from before the draw until the release has restored it -/

/-- Where the holder stands in `L_nimm` / its section / `L_gib`. -/
inductive Pc where
  | vor       -- before `L_nimm`
  | maskiert  -- after `f = metall_ia_aus()` (pushfq; pop; cli)
  | spinnt    -- after the claim mark, inside `metall_sperre_nimm` (draw, spin)
  | drin      -- after `metall_flaggen_L = f`: the critical section
  | gibt      -- inside `L_gib` after `f = metall_flaggen_L`, before the restore
  | nach      -- after `metall_ia_her(f)`
  deriving DecidableEq

/-- The holder's core: its IF, the local `f`, and the lock's flag word (`metall_flaggen_L`;
    that only the holder writes it between its store and its read is `flaggen_eigen`, §2b). -/
structure Kern where
  pc : Pc
  ia : Bool
  f : Bool
  gespeichert : Bool

/-- **ONE INSTRUCTION ON THE HOLDER'S CORE.** The section's own steps (`rumpf`) leave IF
    alone -- the emitter writes no flag instruction, `N461` keeps a start and its join out of
    a held lock, and a spin with IF = 0 never yields (§1). An interrupt delivery, a yield and
    a timer preemption are core events that need IF = 1 (`zustellung`); they change nothing
    of the holder's state. -/
inductive KSchritt : Kern → Kern → Prop where
  | aus (k : Kern) (h : k.pc = .vor) :
      KSchritt k { k with pc := .maskiert, f := k.ia, ia := false }
  | anspruch (k : Kern) (h : k.pc = .maskiert) : KSchritt k { k with pc := .spinnt }
  | dreht (k : Kern) (h : k.pc = .spinnt) : KSchritt k k
  | tritt (k : Kern) (h : k.pc = .spinnt) :
      KSchritt k { k with pc := .drin, gespeichert := k.f }
  | rumpf (k : Kern) (h : k.pc = .drin) : KSchritt k k
  | liest (k : Kern) (h : k.pc = .drin) :
      KSchritt k { k with pc := .gibt, f := k.gespeichert }
  | her (k : Kern) (h : k.pc = .gibt) : KSchritt k { k with pc := .nach, ia := k.f }
  | zustellung (k : Kern) (h : k.ia = true) : KSchritt k k

/-- The holder's flags before `L_nimm`, at every point of the masked claim. -/
def MInv (i0 : Bool) (k : Kern) : Prop :=
  (k.pc = .vor → k.ia = i0) ∧
  (k.pc = .maskiert → k.ia = false ∧ k.f = i0) ∧
  (k.pc = .spinnt → k.ia = false ∧ k.f = i0) ∧
  (k.pc = .drin → k.ia = false ∧ k.gespeichert = i0) ∧
  (k.pc = .gibt → k.ia = false ∧ k.f = i0) ∧
  (k.pc = .nach → k.ia = i0)

theorem minv_kschritt {i0 : Bool} {k k' : Kern} (hI : MInv i0 k) (hs : KSchritt k k') :
    MInv i0 k' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  cases hs with
  | aus h =>
      refine ⟨fun e => by simp at e, fun _ => ⟨rfl, h1 h⟩, fun e => by simp at e,
        fun e => by simp at e, fun e => by simp at e, fun e => by simp at e⟩
  | anspruch h =>
      refine ⟨fun e => by simp at e, fun e => by simp at e, fun _ => h2 h,
        fun e => by simp at e, fun e => by simp at e, fun e => by simp at e⟩
  | dreht h => exact ⟨h1, h2, h3, h4, h5, h6⟩
  | tritt h =>
      refine ⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e,
        fun _ => ⟨(h3 h).1, (h3 h).2⟩, fun e => by simp at e, fun e => by simp at e⟩
  | rumpf h => exact ⟨h1, h2, h3, h4, h5, h6⟩
  | liest h =>
      refine ⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e,
        fun e => by simp at e, fun _ => ⟨(h4 h).1, (h4 h).2⟩, fun e => by simp at e⟩
  | her h =>
      refine ⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e,
        fun e => by simp at e, fun e => by simp at e, fun _ => (h5 h).2⟩
  | zustellung h => exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Runs of the holder's core from `L_nimm`'s entry with IF = `i0`. -/
inductive KErreichbar (k0 : Kern) : Kern → Prop where
  | start : KErreichbar k0 k0
  | schritt {k k' : Kern} : KErreichbar k0 k → KSchritt k k' → KErreichbar k0 k'

theorem maskiert_inv_erreichbar {k0 k : Kern} (h0 : k0.pc = .vor) (h : KErreichbar k0 k) :
    MInv k0.ia k := by
  induction h with
  | start =>
      refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [h0] at e <;> cases e
  | schritt _ hs ih => exact minv_kschritt ih hs

/-- **NO INTERRUPT, NO YIELD, NO PREEMPTION ON THE HOLDER'S CORE**: from the `cli` of
    `L_nimm` until the restore of `L_gib` -- the draw, the whole spin, the section, the release
    -- IF is 0, so the core event `zustellung` (which needs IF = 1) cannot happen there. -/
theorem maskiert_keine_zustellung {k0 k : Kern} (h0 : k0.pc = .vor) (h : KErreichbar k0 k)
    (hp : k.pc = .maskiert ∨ k.pc = .spinnt ∨ k.pc = .drin ∨ k.pc = .gibt) : k.ia = false := by
  obtain ⟨_, h2, h3, h4, h5, _⟩ := maskiert_inv_erreichbar h0 h
  rcases hp with e | e | e | e
  · exact (h2 e).1
  · exact (h3 e).1
  · exact (h4 e).1
  · exact (h5 e).1

/-- **THE CALLER'S FLAGS COME BACK**: after `L_gib`, IF is what it was before `L_nimm`. -/
theorem maskiert_flaggen_zurueck {k0 k : Kern} (h0 : k0.pc = .vor) (h : KErreichbar k0 k)
    (hp : k.pc = .nach) : k.ia = k0.ia :=
  (maskiert_inv_erreichbar h0 h).2.2.2.2.2 hp

/-- **Witness**: a caller with IF = 1 runs the whole masked claim to its end -- every step
    taken, an interrupt delivered BEFORE the claim (IF = 1 there), IF = 0 in the section, and
    IF = 1 again afterwards. -/
theorem sperre_maskiert_zeuge :
    let k0 : Kern := ⟨.vor, true, false, false⟩
    let kd : Kern := ⟨.drin, false, true, true⟩
    let kn : Kern := ⟨.nach, true, true, true⟩
    KErreichbar k0 kd ∧ KErreichbar k0 kn ∧ kd.ia = false ∧ kn.ia = k0.ia := by
  intro k0 kd kn
  have a : KErreichbar k0 k0 := KErreichbar.start
  have b := KErreichbar.schritt a (KSchritt.zustellung k0 rfl)
  have c := KErreichbar.schritt b (KSchritt.aus k0 rfl)
  have d := KErreichbar.schritt c (KSchritt.anspruch _ rfl)
  have e := KErreichbar.schritt d (KSchritt.dreht _ rfl)
  have f := KErreichbar.schritt e (KSchritt.tritt _ rfl)
  have g := KErreichbar.schritt f (KSchritt.rumpf _ rfl)
  have i := KErreichbar.schritt g (KSchritt.liest _ rfl)
  have j := KErreichbar.schritt i (KSchritt.her _ rfl)
  refine ⟨g, j, rfl, rfl⟩

/-! ### 2b. The lock's flag word hands every holder back its own store -/

/-- The abstract lock (`sperrAbstrakt`, which `ticketLP_sperrAbstrakt` refines) and the
    flag word: `eigen t` is what `t` stored during its current hold. -/
structure FZ where
  halter : Option Faden
  wort : Bool
  eigen : Faden → Option Bool

inductive FSchritt : FZ → FZ → Prop where
  | nimm (z : FZ) (t : Faden) (h : z.halter = none) :
      FSchritt z { z with halter := some t, eigen := aendere z.eigen t none }
  | schreibt (z : FZ) (t : Faden) (v : Bool) (h : z.halter = some t) :
      FSchritt z { z with wort := v, eigen := aendere z.eigen t (some v) }
  | gib (z : FZ) (t : Faden) (h : z.halter = some t) :
      FSchritt z { z with halter := none, eigen := aendere z.eigen t none }

def FInv (z : FZ) : Prop := ∀ t v, z.eigen t = some v → z.halter = some t ∧ z.wort = v

theorem finv_schritt {z z' : FZ} (hI : FInv z) (hs : FSchritt z z') : FInv z' := by
  cases hs with
  | nimm t h =>
      intro u v hu
      by_cases e : u = t
      · subst e; simp [aendere_eq] at hu
      · have := hI u v (by simpa [aendere_ne _ _ _ _ e] using hu)
        rw [h] at this; cases this.1
  | schreibt t v h =>
      intro u w hu
      by_cases e : u = t
      · subst e
        have hu' : aendere z.eigen u (some v) u = some w := hu
        rw [aendere_eq] at hu'
        cases hu'
        exact ⟨h, rfl⟩
      · have := hI u w (by simpa [aendere_ne _ _ _ _ e] using hu)
        rw [h] at this
        exact absurd (Option.some.inj this.1).symm e
  | gib t h =>
      intro u v hu
      by_cases e : u = t
      · subst e; simp [aendere_eq] at hu
      · have := hI u v (by simpa [aendere_ne _ _ _ _ e] using hu)
        rw [h] at this
        exact absurd (Option.some.inj this.1).symm e

inductive FErreichbar (z0 : FZ) : FZ → Prop where
  | start : FErreichbar z0 z0
  | schritt {z z' : FZ} : FErreichbar z0 z → FSchritt z z' → FErreichbar z0 z'

theorem finv_erreichbar {z0 z : FZ} (h0 : FInv z0) (h : FErreichbar z0 z) : FInv z := by
  induction h with
  | start => exact h0
  | schritt _ hs ih => exact finv_schritt ih hs

/-- **THE READ IN `L_gib` RETURNS THE HOLDER'S OWN STORE**, however the cores interleave. -/
theorem flaggen_eigen {z0 z : FZ} (h0 : FInv z0) (h : FErreichbar z0 z) {t : Faden} {v : Bool}
    (he : z.eigen t = some v) : z.wort = v :=
  (finv_erreichbar h0 h t v he).2

/-- **Witness**: thread 1 holds and stores `true`, releases; thread 2 takes the lock and
    stores `false` -- each reads its own value. -/
theorem flaggen_zeuge :
    let z0 : FZ := ⟨none, false, fun _ => none⟩
    let z1 : FZ := { z0 with halter := some 1, eigen := aendere z0.eigen 1 none }
    let z2 : FZ := { z1 with wort := true, eigen := aendere z1.eigen 1 (some true) }
    let z3 : FZ := { z2 with halter := none, eigen := aendere z2.eigen 1 none }
    let z4 : FZ := { z3 with halter := some 2, eigen := aendere z3.eigen 2 none }
    let z5 : FZ := { z4 with wort := false, eigen := aendere z4.eigen 2 (some false) }
    FInv z0 ∧ FErreichbar z0 z2 ∧ z2.eigen 1 = some true ∧ FErreichbar z0 z5 ∧
      z5.eigen 2 = some false := by
  intro z0 z1 z2 z3 z4 z5
  have h0 : FInv z0 := fun _ _ h => by cases h
  have a1 := FErreichbar.schritt (FErreichbar.start (z0 := z0)) (FSchritt.nimm z0 1 rfl)
  have a2 := FErreichbar.schritt a1 (FSchritt.schreibt z1 1 true rfl)
  have a3 := FErreichbar.schritt a2 (FSchritt.gib z2 1 rfl)
  have a4 := FErreichbar.schritt a3 (FSchritt.nimm z3 2 rfl)
  have a5 := FErreichbar.schritt a4 (FSchritt.schreibt z4 2 false rfl)
  exact ⟨h0, a2, rfl, a5, rfl⟩

/-! ## 3. `rcu.metall`: the count is the readers' total depth -/

/-- The sum of `f 0 .. f (n-1)`. -/
def summe (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => summe f n + f n

theorem summe_aendere_ausser (f : Nat → Nat) (i v : Nat) :
    ∀ n, n ≤ i → summe (aendere f i v) n = summe f n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [summe]
      rw [summe_aendere_ausser f i v n (Nat.le_of_succ_le h),
        aendere_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_of_succ_le h))]

theorem summe_aendere (f : Nat → Nat) (i v : Nat) :
    ∀ n, i < n → summe (aendere f i v) n + f i = summe f n + v
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
      simp only [summe]
      by_cases e : i = n
      · subst e
        rw [summe_aendere_ausser f i v i (Nat.le_refl _), aendere_eq]
        omega
      · have hi : i < n := by omega
        have ih := summe_aendere f i v n hi
        rw [aendere_ne _ _ _ _ (Ne.symm e)]
        omega

theorem summe_null (f : Nat → Nat) : ∀ n, summe f n = 0 → ∀ i, i < n → f i = 0
  | 0, _, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
      simp only [summe] at h
      by_cases e : i = n
      · subst e; omega
      · exact summe_null f n (by omega) i (by omega)

/-- The domain's reader count and each of the `n` threads' nesting depth. -/
structure RZ where
  zahl : Nat
  tiefe : Nat → Nat

/-- `R_lese_start` (`+1`) and `R_lese_ende` (`-1`) by thread `i < n`; the end only inside a
    read section (the emitter pairs every start with its end -- `rcu_ende_ohne_start_waere_falsch`
    shows the premise is needed). -/
inductive RSchritt (n : Nat) : RZ → RZ → Prop where
  | start (z : RZ) (i : Nat) (hi : i < n) :
      RSchritt n z ⟨z.zahl + 1, aendere z.tiefe i (z.tiefe i + 1)⟩
  | ende (z : RZ) (i k : Nat) (hi : i < n) (hk : z.tiefe i = k + 1) :
      RSchritt n z ⟨z.zahl - 1, aendere z.tiefe i k⟩

def RInv (n : Nat) (z : RZ) : Prop := z.zahl = summe z.tiefe n

theorem rinv_schritt {n : Nat} {z z' : RZ} (hI : RInv n z) (hs : RSchritt n z z') :
    RInv n z' := by
  unfold RInv at *
  cases hs with
  | start i hi =>
      have := summe_aendere z.tiefe i (z.tiefe i + 1) n hi
      show z.zahl + 1 = summe (aendere z.tiefe i (z.tiefe i + 1)) n
      omega
  | ende i k hi hk =>
      have := summe_aendere z.tiefe i k n hi
      show z.zahl - 1 = summe (aendere z.tiefe i k) n
      omega

inductive RErreichbar (n : Nat) (z0 : RZ) : RZ → Prop where
  | start : RErreichbar n z0 z0
  | schritt {z z' : RZ} : RErreichbar n z0 z → RSchritt n z z' → RErreichbar n z0 z'

theorem rcu_inv_erreichbar {n : Nat} {z : RZ} (h : RErreichbar n ⟨0, fun _ => 0⟩ z) :
    RInv n z := by
  induction h with
  | start =>
      show 0 = summe (fun _ => 0) n
      induction n with
      | zero => rfl
      | succ m ih => simp only [summe]; exact ih
  | schritt _ hs ih => exact rinv_schritt ih hs

/-- **THE GRACE WAIT IS RIGHT WHEN IT RETURNS**: at the moment `metall_rcu_gnade_R` reads a
    zero count, no thread stands inside any read section of the domain. -/
theorem rcu_gnade_korrekt {n : Nat} {z : RZ} (h : RErreichbar n ⟨0, fun _ => 0⟩ z)
    (h0 : z.zahl = 0) : ∀ i, i < n → z.tiefe i = 0 := by
  have hI := rcu_inv_erreichbar h
  unfold RInv at hI
  exact summe_null z.tiefe n (hI ▸ h0)

/-- The same count WITHOUT the pairing premise: an end by a thread that is in no read
    section. -/
inductive RSchrittRoh (n : Nat) : RZ → RZ → Prop where
  | echt {z z' : RZ} (hs : RSchritt n z z') : RSchrittRoh n z z'
  | endeRoh (z : RZ) (i : Nat) (hi : i < n) :
      RSchrittRoh n z ⟨z.zahl - 1, aendere z.tiefe i (z.tiefe i - 1)⟩

inductive RErreichbarRoh (n : Nat) (z0 : RZ) : RZ → Prop where
  | start : RErreichbarRoh n z0 z0
  | schritt {z z' : RZ} : RErreichbarRoh n z0 z → RSchrittRoh n z z' → RErreichbarRoh n z0 z'

/-- **The pairing premise is not decoration**: thread 1 starts a read, then thread 0 -- in no
    read section -- ends one. The count reads 0 while thread 1 is inside: a grace wait would
    return under a live reader. -/
theorem rcu_ende_ohne_start_waere_falsch :
    ∃ z, RErreichbarRoh 2 ⟨0, fun _ => 0⟩ z ∧ z.zahl = 0 ∧ z.tiefe 1 = 1 := by
  let z0 : RZ := ⟨0, fun _ => 0⟩
  let z1 : RZ := ⟨1, aendere z0.tiefe 1 1⟩
  have a1 : RErreichbarRoh 2 z0 z1 :=
    RErreichbarRoh.schritt RErreichbarRoh.start (RSchrittRoh.echt (RSchritt.start z0 1 (by decide)))
  have a2 := RErreichbarRoh.schritt a1 (RSchrittRoh.endeRoh z1 0 (by decide))
  exact ⟨_, a2, rfl, rfl⟩

/-- **Witness**: two threads, nested reads by thread 0, one read by thread 1, all ended --
    reachable, count zero, nobody inside; and an intermediate state with count 3. -/
theorem rcu_zeuge :
    let z0 : RZ := ⟨0, fun _ => 0⟩
    let z1 : RZ := ⟨1, aendere z0.tiefe 0 1⟩
    let z2 : RZ := ⟨2, aendere z1.tiefe 0 2⟩
    let z3 : RZ := ⟨3, aendere z2.tiefe 1 1⟩
    RErreichbar 2 z0 z3 ∧ RInv 2 z3 ∧ z3.zahl = 3 ∧
      (∀ z, RErreichbar 2 z0 z → z.zahl = 0 → ∀ i, i < 2 → z.tiefe i = 0) := by
  intro z0 z1 z2 z3
  have a1 := RErreichbar.schritt (RErreichbar.start (n := 2) (z0 := z0)) (RSchritt.start z0 0 (by decide))
  have a2 := RErreichbar.schritt a1 (RSchritt.start z1 0 (by decide))
  have a3 := RErreichbar.schritt a2 (RSchritt.start z2 1 (by decide))
  exact ⟨a3, rcu_inv_erreichbar a3, rfl, fun z h h0 => rcu_gnade_korrekt h h0⟩

end MetallSperre

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.MetallSperre.mschritt_ticket_oder_stotter
#print axioms Gabbro.Grammatik.MetallSperre.abgabe_nur_mit_if
#print axioms Gabbro.Grammatik.MetallSperre.metall_ausschluss
#print axioms Gabbro.Grammatik.MetallSperre.metall_sichtbar_ist_ticket
#print axioms Gabbro.Grammatik.MetallSperre.sperre_metall_zeuge
#print axioms Gabbro.Grammatik.MetallSperre.maskiert_keine_zustellung
#print axioms Gabbro.Grammatik.MetallSperre.maskiert_flaggen_zurueck
#print axioms Gabbro.Grammatik.MetallSperre.sperre_maskiert_zeuge
#print axioms Gabbro.Grammatik.MetallSperre.flaggen_eigen
#print axioms Gabbro.Grammatik.MetallSperre.flaggen_zeuge
#print axioms Gabbro.Grammatik.MetallSperre.rcu_gnade_korrekt
#print axioms Gabbro.Grammatik.MetallSperre.rcu_ende_ohne_start_waere_falsch
#print axioms Gabbro.Grammatik.MetallSperre.rcu_zeuge
