/-
  File:      Grammatik/Maschine.lean
  Subject:   **THE MACHINE** -- threads STARTED over the grammar, interleaved by the
             scheduler; every reachable run yields its worlds and its order from that
             construction, never from a separately asserted link.

  ## The model

  A thread is a STARTED body: its full event trace is what one `exec` run yields from
  the empty trace (`MaschinenFaden`, closed per body by `exec_spur` -- the per-thread
  `Brav` provenance). A machine run (`MaschinenLauf`) is the scheduler's interleaving  of started threads over the grammar:

    * `hvoll` -- every thread started (per-thread `Brav` from the empty trace),
    * `hvers` -- the run interleaves the full traces (`IstVerschraenkung`: every
      observed per-thread trace is a tail of its full trace),
    * `hausschluss` -- (W3) the scheduler rule: who takes a lock takes it while no
      other thread holds it (`ForeignExclusion`, the foreign-lock promise),
    * `hEin` -- (W4) the construction: single-threadedness over the projected run
      (`Marken.Einfaedig`, the Verlauf side),
    * `hungeteilt` -- (W5) the declaration side: an unshared carrier belongs to one
      thread.

  A `MaschinenLauf` IS a reachable run: started threads plus scheduler interleaving.
  `maschinenLeer` is the reachable base (threads started, zero steps taken).

  ## The theorems

    `maschinenWelten`     -- event-to-world: the worlds a real run produces, by
                             folding the run's own events onto the start world
    `w1w2w4_aus_maschine` -- W1/W2/W4 for every reachable run (W1+W2 from the
                             grammar side via `lauf_aus_brav`; W4 from the
                             construction via `marke_eindeutig_aus_einfaedig`)
    `reduktion_maschine`  -- REAL reduction, Lipton sense, order fragment: two
                             conflicting sections of a machine run admit a serial
                             order, via `reduktion_seriell` with `Gesittet`
                             derived from the machine itself
                             (`gesittet_aus_maschine`). The witnesses are run
                             positions; no chain object and no `SerialLink`-style
                             premise appear anywhere.

  Port note: adapted from the WIP `Maschine.lean` at `85cb4f4` (branch
  `wip/maschine-pflicht-2026-09-11`, read-only, stale base, NOT merged) onto the
  current core -- 5-field `Gesittet` with `ungeteilt`, 3-tuple `Brav`, `geteilt`
  still declared. The portable WIP sections (thread shapes, scheduler, start) are
  rebuilt here as data; the W1/W2/W4 derivations go through the current bridge
  (`lauf_aus_brav`, `bruecke_exec_gesittet`) instead of the WIP's reshaped core.
  Read-only inputs: `PORT-MASCHINE.md` (lane-110 audit), `PORT-MIGRATION.md`
  (lane-112), `PORT-SYNTAX.md` (lane-111), `PORT-PFLICHT.md` (lane-113).
  Sibling theorems used read-only, never modified: `reduktion_seriell`,
  `mover_nonwriter_past`, `wache_aus_schuld` (`InterferenzAllgemein.lean`
  sections 21-22).
-/
import Grammatik.Wettlauf
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Started threads -- thread start over the grammar -/

/-- A STARTED thread: its full trace is what a body yields from the empty trace.
    The `start` witness is closed per body by `exec_spur`
    (see `MaschinenFaden.spawn` below). -/
structure MaschinenFaden (D : Deklaration) where
  faden : Faden
  voll : List (Ereignis D)
  start : ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll

variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **Thread start.** Running a body from an empty-trace world starts a thread:
    the outcome world carries the full trace with `Brav` provenance from empty
    (`exec_spur` read as `Brav`, the same step `Ziel.lean` closes per body). -/
def MaschinenFaden.spawn (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (hO : GutO O) (f : Faden) (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hh : HeldGenau Λ σ.haelt) (hempty : σ.spur = [])
    (σ' : World D) (h : (exec P O passes fuel V b σ ρ).welt = some σ') :
    MaschinenFaden D :=
  ⟨f, σ'.spur, σ, σ', hempty, exec_spur P O passes fuel hO b σ ρ hh σ' h, rfl⟩

/-! ## 2. The machine run -- interleaving over the grammar, reachable by construction -/

/-- **The machine run.** Started threads (`hvoll`), interleaved by the scheduler
    (`hvers`), under the scheduler rule (W3, `hausschluss`), the single-thread
    construction (W4, `hEin`), and the declaration side (W5, `hungeteilt`).
    Every inhabitant is a reachable run: there is no other way to build one. -/
structure MaschinenLauf (D : Deklaration) where
  run : Lauf D
  voll : Faden → List (Ereignis D)
  code : D.Marke → Nat
  start : World D
  hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f
  hvers : IstVerschraenkung run voll
  hausschluss : ForeignExclusion run
  hEin : Marken.Einfaedig (laufProj code run)
  hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
    (ei ej : Ereignis D),
    run[i]? = some (Schritt.mk f ei) → run[j]? = some (Schritt.mk g ej) →
    ei.traeger = some o → ej.traeger = some o →
    (match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false) → f = g

/-- **The reachable base.** Threads started, zero steps taken: the empty run
    observes the empty tail of every full trace. -/
def maschinenLeer (voll : Faden → List (Ereignis D)) (code : D.Marke → Nat)
    (σ₀ : World D)
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hausschluss : ForeignExclusion ([] : Lauf D))
    (hEin : Marken.Einfaedig (laufProj code []))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      ([] : Lauf D)[i]? = some (Schritt.mk f ei) →
      ([] : Lauf D)[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    MaschinenLauf D :=
  { run := [], voll := voll, code := code, start := σ₀, hvoll := hvoll,
    hvers := fun f j => ⟨(voll f).length, by rw [List.drop_length]; simp [Lauf.spur]⟩,
    hausschluss := hausschluss, hEin := hEin, hungeteilt := hungeteilt }

/-! ## 3. Event-to-world -- which worlds and events a real run produces -/

/-- The world list of a run: the start world, then one world per step, each
    recording exactly its step event (`merke [e]`, newest first -- the same
    convention as every per-thread `spur`). -/
def weltenFalte : World D → Lauf D → List (World D)
  | σ, [] => [σ]
  | σ, s :: rest => σ :: weltenFalte (σ.merke [s.ereignis]) rest

/-- **Event-to-world.** The worlds a real run produces: folding the run's own
    events onto the machine's start world. No chain object contributes worlds;
    the run fixes them step by step. -/
def maschinenWelten (M : MaschinenLauf D) : List (World D) :=
  weltenFalte M.start M.run

/-- The end world of the fold, as a single world (the last element of the list). -/
def weltenEnde (σ : World D) (run : Lauf D) : World D :=
  run.foldl (fun w s => w.merke [s.ereignis]) σ

theorem weltenFalte_laenge (σ : World D) (run : Lauf D) :
    (weltenFalte σ run).length = run.length + 1 := by
  induction run generalizing σ with
  | nil => rfl
  | cons s rest ih => simp [weltenFalte, ih]

/-- One world per step, plus the start world. -/
theorem maschinenWelten_laenge (M : MaschinenLauf D) :
    (maschinenWelten M).length = M.run.length + 1 :=
  weltenFalte_laenge M.start M.run

/-- The end world records every run event exactly once, newest first. -/
theorem weltenEnde_spur (run : Lauf D) (σ : World D) :
    (weltenEnde σ run).spur = (run.map Schritt.ereignis).reverse ++ σ.spur := by
  unfold weltenEnde
  induction run generalizing σ with
  | nil => simp [World.merke]
  | cons s rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.reverse_cons]
      rw [ih]
      simp [World.merke, List.append_assoc]

/-- The list ends at the folded end world. -/
theorem weltenFalte_ende (σ : World D) (run : Lauf D) :
    (weltenFalte σ run).getLast? = some (weltenEnde σ run) := by
  induction run generalizing σ with
  | nil => rfl
  | cons s rest ih =>
      have htail := ih (σ.merke [s.ereignis])
      simp only [weltenFalte, weltenEnde, List.foldl_cons] at htail ⊢
      cases h : weltenFalte (σ.merke [s.ereignis]) rest with
      | nil =>
          have hlen := weltenFalte_laenge (σ.merke [s.ereignis]) rest
          rw [h] at hlen
          simp at hlen
      | cons w ws =>
          rw [h] at htail
          rwa [List.getLast?_cons_cons] at ⊢

/-- The last machine world records every run event exactly once, newest first. -/
theorem maschinenWelten_letzte_spur (M : MaschinenLauf D) :
    ((maschinenWelten M).getLast?.map World.spur) =
      some ((M.run.map Schritt.ereignis).reverse ++ M.start.spur) := by
  unfold maschinenWelten
  rw [weltenFalte_ende, Option.map_some, weltenEnde_spur]

/-- Every step event of the run is good: it sits in its thread's observed trace,
    hence in the full trace, hence `Brav.gut_von_leer` applies. -/
theorem schritt_ereignis_gut (run : Lauf D)
    (hg : ∀ f j (e : Ereignis D), e ∈ run.spur f j → e.gut)
    (s : Schritt D) (hs : s ∈ run) : s.ereignis.gut := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hs
  cases s with
  | mk f e =>
      have hmem : e ∈ run.spur f (k + 1) := by
        rw [run.spur_succ_eigen f k e hk]
        exact List.mem_cons_self
      exact hg f (k + 1) e hmem

/-- Every world a run produces observes only start events or good events: the
    observations of a real run are good. -/
theorem weltenFalte_gut (run : Lauf D) (σ : World D)
    (hg : ∀ s ∈ run, s.ereignis.gut) :
    ∀ W ∈ weltenFalte σ run, ∀ e ∈ W.spur, e ∈ σ.spur ∨ e.gut := by
  induction run generalizing σ with
  | nil =>
      intro W hW e he
      simp only [weltenFalte, List.mem_singleton] at hW
      subst hW
      exact Or.inl he
  | cons s rest ih =>
      intro W hW e he
      simp only [weltenFalte, List.mem_cons] at hW
      rcases hW with rfl | hW
      · exact Or.inl he
      · have hrest : ∀ s' ∈ rest, s'.ereignis.gut :=
          fun s' hs' => hg s' (List.mem_cons_of_mem _ hs')
        have hW' := ih (σ.merke [s.ereignis]) hrest W hW e he
        rcases hW' with h | h
        · simp only [World.merke, List.mem_append, List.mem_singleton] at h
          rcases h with rfl | h
          · exact Or.inr (hg s List.mem_cons_self)
          · exact Or.inl h
        · exact Or.inr h

/-- The observations of every reachable run are good (W2 at world level). -/
theorem maschinenWelten_gut (M : MaschinenLauf D) :
    ∀ W ∈ maschinenWelten M, ∀ e ∈ W.spur, e ∈ M.start.spur ∨ e.gut := by
  obtain ⟨_, hgut⟩ := lauf_aus_brav M.run M.voll M.hvoll M.hvers
  exact weltenFalte_gut M.run M.start
    (fun s hs => schritt_ereignis_gut M.run (fun f j e he => hgut f j e he) s hs)

/-! ## 4. W1/W2/W4 for every reachable run -/

/-- **W1, W2, W4 for every reachable run.** W1+W2 come from the grammar side
    (`lauf_aus_brav`: per-thread `Brav` from empty traces, inherited over the
    interleaved tails); W4 comes from the construction
    (`marke_eindeutig_aus_einfaedig`: `Einfaedig` over the projected run IS
    `marke_eindeutig` over the real run). W3 travels as the scheduler rule
    (`hausschluss`), W5 as the declaration side (`hungeteilt`) -- neither is
    derived here, exactly as the bridge books them. -/
theorem w1w2w4_aus_maschine (M : MaschinenLauf D) :
    (∀ f j, Konsistent (M.run.spur f j)) ∧
    (∀ f j (e : Ereignis D), e ∈ M.run.spur f j → e.gut) ∧
    (∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
      M.run[i]? = some (Schritt.mk f ei) → M.run[j]? = some (Schritt.mk g ej) →
      Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g) := by
  obtain ⟨hkons, hgut⟩ := lauf_aus_brav M.run M.voll M.hvoll M.hvers
  exact ⟨hkons, hgut, marke_eindeutig_aus_einfaedig M.code M.run M.hEin⟩

/-- **The machine run is `Gesittet`.** The bridge (`bruecke_exec_gesittet`) over
    the machine's own fields: per-thread provenance plus interleaving shape
    (W1, W2), scheduler rule (W3), construction (W4), declaration side (W5).
    This is what `reduktion_maschine` consumes -- derived, never assumed. -/
theorem gesittet_aus_maschine (M : MaschinenLauf D) : Gesittet M.run :=
  bruecke_exec_gesittet M.run M.voll M.hvoll M.hvers M.hausschluss M.code M.hEin
    M.hungeteilt

/-! ## 5. Real reduction, Lipton sense -- every machine run admits the serial order

  The serial unit is the whole section (grain, section 21 `schritt_rahmen_aus_korn`
  read-only: at event grain the invariant breaks mid-step; at section grain each
  step re-establishes what it owes). At order level the reduction IS the serial
  order (`InterferenzAllgemein.lean` section 22, read-only): two conflicting
  sections are happens-before ordered in the run, in one direction or the other.

  What is proved (`reduktion_maschine` below, no `sorry`):

    - the run, the discipline, and the witnesses all come from the machine: the
      two conflicting accesses are positions in `M.run` itself, and `Gesittet`
      is derived from the machine (`gesittet_aus_maschine`). There is no chain
      object `J`, no order-faithfulness premise, and no `SerialLink`-style link
      to assert per use -- the exact bare-link premise section 22 still carries
      is gone because there is nothing left to link: worlds come from
      `maschinenWelten`, order from `reduktion_seriell` over the machine run.

  Coverage (exactly): single shared TABLE carrier, whole-section grain at order
  level, two conflicting accesses, race-free machine runs. Table-scoped because
  `wache_aus_schuld` (section 21, from `SchuldnerHaelt` via U003) is
  table-scoped; shared globals stay on the section 13-15 exception track.

  Remainder (booked, not hidden):

    - Full observation equality -- the serial world sequence carrying the same
      observations -- needs chain worlds: `mover_nonwriter_past` and
      `wache_aus_schuld` both take a `GemeinsamerLauf`, and the machine supplies
      run worlds, not chain worlds. Both theorems were read, not modified; the
      chain-to-machine wiring is the open lane (it consumes exactly this file's
      `maschinenWelten`, `w1w2w4_aus_maschine`, `reduktion_maschine`).
    - More than two conflicting sections (pairwise HB orders folded into one
      global serial schedule), restoring writers, and non-uniform invariant form
      carry over from the section 22 remainder unchanged.
-/

/-- **Reduction, serial order, from the machine (two-access single-carrier
    fragment).** Two conflicting accesses in a machine run are happens-before
    ordered, in one direction or the other: the conflict admits a serial order.
    Both directions close via `reduktion_seriell` (read-only) with `Gesittet`
    derived from the machine; the equal-index case contradicts the distinct
    threads inside `reduktion_seriell` itself. -/
theorem reduktion_maschine (M : MaschinenLauf D) (t₀ : D.Tab) (g₁ g₂ : Faden)
    (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB M.run j₁ j₂ ∨ HB M.run j₂ j₁ :=
  reduktion_seriell M.run (gesittet_aus_maschine M) t₀ g₁ g₂ hne j₁ j₂ w₁ w₂
    Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.MaschinenFaden.spawn
#print axioms Gabbro.Grammatik.maschinenLeer
#print axioms Gabbro.Grammatik.maschinenWelten
#print axioms Gabbro.Grammatik.maschinenWelten_laenge
#print axioms Gabbro.Grammatik.maschinenWelten_letzte_spur
#print axioms Gabbro.Grammatik.maschinenWelten_gut
#print axioms Gabbro.Grammatik.w1w2w4_aus_maschine
#print axioms Gabbro.Grammatik.gesittet_aus_maschine
#print axioms Gabbro.Grammatik.reduktion_maschine

end Gabbro.Grammatik
