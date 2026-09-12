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

  Mechanism (k02 `Schrittrelation`, §§6-11): the step relation over shared
  memory (`GenSchritt`: one leaf statement through `execStmt`, `locks L` as
  scheduler rule), inductive reachability from start worlds (`GenErreichbar`),
  and the world history with live memory (`GenMaschine.welten`). A write step
  moves memory by construction (`schreibt_wirkt_*`, `gen_write_glob_moves`);
  the old fold's constant-memory shape is kept below as the NEGATIVE example
  (`maschinenWelten_speicher_gleich`). Reachable runs yield W1/W2 plus the
  scheduler rule (`gen_konsistent`, `gen_gut_obs`, `gen_ausschluss`); W4/W5
  stay explicit construction/declaration premises (`gen_w1w2w4`,
  `gen_gesittet`, `gen_reduktion`), exactly as the bridge books them.

  Compatibility: §§1-5 below are the premise-structure (`MaschinenLauf`),
  kept byte-identical for the consumer (`Ziel.lean` §9 uses every field and
  theorem). It is DEPRECATED in favour of §§6-11: new work builds generated
  runs; the structure stays only so nothing breaks.

  Remainder (booked, not hidden): §12 threads program counters through the
  generated machine -- positions with footprints, the `Einfaedig` projection
  premise discharged from program text (`pc_discharge_einfaedig`) and the
  declaration side likewise (`pc_discharge_unshared`). What stays open: full
  `Block` continuations (`ite` arms, call stacks, loop resumption as explicit
  continuation objects) and the run-to-`Bau` wiring for `Geteilt.lean`.
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
    Every inhabitant is a reachable run: there is no other way to build one.

    DEPRECATED in favour of §7 (`GenSchritt`) and §10 (`GenErreichbar`): this
    structure hands reachability as premises instead of generating it. Kept
    because `Ziel.lean` §9 consumes every field; new work builds generated runs. -/
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

/-! ## 6. Shared memory -- the half `merke` never touches

   `World.merke` extends only the trace (`Semantik.lean`: `{ σ with spur := ... }`):
   slots and globals ride along unchanged. Section 9 keeps that constant-memory
   shape as the NEGATIVE example (`maschinenWelten_speicher_gleich`); the steps
   below escape it because they go through `execStmt`, whose writes
   (`schreibSlot`, `schreibGlob`) replace slots and globals. -/

/-- The shared memory of all threads: slots and globals, without a trace. -/
structure Speicher (D : Deklaration) where
  slots : ∀ t : D.Tab, Int → ∀ f : D.Feld t, Wert D (D.typ t f)
  globs : ∀ g : D.Glob, Wert D (D.gtyp g)

/-- A memory plus a trace is a world; a world splits into memory plus trace. -/
def Speicher.welt (s : Speicher D) (spur : List (Ereignis D)) : World D :=
  ⟨s.slots, s.globs, spur⟩

def World.speicher (σ : World D) : Speicher D := ⟨σ.slots, σ.globs⟩

theorem Speicher.welt_speicher (σ : World D) : σ.speicher.welt σ.spur = σ := by
  cases σ
  rfl

/-! ## 7. One thread step over shared memory: leaf statements plus the lock rule

   A thread step executes ONE leaf statement through `execStmt` -- the same
   evaluator `Satz.lean` proves frame and trace for (`stmt_gut`) -- starting
   from the thread's current world (shared memory plus its own trace). A real
   write changes slots/globs (§9); reads only extend the trace. `locks L` is
   the one step that looks at ANOTHER thread: `nimmt` fires only while no other
   thread holds `L` (`GenFrei`), which is the lock as scheduler rule. -/

/-- Leaf statements never consult the call handler: this `R` is never asked. -/
def keinRuf : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f :=
  fun f _ _ => .logik (.abstieg f)

theorem keinRuf_gut : GutR (D := D) keinRuf := by
  intro f σ ρ _ σ' h
  simp [keinRuf, RufAusgang.welt] at h

/-- Leaf or compound. A thread step executes one leaf; compound statements
    (`ite`, calls, `locks`, loops, ...) open into further steps instead. -/
def Stmt.istBlatt : Stmt D V l Γ Λ Λ' → Bool
  | .ite .. | .onOption .. | .onTag .. | .onGrund .. | .call .. | .callInd ..
  | .locks .. | .breaking .. | .traverse .. | .retry .. | .forever .. => false
  | _ => true

/-- The generated machine: shared memory, one trace per thread, the run so far,
    the start world, the world history (one entry per step, with live memory),
    and the step count. -/
structure GenMaschine (D : Deklaration) where
  speicher : Speicher D
  spuren : Faden → List (Ereignis D)
  lauf : Lauf D
  start : World D
  welten : List (World D)
  tiefe : Nat

/-- The current world of thread `f`: live shared memory plus its own trace. -/
def GenMaschine.weltVon (M : GenMaschine D) (f : Faden) : World D :=
  M.speicher.welt (M.spuren f)

/-- No thread other than `f` holds `L` right now -- the scheduler rule side. -/
def GenFrei (M : GenMaschine D) (f : Faden) (L : D.Lock) : Prop :=
  ∀ g, g ≠ f → L ∉ offen (M.spuren g)

/-- The new run events of one step, all attributed to the acting thread. -/
def genEigen (f : Faden) (neu : List (Ereignis D)) : Lauf D :=
  neu.reverse.map fun e => Schritt.mk f e

/-- One thread's trace replaced, all others kept. -/
def genUpdate (m : Faden → List (Ereignis D)) (f : Faden) (s : List (Ereignis D)) :
    Faden → List (Ereignis D) :=
  fun g => if g = f then s else m g

theorem genUpdate_self (m : Faden → List (Ereignis D)) (f : Faden) (s : List (Ereignis D)) :
    genUpdate m f s f = s := by
  simp [genUpdate]

theorem genUpdate_noteq (m : Faden → List (Ereignis D)) (f g : Faden) (h : g ≠ f)
    (s : List (Ereignis D)) :
    genUpdate m f s g = m g := by
  simp [genUpdate, h]

/-- **One step of the generated machine.** `blatt`: thread `f` runs one leaf
    statement through `execStmt` (shared memory moves on writes); `nimmt`:
    `f` takes `L` while nobody else holds it (the lock as scheduler rule);
    `gibt`: `f` releases `L`. Every step appends its post-world to the history. -/
inductive GenSchritt (P : Programm D) (O : Orakel D) (passes : Nat) :
    GenMaschine D → Faden → GenMaschine D → Prop where
  | blatt (M : GenMaschine D) (f : Faden)
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hΛ : HeldGenau Λ (offen (M.spuren f)))
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
      (hneu : σ'.spur = neu ++ M.spuren f)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      GenSchritt P O passes M f
        ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
         M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
  | nimmt (M : GenMaschine D) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.spuren f))
      (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
      (hfrei : GenFrei M f L) :
      GenSchritt P O passes M f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)],
         M.tiefe + 1⟩
  | gibt (M : GenMaschine D) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.spuren f)) :
      GenSchritt P O passes M f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.gibt L],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)],
         M.tiefe + 1⟩

/-! ## 8. Computing with `Lauf.spur` on generated runs

   List-only facts about run projection: appending one step's events grows the
   acting thread's projection by exactly those events and leaves every other
   thread's projection (at any covered position) unchanged. -/

theorem gen_spur_append_le (l xs : Lauf D) (f : Faden) (j : Nat) (hj : j ≤ l.length) :
    (l ++ xs).spur f j = l.spur f j := by
  unfold Lauf.spur
  rw [List.take_append_of_le_length hj]

theorem gen_spur_length (l : Lauf D) (f : Faden) :
    l.spur f l.length =
      (l.filterMap fun s => if s.faden = f then some s.ereignis else none).reverse := by
  unfold Lauf.spur
  rw [List.take_length]

theorem genFilterMap_eigen (f : Faden) (neu : List (Ereignis D)) :
    (genEigen f neu).filterMap (fun s => if s.faden = f then some s.ereignis else none) =
      neu.reverse := by
  unfold genEigen
  induction neu.reverse with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem genFilterMap_eigen_fremd (f g : Faden) (hg : g ≠ f) (neu : List (Ereignis D)) :
    (genEigen f neu).filterMap (fun s => if s.faden = g then some s.ereignis else none) = [] := by
  unfold genEigen
  induction neu.reverse with
  | nil => rfl
  | cons _ _ ih => simp [ih, Ne.symm hg]

theorem genFilterMap_eigen_take_fremd (f g : Faden) (hg : g ≠ f) (neu : List (Ereignis D))
    (i : Nat) :
    ((genEigen f neu).take i).filterMap (fun s => if s.faden = g then some s.ereignis else none) =
      [] := by
  unfold genEigen
  rw [← List.map_take]
  generalize neu.reverse.take i = xs
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih, Ne.symm hg]

/-- After appending: the acting thread's projection grows by `neu`. -/
theorem gen_spur_append_eigen (l : Lauf D) (f : Faden) (neu : List (Ereignis D)) :
    (l ++ genEigen f neu).spur f (l ++ genEigen f neu).length = neu ++ l.spur f l.length := by
  rw [gen_spur_length, gen_spur_length, List.filterMap_append, List.reverse_append,
    genFilterMap_eigen, List.reverse_reverse]

/-- After appending: any other thread's projection is unchanged. -/
theorem gen_spur_append_fremd (l : Lauf D) (f g : Faden) (hg : g ≠ f) (neu : List (Ereignis D))
    (i : Nat) :
    (l ++ genEigen f neu).spur g (l.length + i) = l.spur g l.length := by
  unfold Lauf.spur
  rw [List.take_append, List.take_length, List.filterMap_append,
    show l.length + i - l.length = i by omega, genFilterMap_eigen_take_fremd f g hg,
    List.append_nil, List.take_of_length_le (Nat.le_add_right _ _)]

/-- After appending: any other thread's projection at any covered position. -/
theorem gen_spur_append_fremd_ge (l : Lauf D) (f g : Faden) (hg : g ≠ f)
    (neu : List (Ereignis D)) (j' : Nat) (hj : l.length ≤ j') :
    (l ++ genEigen f neu).spur g j' = l.spur g l.length := by
  unfold Lauf.spur
  rw [List.take_append, List.take_of_length_le hj, List.filterMap_append,
    genFilterMap_eigen_take_fremd f g hg, List.append_nil, List.take_length]

/-- A prefix of the run shows a suffix of the projection. -/
theorem gen_spur_suffix (l : Lauf D) (f : Faden) (j j' : Nat) (hj : j ≤ j') :
    ∃ pre, l.spur f j' = pre ++ l.spur f j := by
  unfold Lauf.spur
  have e : l.take j' = l.take j ++ (l.drop j).take (j' - j) := by
    rw [← List.take_add, Nat.add_sub_cancel' hj]
  rw [e, List.filterMap_append, List.reverse_append]
  exact ⟨_, rfl⟩

theorem gen_spur_ueber (l : Lauf D) (f : Faden) (j : Nat) (hj : l.length ≤ j) :
    l.spur f j = l.spur f l.length := by
  unfold Lauf.spur
  rw [List.take_of_length_le hj, List.take_length]

theorem gen_konsistent_suffix (pre s : List (Ereignis D)) (h : Konsistent (pre ++ s)) :
    Konsistent s := by
  induction pre with
  | nil => exact h
  | cons _ pre ih => exact ih (konsistent_tail h)

theorem gen_eigen_getElem (f : Faden) (neu : List (Ereignis D)) (i : Nat) (g : Faden)
    (e : Ereignis D)
    (h : (genEigen f neu)[i]? = some (Schritt.mk g e)) : g = f ∧ e ∈ neu := by
  unfold genEigen at h
  rw [List.getElem?_map] at h
  cases hx : neu.reverse[i]? with
  | none => rw [hx] at h; simp at h
  | some e' =>
      rw [hx] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, List.mem_reverse.mp (List.mem_of_getElem? hx)⟩

theorem gen_getLast_append_singleton (l : List α) (x : α) : (l ++ [x]).getLast? = some x :=
  List.getLast?_concat

/-! ## 9. Writes move memory: `schreibt_wirkt`, and the probe shape as NEGATIVE

   The auditor's probe names the OLD event-to-world fold (§3): every world it
   produces carries the start world's memory (`maschinenWelten_speicher_gleich`
   below -- `merke` extends the trace and nothing else). That shape is kept
   here as the NEGATIVE example: it is what generated worlds escape. A write
   through `execStmt` stores the written value into the world
   (`schreibt_wirkt_slot/glob`), so a write whose value differs moves the
   memory (`schreibt_wirkt_slot_ne/glob_ne`), and a fireable write yields a
   one-step generated run whose memory differs (`gen_write_glob_moves`). -/

/-- The OLD fold preserves memory: every world it produces carries the start
    world's slots and globals. NEGATIVE example (auditor-measured): `merke`
    extends the trace and nothing else, so worlds folded from events alone can
    never be won from writing. Generated worlds (§§7, 10-11) escape exactly
    this shape. -/
theorem weltenFalte_speicher_gleich (σ : World D) (run : Lauf D) :
    ∀ W ∈ weltenFalte σ run, W.slots = σ.slots ∧ W.globs = σ.globs := by
  induction run generalizing σ with
  | nil =>
      intro W hW
      simp only [weltenFalte, List.mem_singleton] at hW
      subst hW
      exact ⟨rfl, rfl⟩
  | cons s rest ih =>
      intro W hW
      simp only [weltenFalte, List.mem_cons] at hW
      rcases hW with rfl | hW
      · exact ⟨rfl, rfl⟩
      · exact ih (σ.merke [s.ereignis]) W hW

theorem maschinenWelten_speicher_gleich (M : MaschinenLauf D) :
    ∀ W ∈ maschinenWelten M, W.slots = M.start.slots ∧ W.globs = M.start.globs :=
  weltenFalte_speicher_gleich M.start M.run

/-- A store hits: the slot carries the stored value afterwards. -/
theorem storeSlot_hit (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) :
    (σ.storeSlot t k f v).slots t k f = v := by
  simp [World.storeSlot]

/-- A store hits: the global carries the stored value afterwards. -/
theorem storeGlob_hit (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    (σ.storeGlob g v).globs g = v := by
  simp [World.storeGlob]

/-- A write carries its value into the world, with its event. -/
theorem schreibt_wirkt_slot (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ) :
    let σ₁ := σ.lese Λ (i.orte ++ e.orte)
    let k := (eval σ₁ i σ₁ ρ).n
    let v := eval σ₁ e σ₁ ρ
    ((execStmt O passes keinRuf ((.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
      some (σ₁.schreibSlot t Λ k f v)) ∧ (σ₁.schreibSlot t Λ k f v).slots t k f = v := by
  refine ⟨rfl, ?_⟩
  show ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t _ f _).slots _ _ _ = _
  rw [storeSlot_hit]

/-- A write whose value differs moves the memory. -/
theorem schreibt_wirkt_slot_ne (σ₁ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (Λ : List (Res D)) (v : Wert D (D.typ t f)) (hv : v ≠ σ₁.slots t k f) :
    (σ₁.schreibSlot t Λ k f v).speicher ≠ σ₁.speicher := by
  intro hcon
  apply hv
  have h2 : ((σ₁.schreibSlot t Λ k f v).speicher).slots t k f =
      (σ₁.speicher).slots t k f :=
    congrArg (fun s : Speicher D => s.slots t k f) hcon
  have h3 : (σ₁.storeSlot t k f v).slots t k f = σ₁.slots t k f := h2
  rw [storeSlot_hit] at h3
  exact h3

/-- A write carries its value into the world, with its event. -/
theorem schreibt_wirkt_glob (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (σ : World D) (ρ : Env D Γ) :
    let σ₁ := σ.lese Λ e.orte
    let v := eval σ₁ e σ₁ ρ
    ((execStmt O passes keinRuf ((.assignGlob g e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
      some (σ₁.schreibGlob g Λ v)) ∧ (σ₁.schreibGlob g Λ v).globs g = v := by
  refine ⟨rfl, ?_⟩
  show ((σ.lese Λ e.orte).storeGlob g _).globs g = _
  rw [storeGlob_hit]

/-- A write whose value differs moves the memory. -/
theorem schreibt_wirkt_glob_ne (σ₁ : World D) (g : D.Glob)
    (Λ : List (Res D)) (v : Wert D (D.gtyp g)) (hv : v ≠ σ₁.globs g) :
    (σ₁.schreibGlob g Λ v).speicher ≠ σ₁.speicher := by
  intro hcon
  apply hv
  have h2 : ((σ₁.schreibGlob g Λ v).speicher).globs g =
      (σ₁.speicher).globs g :=
    congrArg (fun s : Speicher D => s.globs g) hcon
  have h3 : (σ₁.storeGlob g v).globs g = σ₁.globs g := h2
  rw [storeGlob_hit] at h3
  exact h3

/-- **A fireable write yields a one-step generated run whose memory differs.**
    The write's value comes from the thread's own world (any differing value
    fires: for a boolean global the literals `.wahr`/`.falsch` always supply
    one); the step is the `blatt` rule with the computed event list. -/
theorem gen_write_glob_moves (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (ρ : Env D Γ)
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (hv : eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ ≠
      ((M.weltVon f).lese Λ e.orte).globs g) :
    ∃ M', GenSchritt P O passes M f M' ∧ M'.speicher.globs g ≠ M.speicher.globs g := by
  have hleaf : ((Stmt.assignGlob (D := D) (V := V) g e hw hL : Stmt D V l Γ Λ Λ)).istBlatt = true := rfl
  have hneu : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
        (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)).spur =
      [Ereignis.gzugriff g true Λ ((M.weltVon f).lese Λ e.orte).haelt] ++
        (e.orte.map fun o => match o with
          | .inl t => Ereignis.zugriff t false Λ (M.weltVon f).haelt
          | .inr g' => Ereignis.gzugriff g' false Λ (M.weltVon f).haelt) ++ M.spuren f := rfl
  refine ⟨_, GenSchritt.blatt M f V l Γ Λ _ ((.assignGlob g e hw hL : Stmt D V l Γ Λ Λ)) ρ hleaf hΛ _ _ rfl hneu ?_, ?_⟩
  · intro L h hm
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hm
    rcases hm with hm | ⟨o, _, hm⟩
    · simp at hm
    · cases o <;> simp at hm
  · show ((((M.weltVon f).lese Λ e.orte).storeGlob g _).globs g) ≠ _
    rw [storeGlob_hit]
    exact hv

/-! ## 10. Reachable runs are generated, not handed

   From a start machine (shared memory, empty traces, empty run) every step of
   §7 extends reachability inductively (`GenErreichbar`). The invariant
   (`GenInv`) carries what the old structure assumed per thread -- consistency
   and goodness of every trace -- plus the projection link, the world history,
   the scheduler rule, and the step count; every step preserves it. -/

/-- The start machine: shared memory, empty traces, an empty run, and the
    start world with an empty trace. -/
def GenStart (sp : Speicher D) : GenMaschine D :=
  ⟨sp, fun _ => [], [], sp.welt [], [sp.welt []], 0⟩

/-- Reachable machines, generated from `M0` by the step relation. -/
inductive GenErreichbar (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : GenMaschine D) : GenMaschine D → Prop where
  | start : GenErreichbar P O passes M0 M0
  | schritt (M M' : GenMaschine D) (f : Faden)
      (h : GenErreichbar P O passes M0 M) (hs : GenSchritt P O passes M f M') :
      GenErreichbar P O passes M0 M'

/-- One leaf through `execStmt` keeps frame and trace (`stmt_gut`). -/
theorem blatt_brav (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f))) (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ') :
    Brav (M.weltVon f) σ' :=
  ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ) σ' hstep).2

/-- Old positions of an extended run keep the scheduler rule. -/
theorem genAuss_append_old (l xs : Lauf D) (hA : ForeignExclusion l)
    (j' : Nat) (g : Faden) (L : D.Lock) (h : List D.Lock)
    (hj' : (l ++ xs)[j']? = some (Schritt.mk g (Ereignis.nimmt L h)))
    (hj : j' < l.length) :
    ∀ g', g' ≠ g → ¬ (l ++ xs).haelt g' L j' := by
  rw [List.getElem?_append_left hj] at hj'
  have hold := hA j' g L h hj'
  intro g' hgne
  show ¬ L ∈ offen ((l ++ xs).spur g' j')
  rw [gen_spur_append_le _ _ _ _ (Nat.le_of_lt hj)]
  exact hold g' hgne

/-- A leaf step's new positions: its events are never `nimmt`. -/
theorem genAuss_blatt (l : Lauf D) (f : Faden) (neu : List (Ereignis D))
    (hA : ForeignExclusion l)
    (hkein : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
    ForeignExclusion (l ++ genEigen f neu) := by
  intro j' g L h hj'
  by_cases hj : j' < l.length
  · exact genAuss_append_old l (genEigen f neu) hA j' g L h hj' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hj'
    obtain ⟨-, hmem⟩ := gen_eigen_getElem f neu _ _ _ hj'
    exact absurd hmem (hkein L h)

/-- A `nimmt` step's new position: nobody else held the lock. -/
theorem genAuss_nimmt (l : Lauf D) (sp : Faden → List (Ereignis D)) (f : Faden)
    (L : D.Lock)
    (hA : ForeignExclusion l)
    (hfrei : ∀ g, g ≠ f → L ∉ offen (sp g))
    (hproj : ∀ g, l.spur g l.length = sp g) :
    ForeignExclusion (l ++ genEigen f [Ereignis.nimmt L (offen (sp f))]) := by
  intro j' g L' h' hj'
  by_cases hj : j' < l.length
  · exact genAuss_append_old l _ hA j' g L' h' hj' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hj'
    obtain ⟨hgf, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hj'
    subst g
    simp only [List.mem_singleton] at hmem
    cases hmem
    intro g' hgne
    show ¬ L ∈ offen ((l ++ genEigen f [Ereignis.nimmt L (offen (sp f))]).spur g' j')
    rw [gen_spur_append_fremd_ge _ _ _ hgne _ _ (Nat.le_of_not_lt hj), hproj g']
    exact hfrei g' hgne

/-- A `gibt` step's new position: releasing is never taking. -/
theorem genAuss_gibt (l : Lauf D) (f : Faden) (L : D.Lock)
    (hA : ForeignExclusion l) :
    ForeignExclusion (l ++ genEigen f [Ereignis.gibt L]) := by
  intro j' g L' h' hj'
  by_cases hj : j' < l.length
  · exact genAuss_append_old l _ hA j' g L' h' hj' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hj'
    obtain ⟨-, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hj'
    simp only [List.mem_singleton] at hmem
    cases hmem

/-- The projection after a step: the actor grows by `neu`, everyone else rests. -/
theorem genProj_blatt (l : Lauf D) (sp : Faden → List (Ereignis D)) (f : Faden)
    (neu : List (Ereignis D)) (sneu : List (Ereignis D))
    (hproj : ∀ f', l.spur f' l.length = sp f')
    (hneu : sneu = neu ++ sp f) :
    ∀ f', (l ++ genEigen f neu).spur f' (l ++ genEigen f neu).length =
      genUpdate sp f sneu f' := by
  intro f'
  by_cases hf : f' = f
  · subst f'
    rw [gen_spur_append_eigen, hproj f, ← hneu, genUpdate_self]
  · rw [List.length_append, gen_spur_append_fremd _ _ _ hf, hproj f',
      genUpdate_noteq _ _ _ hf]

/-- What every generated machine maintains. -/
structure GenInv (M : GenMaschine D) : Prop where
  konsistent : ∀ f, Konsistent (M.spuren f)
  spur_gut : ∀ f (e : Ereignis D), e ∈ M.spuren f → e.gut
  welt_gut : ∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut
  proj : ∀ f, M.lauf.spur f M.lauf.length = M.spuren f
  letzte : ∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f))
  auss : ForeignExclusion M.lauf
  tiefe_len : M.welten.length = M.tiefe + 1

theorem genStart_inv (sp : Speicher D) : GenInv (GenStart sp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    show Konsistent ([] : List (Ereignis D))
    exact konsistent_nil
  · intro f e he
    simp [GenStart] at he
  · intro W hW e he
    simp only [GenStart, List.mem_singleton] at hW
    subst hW
    change e ∈ ([] : List (Ereignis D)) at he
    simp at he
  · intro f
    show Lauf.spur ([] : Lauf D) f 0 = []
    exact Lauf.spur_zero _ _
  · refine ⟨0, ?_⟩
    show ([sp.welt []]).getLast? = some (sp.welt [])
    exact List.getLast?_singleton
  · intro j g L h hj
    simp [GenStart] at hj
  · show (([sp.welt []] : List (World D))).length = (0 : Nat) + 1
    rfl

/-- A leaf step preserves the invariant. -/
theorem genInv_blatt (_P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (_hleaf : s.istBlatt = true)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (hM : GenInv M) :
    GenInv ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
      M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩ := by
  have hb : Brav (M.weltVon f) σ' := blatt_brav O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f'
    by_cases hf : f' = f
    · subst f'
      show Konsistent (genUpdate M.spuren f σ'.spur f)
      rw [genUpdate_self]
      exact hb.2.2 (hM.konsistent f)
    · show Konsistent (genUpdate M.spuren f σ'.spur f')
      rw [genUpdate_noteq _ _ _ hf]
      exact hM.konsistent f'
  · intro f' e he
    by_cases hf : f' = f
    · subst f'
      change e ∈ genUpdate M.spuren f σ'.spur f at he
      rw [genUpdate_self, hneu, List.mem_append] at he
      rcases he with he | he
      · have he' : e ∈ σ'.spur := by rw [hneu]; exact List.mem_append_left _ he
        rcases hb.2.1 e he' with hm | hg
        · exact hM.spur_gut f e hm
        · exact hg
      · exact hM.spur_gut f e he
    · change e ∈ genUpdate M.spuren f σ'.spur f' at he
      rw [genUpdate_noteq _ _ _ hf] at he
      exact hM.spur_gut f' e he
  · intro W hW e he
    have hW' : W ∈ M.welten ∨ W = σ' := by
      change W ∈ M.welten ++ [σ'] at hW
      rwa [List.mem_append, List.mem_singleton] at hW
    rcases hW' with hW' | hW'
    · exact hM.welt_gut W hW' e he
    · subst W
      rw [hneu, List.mem_append] at he
      rcases he with he | he
      · have he' : e ∈ σ'.spur := by rw [hneu]; exact List.mem_append_left _ he
        rcases hb.2.1 e he' with hm | hg
        · exact hM.spur_gut f e hm
        · exact hg
      · exact hM.spur_gut f e he
  · show ∀ f', (M.lauf ++ genEigen f neu).spur f' (M.lauf ++ genEigen f neu).length =
      genUpdate M.spuren f σ'.spur f'
    exact genProj_blatt M.lauf M.spuren f neu σ'.spur hM.proj hneu
  · refine ⟨f, ?_⟩
    show (M.welten ++ [σ']).getLast? =
      some ((σ'.speicher).welt (genUpdate M.spuren f σ'.spur f))
    rw [gen_getLast_append_singleton, genUpdate_self, Speicher.welt_speicher]
  · show ForeignExclusion (M.lauf ++ genEigen f neu)
    exact genAuss_blatt M.lauf f neu hM.auss hkein_nimmt
  · show (M.welten ++ [σ']).length = (M.tiefe + 1) + 1
    simp [List.length_append, hM.tiefe_len]

/-- A `nimmt` step preserves the invariant. -/
theorem genInv_nimmt (_P : Programm D) (_O : Orakel D) (_passes : Nat)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hself : L ∉ offen (M.spuren f))
    (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
    (hfrei : GenFrei M f L)
    (hM : GenInv M) :
    GenInv ⟨M.speicher,
      genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f),
      M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))],
      M.start,
      M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)],
      M.tiefe + 1⟩ := by
  have hgut : (Ereignis.nimmt L (offen (M.spuren f))).gut :=
    ⟨hrang, hself⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f'
    by_cases hf : f' = f
    · subst f'
      show Konsistent (genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f)
      rw [genUpdate_self]
      exact konsistent_cons rfl (hM.konsistent f)
    · show Konsistent (genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f')
      rw [genUpdate_noteq _ _ _ hf]
      exact hM.konsistent f'
  · intro f' e he
    by_cases hf : f' = f
    · subst f'
      change e ∈ genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f at he
      rw [genUpdate_self, List.mem_cons] at he
      rcases he with rfl | he
      · exact hgut
      · exact hM.spur_gut f e he
    · change e ∈ genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f' at he
      rw [genUpdate_noteq _ _ _ hf] at he
      exact hM.spur_gut f' e he
  · intro W hW e he
    have hW' : W ∈ M.welten ∨ W = M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) := by
      change W ∈ M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)] at hW
      rwa [List.mem_append, List.mem_singleton] at hW
    rcases hW' with hW' | hW'
    · exact hM.welt_gut W hW' e he
    · subst hW'
      have he' : e ∈ Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f := he
      rw [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact hgut
      · exact hM.spur_gut f e he'
  · show ∀ f', (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))]).spur f' (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))]).length =
      genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f'
    exact genProj_blatt M.lauf M.spuren f [Ereignis.nimmt L (offen (M.spuren f))] (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) hM.proj rfl
  · refine ⟨f, ?_⟩
    show (M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)]).getLast? =
      some (M.speicher.welt (genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f))
    rw [gen_getLast_append_singleton, genUpdate_self]
  · show ForeignExclusion (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))])
    exact genAuss_nimmt M.lauf M.spuren f L hM.auss hfrei hM.proj
  · show (M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)]).length = (M.tiefe + 1) + 1
    simp [List.length_append, hM.tiefe_len]

/-- A `gibt` step preserves the invariant. -/
theorem genInv_gibt (_P : Programm D) (_O : Orakel D) (_passes : Nat)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (_hhaelt : L ∈ offen (M.spuren f))
    (hM : GenInv M) :
    GenInv ⟨M.speicher,
      genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f),
      M.lauf ++ genEigen f [Ereignis.gibt L],
      M.start,
      M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)],
      M.tiefe + 1⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f'
    by_cases hf : f' = f
    · subst f'
      show Konsistent (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f)
      rw [genUpdate_self]
      exact konsistent_cons trivial (hM.konsistent f)
    · show Konsistent (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f')
      rw [genUpdate_noteq _ _ _ hf]
      exact hM.konsistent f'
  · intro f' e he
    by_cases hf : f' = f
    · subst f'
      change e ∈ genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f at he
      rw [genUpdate_self, List.mem_cons] at he
      rcases he with rfl | he
      · trivial
      · exact hM.spur_gut f e he
    · change e ∈ genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f' at he
      rw [genUpdate_noteq _ _ _ hf] at he
      exact hM.spur_gut f' e he
  · intro W hW e he
    have hW' : W ∈ M.welten ∨ W = M.speicher.welt (Ereignis.gibt L :: M.spuren f) := by
      change W ∈ M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)] at hW
      rwa [List.mem_append, List.mem_singleton] at hW
    rcases hW' with hW' | hW'
    · exact hM.welt_gut W hW' e he
    · subst hW'
      have he' : e ∈ Ereignis.gibt L :: M.spuren f := he
      rw [List.mem_cons] at he'
      rcases he' with rfl | he'
      · trivial
      · exact hM.spur_gut f e he'
  · show ∀ f', (M.lauf ++ genEigen f [Ereignis.gibt L]).spur f' (M.lauf ++ genEigen f [Ereignis.gibt L]).length =
      genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f'
    exact genProj_blatt M.lauf M.spuren f [Ereignis.gibt L] (Ereignis.gibt L :: M.spuren f) hM.proj rfl
  · refine ⟨f, ?_⟩
    show (M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)]).getLast? =
      some (M.speicher.welt (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f))
    rw [gen_getLast_append_singleton, genUpdate_self]
  · show ForeignExclusion (M.lauf ++ genEigen f [Ereignis.gibt L])
    exact genAuss_gibt M.lauf f L hM.auss
  · show (M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)]).length = (M.tiefe + 1) + 1
    simp [List.length_append, hM.tiefe_len]

/-- Every step preserves the invariant. -/
theorem genSchritt_inv (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M M' : GenMaschine D) (f : Faden)
    (hM : GenInv M) (hs : GenSchritt P O passes M f M') : GenInv M' := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn⟩ |
    ⟨L, hself, hrang, hfrei⟩ | ⟨L, hhaelt⟩
  · exact genInv_blatt P O passes hO M f V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn hM
  · exact genInv_nimmt P O passes M f L hself hrang hfrei hM
  · exact genInv_gibt P O passes M f L hhaelt hM

/-- Every generated machine maintains the invariant. -/
theorem genErreichbar_inv (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M0 M : GenMaschine D)
    (h0 : GenInv M0) (h : GenErreichbar P O passes M0 M) : GenInv M := by
  induction h with
  | start => exact h0
  | schritt M M' f _ hs ih => exact genSchritt_inv P O passes hO M M' f ih hs

/-! ## 11. What generated runs yield: W1/W2, the scheduler rule, worlds, order

   Every run generated from a start machine is consistent (W1) with good
   observations (W2) and obeys the scheduler rule (W3, `gen_ausschluss`): the
   lock is taken only while nobody else holds it, by construction of the
   `nimmt` step. W4 comes from the explicit `Einfaedig` projection
   (`gen_w1w2w4`, same triple shape as `w1w2w4_aus_maschine`); with the
   declaration side it closes to `Gesittet` (`gen_gesittet`) and to the serial
   order (`gen_reduktion`), through the read-only bridge and reduction. The
   world history carries live memory (`genWelten_*`, same shapes as the
   `maschinenWelten_*` family); a fireable write moves it
   (`gen_welt_speicher_bewegt`). -/

/-- W1 for generated runs: every projection of the run is consistent. -/
theorem gen_konsistent (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) (f : Faden) (j : Nat) :
    Konsistent (M.lauf.spur f j) := by
  have hM := genErreichbar_inv P O passes hO _ M (genStart_inv sp) h
  have hk : Konsistent (M.lauf.spur f M.lauf.length) := by
    rw [hM.proj]
    exact hM.konsistent f
  by_cases hj : M.lauf.length ≤ j
  · rw [gen_spur_ueber _ _ _ hj]
    exact hk
  · have hj' : j ≤ M.lauf.length := by omega
    obtain ⟨pre, hpre⟩ := gen_spur_suffix M.lauf f j M.lauf.length hj'
    rw [hpre] at hk
    exact gen_konsistent_suffix pre _ hk

/-- W2 for generated runs: every observed event is good. -/
theorem gen_gut_obs (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) (f : Faden) (j : Nat)
    (e : Ereignis D) (he : e ∈ M.lauf.spur f j) : e.gut := by
  have hM := genErreichbar_inv P O passes hO _ M (genStart_inv sp) h
  have hg : ∀ e ∈ M.lauf.spur f M.lauf.length, e.gut := by
    rw [hM.proj]
    exact hM.spur_gut f
  by_cases hj : M.lauf.length ≤ j
  · rw [gen_spur_ueber _ _ _ hj] at he
    exact hg e he
  · have hj' : j ≤ M.lauf.length := by omega
    obtain ⟨pre, hpre⟩ := gen_spur_suffix M.lauf f j M.lauf.length hj'
    exact hg e (by rw [hpre]; exact List.mem_append_right _ he)

/-- W3 for generated runs: the scheduler rule holds over the whole run. -/
theorem gen_ausschluss (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    ForeignExclusion M.lauf :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).auss

/-- **W1, W2, W4 for generated runs.** W1+W2 are generated (grammar side,
    through `execStmt`); W4 comes from the explicit `Einfaedig` projection --
    thread programs are over-approximated (any leaf any time, no counters),
    so ownership is still a construction premise, exactly as the bridge books
    it. Same triple shape as `w1w2w4_aus_maschine`. -/
theorem gen_w1w2w4 (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf)) :
    (∀ f j, Konsistent (M.lauf.spur f j)) ∧
    (∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut) ∧
    (∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g) :=
  ⟨gen_konsistent P O passes hO sp M h, gen_gut_obs P O passes hO sp M h,
   marke_eindeutig_aus_einfaedig code M.lauf hEin⟩

/-- **A generated run is `Gesittet`.** W1-W3 are generated; W4 travels as the
    `Einfaedig` projection, W5 as the declaration side -- both explicit
    premises, exactly as the bridge books the construction and the declaration
    side. -/
theorem gen_gesittet (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet M.lauf :=
  gesittet_aus_einfaedig M.lauf (gen_konsistent P O passes hO sp M h)
    (gen_gut_obs P O passes hO sp M h) (gen_ausschluss P O passes hO sp M h)
    code hEin hungeteilt

/-- **Reduction, serial order, from a generated run (two-access single-carrier
    fragment).** Same interface as `reduktion_maschine`: two conflicting
    accesses in a generated run are happens-before ordered, in one direction
    or the other. Closes via `reduktion_seriell` with machine-derived
    `Gesittet`; the narrowing (single shared table carrier, two accesses at
    order level) is carried unchanged. -/
theorem gen_reduktion (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g)
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁ :=
  reduktion_seriell M.lauf
    (gen_gesittet P O passes hO sp M h code hEin hungeteilt)
    t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

/-- One world per step, plus the start world: the history counts steps. -/
theorem genWelten_laenge (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    M.welten.length = M.tiefe + 1 :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).tiefe_len

/-- The observations of every generated run are good. -/
theorem genWelten_gut (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    ∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).welt_gut

/-- The last recorded world is a thread world with live memory. -/
theorem genWelten_letzte (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    ∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f)) :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).letzte

/-- **Generated worlds move memory.** A fireable write reaches, in one step, a
    machine whose memory differs -- the auditor's constant-memory shape
    (`maschinenWelten_speicher_gleich`) does not characterize generated runs. -/
theorem gen_welt_speicher_bewegt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (ρ : Env D Γ)
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (hΛ : HeldGenau Λ (offen ((GenStart sp).spuren f)))
    (hv : eval (((GenStart sp).weltVon f).lese Λ e.orte) e
      (((GenStart sp).weltVon f).lese Λ e.orte) ρ ≠
      (((GenStart sp).weltVon f).lese Λ e.orte).globs g) :
    ∃ M', GenErreichbar P O passes (GenStart sp) M' ∧
      M'.speicher.globs g ≠ sp.globs g := by
  obtain ⟨M', hs, hdiff⟩ :=
    gen_write_glob_moves P O passes (GenStart sp) f V l Γ Λ g e ρ hw hL hΛ hv
  exact ⟨M', GenErreichbar.schritt _ _ f GenErreichbar.start hs, hdiff⟩

#print axioms Gabbro.Grammatik.keinRuf_gut
#print axioms Gabbro.Grammatik.Speicher.welt_speicher
#print axioms Gabbro.Grammatik.weltenFalte_speicher_gleich
#print axioms Gabbro.Grammatik.maschinenWelten_speicher_gleich
#print axioms Gabbro.Grammatik.storeSlot_hit
#print axioms Gabbro.Grammatik.storeGlob_hit
#print axioms Gabbro.Grammatik.schreibt_wirkt_slot
#print axioms Gabbro.Grammatik.schreibt_wirkt_slot_ne
#print axioms Gabbro.Grammatik.schreibt_wirkt_glob
#print axioms Gabbro.Grammatik.schreibt_wirkt_glob_ne
#print axioms Gabbro.Grammatik.gen_write_glob_moves
#print axioms Gabbro.Grammatik.gen_konsistent
#print axioms Gabbro.Grammatik.gen_gut_obs
#print axioms Gabbro.Grammatik.gen_ausschluss
#print axioms Gabbro.Grammatik.gen_w1w2w4
#print axioms Gabbro.Grammatik.gen_gesittet
#print axioms Gabbro.Grammatik.gen_reduktion
#print axioms Gabbro.Grammatik.genWelten_laenge
#print axioms Gabbro.Grammatik.genWelten_gut
#print axioms Gabbro.Grammatik.genWelten_letzte
#print axioms Gabbro.Grammatik.gen_welt_speicher_bewegt

/-! ## 12. Program counters -- every thread carries its position

   Section 11 books the remainder honestly: thread programs are over-approximated
   (any leaf any time), so W4 needs the `Einfaedig` projection as premise and W5
   the declaration side. This section removes the over-approximation at the
   position level.

   A thread program (`PCProg`) is the schedule of one thread: one atom per step.
   A `leaf` atom carries the static footprint of the leaf `Stmt` it points at --
   its `Λ` (every `zugriff`/`gzugriff` event of a leaf step names exactly that
   `Λ`: `World.lese`, `World.schreibSlot`, `World.schreibGlob`) and the carrier
   set the step may touch -- reusing the `Stmt`/`Block` body shapes at leaf
   grain. A `take`/`rel` atom is one side of a `locks L` section. Sections are
   take-to-release intervals, the grain of `InterferenzAllgemein.lean` §21
   (`AbschnittGedeckt`): at event grain the invariant breaks mid-step, at section
   grain each step re-establishes what it owes.

   Every thread carries its position (`PCStand`, one counter per thread). A
   `PCSchritt` fires only the pointed-to atom -- the leaf step runs the
   pointed-to footprint (`hΛa` ties the atom to the fired statement), the lock
   steps the pointed-to lock -- and advances only the acting thread
   (`pcAdvance`); every other thread resumes at its stored counter. That advance
   IS the continuation: resumption is explicit, and no step moves another
   thread's position (`pcSchritt_eigen`, `pcSchritt_fremd`).

   From positions follow the footprints: `PCMarkInv` (every mark named by a run
   event sits in its thread's program text) and `PCCarrierInv` (every accessed
   carrier is reachable from its thread's program text), both preserved by every
   step. With program-text separation -- disjoint mark codes (`PCMarkSep`), no
   unshared carrier reached from two threads (`PCUnsharedSep`) -- the projection
   premise discharges (`pc_discharge_einfaedig`, the discharge fragment) and the
   declaration side discharges (`pc_discharge_unshared`); `pc_gesittet` closes
   with neither premise, and `pc_reduktion` runs the serial order on it. The
   generated race-freedom results keep building untouched: `gen_konsistent`,
   `gen_gut_obs`, `gen_ausschluss` are consumed through the projection
   (`pcReach_gen`), never re-proved; the `pc_*` triple restates them on PC runs
   honestly in-file.

   Remainder (booked, not hidden): full `Block` continuations -- `ite` arms, call
   stacks, loop resumption as explicit continuation objects -- are not threaded
   here; the schedule flattens each body to its atom sequence. What W4/W5 need is
   positions with footprints, and that is what this section carries. The full
   run-to-`Bau` wiring (`Geteilt.lean`: unshared means reachable from at most one
   thread) still travels as the carrier-separation shape, not as a `Bau` term. -/

/-- One position in a thread program: the footprint of the statement fired here.
    `leaf` carries the static `Λ` of the pointed-to leaf `Stmt` plus the carrier
    set that step may touch; `take`/`rel` carry the lock of the pointed-to
    `locks L` side. Lock steps name no marks (`Ereignis.lambda` is `[]` there)
    and touch no carrier (`Ereignis.traeger` is `none` there). -/
inductive PCAtom (D : Deklaration) where
  | leaf (Λ : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
  | take (L : D.Lock)
  | rel (L : D.Lock)

/-- The marks named in one atom's static footprint. -/
def PCAtom.marks : PCAtom D → List D.Marke
  | .leaf Λ _ => Λ.filterMap fun r => match r with
    | .marke m _ => some m
    | _ => none
  | _ => []

/-- The carriers one atom may touch. -/
def PCAtom.carriers : PCAtom D → List (D.Tab ⊕ D.Glob)
  | .leaf _ cs => cs
  | _ => []

/-- A thread program: the schedule of one thread, one atom per step. -/
def PCProg (D : Deklaration) := Faden → List (PCAtom D)

/-- Thread positions: every thread carries its position in its program. -/
def PCStand := Faden → Nat

/-- Advance one thread, keep every other: the continuation, explicit. -/
def pcAdvance (pc : PCStand) (f : Faden) : PCStand :=
  fun g => if g = f then pc f + 1 else pc g

theorem pcAdvance_self (pc : PCStand) (f : Faden) :
    pcAdvance pc f f = pc f + 1 := by
  simp [pcAdvance]

theorem pcAdvance_noteq (pc : PCStand) (f g : Faden) (h : g ≠ f) :
    pcAdvance pc f g = pc g := by
  simp [pcAdvance, h]

/-- The marks named anywhere in one thread's program text. -/
def PCProg.marks (prog : PCProg D) (f : Faden) : List D.Marke :=
  (prog f).flatMap PCAtom.marks

/-- Mark separation, over codes: no code named by one thread's text is named by
    another's. Program text, not run projection: this replaces `hEin`. -/
def PCMarkSep (code : D.Marke → Nat) (prog : PCProg D) : Prop :=
  ∀ f g, f ≠ g → ∀ c, c ∈ (prog.marks f).map code → c ∉ (prog.marks g).map code

/-- The carriers reached anywhere in one thread's program text. -/
def PCProg.carriers (prog : PCProg D) (f : Faden) : List (D.Tab ⊕ D.Glob) :=
  (prog f).flatMap PCAtom.carriers

/-- Carrier separation for unshared carriers: a carrier reached from two threads
    is shared. Program text, not declaration side: this replaces `hungeteilt`. -/
def PCUnsharedSep (prog : PCProg D) : Prop :=
  ∀ f g, f ≠ g → ∀ o, o ∈ prog.carriers f → o ∈ prog.carriers g →
    ¬ (match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false)

/-- **One PC step.** The same machine step as `GenSchritt`, firing only the
    pointed-to atom: the leaf step runs the pointed-to footprint (`hΛa` ties the
    atom to the fired statement), the lock steps the pointed-to lock. The
    footprint checks (`hmark`, `hcar`) verify the atom against the step's own
    events; the counter advances only the acting thread (`pcAdvance`). -/
inductive PCSchritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) : GenMaschine D → PCStand → Faden → GenMaschine D → PCStand → Prop where
  | leaf (M : GenMaschine D) (pc : PCStand) (f : Faden)
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hΛ : HeldGenau Λ (offen (M.spuren f)))
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
      (hneu : σ'.spur = neu ++ M.spuren f)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog f)[pc f]? = some (PCAtom.leaf Λa cs))
      (hΛa : Λa = Λ)
      (hmark : ∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat),
        Res.marke m st ∈ e.lambda → m ∈ PCAtom.marks (PCAtom.leaf Λa cs))
      (hcar : ∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf Λa cs)) :
      PCSchritt P O passes prog M pc f
        ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
         M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
        (pcAdvance pc f)
  | take (M : GenMaschine D) (pc : PCStand) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.spuren f))
      (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
      (hfrei : GenFrei M f L)
      (hpc : (prog f)[pc f]? = some (PCAtom.take L)) :
      PCSchritt P O passes prog M pc f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)],
         M.tiefe + 1⟩
        (pcAdvance pc f)
  | rel (M : GenMaschine D) (pc : PCStand) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.spuren f))
      (hpc : (prog f)[pc f]? = some (PCAtom.rel L)) :
      PCSchritt P O passes prog M pc f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.gibt L],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)],
         M.tiefe + 1⟩
        (pcAdvance pc f)

/-- Reachable PC machines, from a start machine and zeroed counters. -/
inductive PCReach (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) : GenMaschine D → PCStand → Prop where
  | start : PCReach P O passes prog M0 M0 (fun _ => 0)
  | step (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
      (h : PCReach P O passes prog M0 M pc) (hs : PCSchritt P O passes prog M pc f M' pc') :
      PCReach P O passes prog M0 M' pc'

/-- Every PC step is a generated step: the counter constrains, the machine moves. -/
theorem pcSchritt_gen (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') :
    GenSchritt P O passes M f M' := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, _Λa, _cs, _hpc, _hΛa, _hmark, _hcar⟩ |
    ⟨L, hself, hrang, hfrei, _hpc⟩ | ⟨L, hhaelt, _hpc⟩
  · exact GenSchritt.blatt M f V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn
  · exact GenSchritt.nimmt M f L hself hrang hfrei
  · exact GenSchritt.gibt M f L hhaelt

/-- Every PC-reachable machine is generated: positions project to runs. -/
theorem pcReach_gen (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc) : GenErreichbar P O passes M0 M := by
  induction h with
  | start => exact GenErreichbar.start
  | step M M' pc pc' f _ hs ih =>
      exact GenErreichbar.schritt M M' f ih (pcSchritt_gen P O passes prog M M' pc pc' f hs)

/-- A step advances its own counter: the acting thread moves to its next atom. -/
theorem pcSchritt_eigen (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') : pc' f = pc f + 1 := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, _Λa, _cs, _hpc, _hΛa, _hmark, _hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · exact pcAdvance_self pc f
  · exact pcAdvance_self pc f
  · exact pcAdvance_self pc f

/-- A step moves no other counter: every other thread resumes where it stood. -/
theorem pcSchritt_fremd (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f g : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') (hne : g ≠ f) :
    pc' g = pc g := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, _Λa, _cs, _hpc, _hΛa, _hmark, _hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · exact pcAdvance_noteq pc f g hne
  · exact pcAdvance_noteq pc f g hne
  · exact pcAdvance_noteq pc f g hne

/-- W1 on PC runs: every projection of a PC run is consistent. -/
theorem pc_konsistent (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) (f : Faden) (j : Nat) :
    Konsistent (M.lauf.spur f j) :=
  gen_konsistent P O passes hO sp M (pcReach_gen P O passes prog _ M pc h) f j

/-- W2 on PC runs: every observed event of a PC run is good. -/
theorem pc_gut_obs (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) (f : Faden) (j : Nat)
    (e : Ereignis D) (he : e ∈ M.lauf.spur f j) : e.gut :=
  gen_gut_obs P O passes hO sp M (pcReach_gen P O passes prog _ M pc h) f j e he

/-- W3 on PC runs: the scheduler rule holds over the whole PC run. -/
theorem pc_ausschluss (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ForeignExclusion M.lauf :=
  gen_ausschluss P O passes hO sp M (pcReach_gen P O passes prog _ M pc h)

/-- Every mark a run event names sits in its thread's program text: which mark a
    thread holds follows from where its program stands. -/
def PCMarkInv (prog : PCProg D) (M : GenMaschine D) : Prop :=
  ∀ (k : Nat) (f : Faden) (e : Ereignis D),
    M.lauf[k]? = some (Schritt.mk f e) →
    ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda → m ∈ prog.marks f

/-- Every accessed carrier is reachable from its thread's program text:
    thread position determines carrier reachability. -/
def PCCarrierInv (prog : PCProg D) (M : GenMaschine D) : Prop :=
  ∀ (k : Nat) (f : Faden) (e : Ereignis D),
    M.lauf[k]? = some (Schritt.mk f e) →
    ∀ o, e.traeger = some o → o ∈ prog.carriers f

/-- One atom's marks sit in its thread's program text. -/
theorem pcAtom_mem_marks (prog : PCProg D) (f : Faden) (a : PCAtom D)
    (h : a ∈ prog f) (m : D.Marke) (hm : m ∈ a.marks) : m ∈ prog.marks f := by
  unfold PCProg.marks
  rw [List.mem_flatMap]
  exact ⟨a, h, hm⟩

/-- One atom's carriers sit in its thread's program text. -/
theorem pcAtom_mem_carriers (prog : PCProg D) (f : Faden) (a : PCAtom D)
    (h : a ∈ prog f) (o : D.Tab ⊕ D.Glob) (ho : o ∈ a.carriers) :
    o ∈ prog.carriers f := by
  unfold PCProg.carriers
  rw [List.mem_flatMap]
  exact ⟨a, h, ho⟩

/-- The start machine names no marks: its run is empty. -/
theorem pcStart_markInv (prog : PCProg D) (sp : Speicher D) :
    PCMarkInv prog (GenStart sp) := by
  intro k f e hk m st hm
  have hnil : (GenStart sp).lauf = [] := rfl
  rw [hnil] at hk
  simp at hk

/-- The start machine touches no carriers: its run is empty. -/
theorem pcStart_carrierInv (prog : PCProg D) (sp : Speicher D) :
    PCCarrierInv prog (GenStart sp) := by
  intro k f e hk o ho
  have hnil : (GenStart sp).lauf = [] := rfl
  rw [hnil] at hk
  simp at hk

/-- A PC step preserves the mark invariant: old positions keep it, new positions
    carry the pointed-to atom's footprint into its thread's program text. -/
theorem pcSchritt_markInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc')
    (hinv : PCMarkInv prog M) : PCMarkInv prog M' := by
  rcases hs with ⟨_V, _l, _Γ, _Λ, _Λ', _s, _ρ, _hleaf, _hΛ, _σ', neu, _hstep, _hneu, _hkn, Λa, cs, hpc, _hΛa, hmark, _hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · intro k f' e hk m st hm
    have hkred : (M.lauf ++ genEigen f neu)[k]? = some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred m st hm
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f neu _ _ _ hkred
      have hfoot := hmark e hmem m st hm
      have ha : PCAtom.leaf Λa cs ∈ prog f' := List.mem_of_getElem? hpc
      exact pcAtom_mem_marks prog f' _ ha m hfoot
  · intro k f' e hk m st hm
    have hkred : (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred m st hm
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hlam : (Ereignis.nimmt L (offen (M.spuren f'))).lambda = [] := rfl
      rw [hlam] at hm
      simp at hm
  · intro k f' e hk m st hm
    have hkred : (M.lauf ++ genEigen f [Ereignis.gibt L])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred m st hm
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hlam : (Ereignis.gibt L).lambda = [] := rfl
      rw [hlam] at hm
      simp at hm

/-- A PC step preserves the carrier invariant: old positions keep it, new
    positions carry the pointed-to atom's carrier set into its thread's text. -/
theorem pcSchritt_carrierInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc')
    (hinv : PCCarrierInv prog M) : PCCarrierInv prog M' := by
  rcases hs with ⟨_V, _l, _Γ, _Λ, _Λ', _s, _ρ, _hleaf, _hΛ, _σ', neu, _hstep, _hneu, _hkn, Λa, cs, hpc, _hΛa, _hmark, hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · intro k f' e hk o ho
    have hkred : (M.lauf ++ genEigen f neu)[k]? = some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred o ho
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f neu _ _ _ hkred
      have hfoot := hcar e hmem o ho
      have ha : PCAtom.leaf Λa cs ∈ prog f' := List.mem_of_getElem? hpc
      exact pcAtom_mem_carriers prog f' _ ha o hfoot
  · intro k f' e hk o ho
    have hkred : (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred o ho
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have htr : (Ereignis.nimmt L (offen (M.spuren f'))).traeger = none := rfl
      rw [htr] at ho
      cases ho
  · intro k f' e hk o ho
    have hkred : (M.lauf ++ genEigen f [Ereignis.gibt L])[k]? =
        some (Schritt.mk f' e) := hk
    by_cases hkk : k < M.lauf.length
    · rw [List.getElem?_append_left hkk] at hkred
      exact hinv k f' e hkred o ho
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hkk)] at hkred
      obtain ⟨rfl, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hkred
      simp only [List.mem_singleton] at hmem
      cases hmem
      have htr : (Ereignis.gibt L).traeger = none := rfl
      rw [htr] at ho
      cases ho

/-- Every PC-reachable machine maintains the mark invariant. -/
theorem pcReach_markInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) : PCMarkInv prog M := by
  induction h with
  | start => exact pcStart_markInv prog sp
  | step M M' pc pc' f _ hs ih =>
      exact pcSchritt_markInv P O passes prog M M' pc pc' f hs ih

/-- Every PC-reachable machine maintains the carrier invariant. -/
theorem pcReach_carrierInv (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) : PCCarrierInv prog M := by
  induction h with
  | start => exact pcStart_carrierInv prog sp
  | step M M' pc pc' f _ hs ih =>
      exact pcSchritt_carrierInv P O passes prog M M' pc pc' f hs ih

/-- A projected mark naming comes from a program-text mark. -/
theorem markenProj_marke (code : D.Marke → Nat) (m : D.Marke) (st : Nat)
    (c s : Nat)
    (h : markenProj code (Res.marke m st) = Marken.Res.marke c s) :
    code m = c := by
  have h2 : Marken.Res.marke (code m) st = Marken.Res.marke c s := h
  cases h2
  rfl

/-- A lock naming is never a mark naming. -/
theorem markenProj_held_absurd (code : D.Marke → Nat) (L : D.Lock) (c s : Nat)
    (h : markenProj code (Res.held L) = Marken.Res.marke c s) : False := by
  have h2 : Marken.Res.held = Marken.Res.marke c s := h
  cases h2

/-- **The discharge fragment: program counters discharge `hEin`.** If no mark
    code is named by two threads' program texts, the projected run is
    single-threaded: which mark a thread holds follows from where its program
    stands (`PCMarkInv`), and separation over codes turns two namings into one
    thread. This replaces the `Einfaedig` projection premise. -/
theorem pc_discharge_einfaedig (code : D.Marke → Nat) (prog : PCProg D)
    (M : GenMaschine D)
    (hinv : PCMarkInv prog M)
    (hSep : PCMarkSep code prog) :
    Marken.Einfaedig (laufProj code M.lauf) := by
  intro i j f g c s s' ei ej hi hj hmi hmj
  unfold laufProj at hi hj
  rw [List.getElem?_map] at hi hj
  cases hxi : M.lauf[i]? with
  | none =>
      rw [hxi] at hi
      simp at hi
  | some si =>
      rw [hxi] at hi
      cases hxj : M.lauf[j]? with
      | none =>
          rw [hxj] at hj
          simp at hj
      | some sj =>
          rw [hxj] at hj
          cases si with
          | mk fi ei' =>
              cases sj with
              | mk fj ej' =>
                  have hi2 : schrittProj code (Schritt.mk fi ei') =
                      Marken.Schritt.mk f ei := by
                    simpa using hi
                  have hj2 : schrittProj code (Schritt.mk fj ej') =
                      Marken.Schritt.mk g ej := by
                    simpa using hj
                  obtain ⟨rfl, rfl⟩ := hi2
                  obtain ⟨rfl, rfl⟩ := hj2
                  have hli : (ereignisProj code ei').lambda =
                      ei'.lambda.map (markenProj code) := rfl
                  have hlj : (ereignisProj code ej').lambda =
                      ej'.lambda.map (markenProj code) := rfl
                  rw [hli] at hmi
                  rw [hlj] at hmj
                  obtain ⟨ri, hri, hreqi⟩ := List.mem_map.mp hmi
                  obtain ⟨rj, hrj, hreqj⟩ := List.mem_map.mp hmj
                  cases ri with
                  | held L =>
                      exact (markenProj_held_absurd code L c s hreqi).elim
                  | marke mi sti =>
                      cases rj with
                      | held L =>
                          exact (markenProj_held_absurd code L c s' hreqj).elim
                      | marke mj stj =>
                          have hci : code mi = c :=
                            markenProj_marke code mi sti c s hreqi
                          have hcj : code mj = c :=
                            markenProj_marke code mj stj c s' hreqj
                          have hfi : mi ∈ prog.marks fi :=
                            hinv i fi ei' hxi mi sti hri
                          have hfj : mj ∈ prog.marks fj :=
                            hinv j fj ej' hxj mj stj hrj
                          have hmemF : c ∈ (prog.marks fi).map code :=
                            List.mem_map.mpr ⟨mi, hfi, hci⟩
                          have hmemG : c ∈ (prog.marks fj).map code :=
                            List.mem_map.mpr ⟨mj, hfj, hcj⟩
                          by_cases hfg : fi = fj
                          · exact hfg
                          · exact absurd hmemG (hSep fi fj hfg c hmemF)

/-- **W4 on PC runs, same shape as `Gesittet.marke_eindeutig`.** The discharge
    fragment through the construction bridge: no projection premise. -/
theorem pc_marke_eindeutig (code : D.Marke → Nat) (prog : PCProg D)
    (M : GenMaschine D)
    (hinv : PCMarkInv prog M)
    (hSep : PCMarkSep code prog)
    (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
    (ei ej : Ereignis D)
    (hi : M.lauf[i]? = some (Schritt.mk f ei))
    (hj : M.lauf[j]? = some (Schritt.mk g ej))
    (hmi : Res.marke m s ∈ ei.lambda)
    (hmj : Res.marke m s' ∈ ej.lambda) : f = g :=
  marke_eindeutig_aus_einfaedig code M.lauf
    (pc_discharge_einfaedig code prog M hinv hSep) i j f g m s s' ei ej hi hj hmi hmj

/-- **The declaration side discharges from program text.** If an unshared
    carrier is accessed from two threads, both threads' texts reach it --
    against `PCUnsharedSep`. This replaces the `hungeteilt` declaration side.
    The shared-side hypothesis comes before the access equations: a `match` on
    `o` elaborates extra discriminants for hypotheses that already mention `o`,
    so the match must precede them to keep the `Gesittet` shape. -/
theorem pc_discharge_unshared (prog : PCProg D) (M : GenMaschine D)
    (hinv : PCCarrierInv prog M)
    (hSep : PCUnsharedSep prog)
    (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
    (ei ej : Ereignis D)
    (hi : M.lauf[i]? = some (Schritt.mk f ei))
    (hj : M.lauf[j]? = some (Schritt.mk g ej))
    (hsh : match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false)
    (hti : ei.traeger = some o) (htj : ej.traeger = some o) :
    f = g := by
  have hfi : o ∈ prog.carriers f := hinv i f ei hi o hti
  have hgj : o ∈ prog.carriers g := hinv j g ej hj o htj
  by_cases hfg : f = g
  · exact hfg
  · exact ((hSep f g hfg o hfi hgj) hsh).elim

/-- **W1, W2, W4 on PC runs, with no projection premise.** W1+W2 come from the
    generated side through the projection; W4 comes from the program text
    through the discharge fragment. Same triple shape as `gen_w1w2w4`. -/
theorem pc_w1w2w4 (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog) :
    (∀ f j, Konsistent (M.lauf.spur f j)) ∧
    (∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut) ∧
    (∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g) := by
  refine ⟨pc_konsistent P O passes hO prog sp M pc h,
    pc_gut_obs P O passes hO prog sp M pc h, ?_⟩
  intro i j f g m s s' ei ej hi hj hmi hmj
  exact pc_marke_eindeutig code prog M
    (pcReach_markInv P O passes prog sp M pc h) hMSep
    i j f g m s s' ei ej hi hj hmi hmj

/-- **A PC run is `Gesittet`, with neither premise.** W1-W3 are generated, W4 is
    discharged from program text, W5 from carrier separation. -/
theorem pc_gesittet (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog)
    (hCSep : PCUnsharedSep prog) :
    Gesittet M.lauf :=
  gesittet_aus_einfaedig M.lauf
    (pc_konsistent P O passes hO prog sp M pc h)
    (pc_gut_obs P O passes hO prog sp M pc h)
    (pc_ausschluss P O passes hO prog sp M pc h)
    code
    (pc_discharge_einfaedig code prog M
      (pcReach_markInv P O passes prog sp M pc h) hMSep)
    (fun i j f g o ei ej hi hj hti htj hsh =>
      pc_discharge_unshared prog M
        (pcReach_carrierInv P O passes prog sp M pc h) hCSep
        i j f g o ei ej hi hj hsh hti htj)

/-- **Reduction, serial order, from a PC run (two-access single-carrier
    fragment).** Same interface as `gen_reduktion`: two conflicting accesses in
    a PC run are happens-before ordered, in one direction or the other. Closes
    via `reduktion_seriell` with `Gesittet` derived from positions. -/
theorem pc_reduktion (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog)
    (hCSep : PCUnsharedSep prog)
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁ :=
  reduktion_seriell M.lauf
    (pc_gesittet P O passes hO prog sp M pc h code hMSep hCSep)
    t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.pcAdvance_self
#print axioms Gabbro.Grammatik.pcAdvance_noteq
#print axioms Gabbro.Grammatik.pcSchritt_gen
#print axioms Gabbro.Grammatik.pcReach_gen
#print axioms Gabbro.Grammatik.pcSchritt_eigen
#print axioms Gabbro.Grammatik.pcSchritt_fremd
#print axioms Gabbro.Grammatik.pc_konsistent
#print axioms Gabbro.Grammatik.pc_gut_obs
#print axioms Gabbro.Grammatik.pc_ausschluss
#print axioms Gabbro.Grammatik.pcAtom_mem_marks
#print axioms Gabbro.Grammatik.pcAtom_mem_carriers
#print axioms Gabbro.Grammatik.pcStart_markInv
#print axioms Gabbro.Grammatik.pcStart_carrierInv
#print axioms Gabbro.Grammatik.pcSchritt_markInv
#print axioms Gabbro.Grammatik.pcSchritt_carrierInv
#print axioms Gabbro.Grammatik.pcReach_markInv
#print axioms Gabbro.Grammatik.pcReach_carrierInv
#print axioms Gabbro.Grammatik.markenProj_marke
#print axioms Gabbro.Grammatik.markenProj_held_absurd
#print axioms Gabbro.Grammatik.pc_discharge_einfaedig
#print axioms Gabbro.Grammatik.pc_marke_eindeutig
#print axioms Gabbro.Grammatik.pc_discharge_unshared
#print axioms Gabbro.Grammatik.pc_w1w2w4
#print axioms Gabbro.Grammatik.pc_gesittet
#print axioms Gabbro.Grammatik.pc_reduktion

end Gabbro.Grammatik

/-! ## 13. The chain-machine link: generated PC worlds read as chain worlds

    `SerialLink` (§22 of `InterferenzAllgemein.lean`) is the ORDER side of the
    run-to-chain link: every writing chain step owns a witness access in the
    run. This section is the WORLD side: a generated PC run's world history
    `M.welten` read as the chain worlds `J.welten`.

    Import check (no cycle): `GemeinsamerLauf` and `SerialLink` already arrive
    through `Grammatik.InterferenzAllgemein` and `Nebeneinander` through
    `Grammatik.Wettlauf` (the two imports at the head of this file), so this
    section adds no import.

    What is proved (`kette_ist_maschinenwelt` below, no `sorry`): under the
    explicit identification `J.welten = M.welten`, the chain worlds inherit
    everything the generated side proves about its history -- the count
    (`genWelten_laenge`), good observations (`genWelten_gut`), and the live
    end-world shape (`genWelten_letzte`) -- projected through `pcReach_gen`.
    Every premise is load-bearing: `P O passes hO prog sp M pc h` feed the
    projection and the three world lemmas, `J` types the identification and the
    conclusion, and `hW` rewrites each conjunct onto the generated history.

    Coverage (exactly): boundary observations only -- length, goodness, and end
    shape of the world list. The full equivalence (deriving the identification
    itself from step correspondence: chain steps close over whole bodies via
    `exec` while machine steps close over leaf statements via `execStmt`, plus
    the `Nb`/`Gesittet` wiring and the `SerialLink` witnesses) is NOT built.

    Remainder (booked, not hidden): constructing a `GemeinsamerLauf` from a
    `PCReach` run (or the converse) without assuming `hW`; per-step `Rahmen`
    correspondence between chain steps and machine micro-steps; lifting
    `SerialLink` witnesses to that constructed chain.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The chain-machine link, boundary-observation fragment.** A generated PC
    run's worlds read as chain worlds: identified histories share the count,
    the observations, and the end shape. One direction only (machine to chain,
    under explicit identification); see §13 for the remainder. -/
theorem kette_ist_maschinenwelt (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hW : J.welten = M.welten) :
    J.welten.length = M.tiefe + 1 ∧
    (∀ W ∈ J.welten, ∀ e ∈ W.spur, e.gut) ∧
    (∃ f, J.welten.getLast? = some (M.speicher.welt (M.spuren f))) := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog (GenStart sp) M pc h
  refine ⟨?_, ?_, ?_⟩
  · rw [hW]
    exact genWelten_laenge P O passes hO sp M hG
  · rw [hW]
    exact genWelten_gut P O passes hO sp M hG
  · rw [hW]
    exact genWelten_letzte P O passes hO sp M hG

#print axioms Gabbro.Grammatik.kette_ist_maschinenwelt

end Gabbro.Grammatik

/-! ## 14. The chain from the machine: identification by construction

    `kette_ist_maschinenwelt` (§13) reads machine worlds as chain worlds UNDER
    the assumed identification `hW : J.welten = M.welten`. This section derives
    the identification itself -- however narrow -- instead of assuming it.

    What is proved (no `sorry`):

    - `kette_aus_maschinenlauf`: the zero-step base. From shared memory `sp`
      and one function entry `fn0`, the start machine `GenStart sp` IS a
      chain: worlds, run, and `SerialLink` come along by construction, so the
      identification `J.welten = M.welten` holds by `rfl`, never assumed.
      `SerialLink` holds vacuously: a chain with no steps has no writing step
      that could owe a witness.
    - `kette_aus_maschinenlauf_schritt`: one induction step over a
      memory-preserving machine step. From a chain `J` tracking `M` (the
      world history `hJw`, a member thread `hmem`, the inherited link `hLink`)
      and a successor `M'` whose worlds append one memory-preserving world
      (`hM'w` with `hslots` / `hglobs`) and whose run appends one step of `f`
      (`hM'l`), the extended chain tracks `M'`, again by construction
      (`rfl`). `Gesittet` and the scheduler rule for the extended run come
      from the read-only projection theorems (`gen_konsistent`,
      `gen_gut_obs`, `gen_ausschluss`); ownership (`marke_eindeutig`,
      `ungeteilt`) and the declaration side (`BeschraenkteVerschraenkung`)
      come from the single-thread premise (`hsingle`): every run step is
      `f`'s, so distinct-thread conclusions close by arithmetic. The frame
      (`hSchritt`) for the new step holds for ANY writer frame because lock
      steps keep slots and globals by construction -- no `exec` / `execStmt`
      correspondence is needed at this boundary. `SerialLink` is inherited
      along the old steps (witness indices transport over the run prefix) and
      vacuous at the new step under the non-writer guard.
    - `kette_aus_maschinenlauf_nimmt` / `_gibt`: the two lock-step
      instantiations, via the `GenSchritt` constructors as evidence.

    Read-only inputs, never modified: `gen_konsistent`, `gen_gut_obs`,
    `gen_ausschluss`, `genWelten_letzte`, `gen_eigen_getElem`, `GenStart`,
    `GenSchritt.nimmt`, `GenSchritt.gibt`. Every premise is load-bearing
    (each one is consumed by its proof; the old run-link `J.l = M.lauf` is
    deliberately NOT taken as a premise because the run side rebuilds from
    the projection theorems instead of transporting).

    Coverage (exactly): the start machine, plus one single-thread lock step
    (`nimmt` / `gibt`) by a member thread, with `SerialLink` vacuous at the
    base and guarded-vacuous at the new step.

    Remainder (booked, not hidden): `blatt` steps -- the `execStmt` frame is
    for the statement's own contract, while `hSchritt` needs the code
    function's writes (`Nb` / code wiring, as §13 books it); iterating the
    step over a whole `PCReach` (counter routing via `pcSchritt_gen` /
    `pcReach_gen` stays future work); multi-thread runs (discharging
    `hsingle` needs the `Einfaedig` projection plus the declaration side, as
    `gen_gesittet` books them); non-vacuous `SerialLink` witnesses for
    writing steps; globals and multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The chain from the machine, zero-step base.** The start machine over
    shared memory is a chain by construction: empty thread list, empty step
    list, the generated worlds and the empty run. The identification holds by
    `rfl`; `SerialLink` holds vacuously over any carrier. -/
theorem kette_aus_maschinenlauf (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    ∃ J : GemeinsamerLauf (D := D) Nb,
      J.welten = (GenStart sp).welten ∧
      J.l = (GenStart sp).lauf ∧
      ∀ t₀ : D.Tab, SerialLink Nb J (GenStart sp).lauf t₀ := by
  have hGes : Gesittet ([] : Lauf D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro f j
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
      rw [hsp]
      exact konsistent_nil
    · intro f j e he
      have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
      rw [hsp] at he
      simp at he
    · intro j f L h hi g hne
      simp at hi
    · intro i j f g m s s' ei ej hi hj hm hm'
      simp at hi
    · intro i j f g o ei ej hi hj ht1 ht2 hu
      simp at hi
  have hBeschr : BeschraenkteVerschraenkung (D := D) Nb ([] : Lauf D) := by
    intro i j f g ei ej hi hj hne
    simp at hi
  have hKette0 : (GenStart sp).welten.length = ([] : List Faden).length + 1 := by
    simp [GenStart]
  have hSchritt0 : ∀ (k : Nat) (f : Faden) (vor nach : World D),
      ([] : List Faden)[k]? = some f → (GenStart sp).welten[k]? = some vor →
      (GenStart sp).welten[k + 1]? = some nach →
      f ∈ ([] : List Faden) ∧
        Rahmen (D.schreibt ((fun _ => fn0) f)) (D.gschreibt ((fun _ => fn0) f)) vor nach := by
    intro k f vor nach hk _ _
    simp at hk
  have hPaar0 : ∀ (f : Faden), f ∈ ([] : List Faden) → ∀ (g : Faden),
      g ∈ ([] : List Faden) → f ≠ g → Nb f g := by
    intro f hf
    simp at hf
  have hEintritt0 : ∀ (f : Faden), f ∈ ([] : List Faden) →
      EintrittPasst ((fun _ => fn0) f) ((fun _ => (GenStart sp).start) f) := by
    intro f hf
    simp at hf
  have hSchuld0 : ∀ (f : Faden), f ∈ ([] : List Faden) →
      SchuldnerHaelt ((fun _ => fn0) f) := by
    intro f hf
    simp at hf
  have hInvSicht0 : ∀ (f : Faden), f ∈ ([] : List Faden) →
      InvSichtHaelt ((fun _ => fn0) f) ((fun _ => (GenStart sp).start) f) := by
    intro f hf
    simp at hf
  refine ⟨{ faeden := [], code := fun _ => fn0, eintritt := fun _ => (GenStart sp).start,
            welten := (GenStart sp).welten, schrittFaden := [], l := ([] : Lauf D),
            hKette := hKette0, hSchritt := hSchritt0, hPaar := hPaar0,
            hGesittet := hGes, hBeschraenkt := hBeschr,
            hEintritt := hEintritt0, hSchuld := hSchuld0, hInvSicht := hInvSicht0 },
          rfl, rfl, ?_⟩
  intro t₀ k g hk _
  have hk' : ([] : List Faden)[k]? = some g := hk
  simp at hk'

/-- **The chain from the machine, one induction step.** A chain tracking `M`
    extends along one memory-preserving step of a member thread: worlds and
    run by construction (`rfl`), order and goodness from the read-only
    projection theorems, ownership and declaration side from the single-thread
    run, the new frame from memory preservation, `SerialLink` inherited plus
    guarded-vacuous at the new step. -/
theorem kette_aus_maschinenlauf_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (e : Ereignis D) (nach : World D)
    (hM'l : M'.lauf = M.lauf ++ genEigen f [e])
    (hM'w : M'.welten = M.welten ++ [nach])
    (hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nach.slots t k fld = M.speicher.slots t k fld)
    (hglobs : ∀ g : D.Glob, nach.globs g = M.speicher.globs g)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  have hlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hReach
  have hLastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  have hfaden : ∀ (i : Nat) (g : Faden) (ei : Ereignis D),
      M'.lauf[i]? = some (Schritt.mk g ei) → g = f := by
    intro i g ei hi
    rw [hM'l] at hi
    by_cases hlt : i < M.lauf.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hsingle _ (List.mem_of_getElem? hi)
    · have hle : M.lauf.length ≤ i := by omega
      rw [List.getElem?_append_right hle] at hi
      exact (gen_eigen_getElem f [e] _ _ _ hi).1
  have hGes' : Gesittet M'.lauf := by
    refine ⟨gen_konsistent P O passes hO sp M' hReach',
            gen_gut_obs P O passes hO sp M' hReach',
            gen_ausschluss P O passes hO sp M' hReach', ?_, ?_⟩
    · intro i j g1 g2 m s s' e1 e2 hi hj _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
    · intro i j g1 g2 o e1 e2 hi hj _ _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
  have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
    intro i j g1 g2 e1 e2 hi hj hne
    have h1 := hfaden i g1 e1 hi
    have h2 := hfaden j g2 e2 hj
    exact absurd (h1.trans h2.symm) hne
  have hKette' : M'.welten.length = (J.schrittFaden ++ [f]).length + 1 := by
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp
    omega
  have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach0 : World D),
      (J.schrittFaden ++ [f])[k]? = some g0 → M'.welten[k]? = some vor →
      M'.welten[k + 1]? = some nach0 →
      g0 ∈ J.faeden ∧
        Rahmen (D.schreibt (J.code g0)) (D.gschreibt (J.code g0)) vor nach0 := by
    intro k g0 vor nach0 hk hkv hkn
    rw [hM'w] at hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
        List.getElem?_append_left hlt
      rw [e1] at hk
      have hltM : k < M.welten.length := by omega
      have e2 : (M.welten ++ [nach])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [nach])[k + 1]? = M.welten[k + 1]? :=
        List.getElem?_append_left hltM1
      rw [e3] at hkn
      have hJkn : J.welten[k + 1]? = some nach0 := by rw [hJw]; exact hkn
      exact J.hSchritt k g0 vor nach0 hk hJkv hJkn
    · by_cases heq : k = J.schrittFaden.length
      · subst heq
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk
        have hg0 : g0 = f := (Option.some_inj.mp hk).symm
        have eW : (M.welten ++ [nach])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [nach])[J.schrittFaden.length + 1]? = some nach := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : nach = nach0 := Option.some_inj.mp hkn
        rw [hg0, hvor, ← hnach0]
        refine ⟨hmem, ?_, ?_⟩
        · intro t _ k2 fld
          exact hslots t k2 fld
        · intro g _
          exact hglobs g
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, ?_⟩
  intro t₀ hnw k0 g0 hk0 hwr
  have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
  have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
  by_cases hlt : k0 < J.schrittFaden.length
  · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk0'
    obtain ⟨j, w, Λ, h, hw⟩ := hLink t₀ k0 g0 hk0' hwr0
    have hjlt : j < M.lauf.length := by
      by_cases h : j < M.lauf.length
      · exact h
      · have hle : M.lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp at hw
    have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λ h)) := by
      rw [hM'l, List.getElem?_append_left hjlt]
      exact hw
    exact ⟨j, w, Λ, h, hw'⟩
  · by_cases heq : k0 = J.schrittFaden.length
    · subst heq
      have hg0 : g0 = f := by
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk0'
        exact (Option.some_inj.mp hk0').symm
      rw [hg0] at hwr
      have hwrF : TraegerSchreibt (J.code f) (.inl t₀) = true := hwr
      rw [hnw] at hwrF
      simp at hwrF
    · have hle : J.schrittFaden.length ≤ k0 := by omega
      have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk0'
      simp at hk0'

/-- **The chain from the machine, lock-take instance.** A fireable `nimmt`
    step of a member thread extends a tracking chain: the successor and its
    evidence come from the `GenSchritt` constructor, the link from the
    one-step extension. -/
theorem kette_aus_maschinenlauf_nimmt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hself : L ∉ offen (M.spuren f))
    (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
    (hfrei : GenFrei M f L)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ M' : GenMaschine D, ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  let eN : Ereignis D := Ereignis.nimmt L (offen (M.spuren f))
  let nachN : World D := M.speicher.welt (eN :: M.spuren f)
  let M' : GenMaschine D :=
    ⟨M.speicher, genUpdate M.spuren f (eN :: M.spuren f),
     M.lauf ++ genEigen f [eN], M.start, M.welten ++ [nachN], M.tiefe + 1⟩
  have hs : GenSchritt P O passes M f M' :=
    GenSchritt.nimmt M f L hself hrang hfrei
  have hReach' : GenErreichbar P O passes (GenStart sp) M' :=
    GenErreichbar.schritt M M' f hReach hs
  have hM'l : M'.lauf = M.lauf ++ genEigen f [eN] := rfl
  have hM'w : M'.welten = M.welten ++ [nachN] := rfl
  have hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nachN.slots t k fld = M.speicher.slots t k fld := fun t k fld => rfl
  have hglobs : ∀ g : D.Glob, nachN.globs g = M.speicher.globs g := fun g => rfl
  refine ⟨M', ?_⟩
  exact kette_aus_maschinenlauf_schritt P O passes hO sp Nb M M' f
    hReach hReach' eN nachN hM'l hM'w hslots hglobs J hJw hmem hLink hsingle

/-- **The chain from the machine, lock-release instance.** A held `gibt`
    step of a member thread extends a tracking chain: same shape as the
    take instance, memory-preserving by the same construction. -/
theorem kette_aus_maschinenlauf_gibt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hhaelt : L ∈ offen (M.spuren f))
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ M' : GenMaschine D, ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  let eG : Ereignis D := Ereignis.gibt L
  let nachG : World D := M.speicher.welt (eG :: M.spuren f)
  let M' : GenMaschine D :=
    ⟨M.speicher, genUpdate M.spuren f (eG :: M.spuren f),
     M.lauf ++ genEigen f [eG], M.start, M.welten ++ [nachG], M.tiefe + 1⟩
  have hs : GenSchritt P O passes M f M' :=
    GenSchritt.gibt M f L hhaelt
  have hReach' : GenErreichbar P O passes (GenStart sp) M' :=
    GenErreichbar.schritt M M' f hReach hs
  have hM'l : M'.lauf = M.lauf ++ genEigen f [eG] := rfl
  have hM'w : M'.welten = M.welten ++ [nachG] := rfl
  have hslots : ∀ (t : D.Tab) (k : Int) (fld : D.Feld t),
      nachG.slots t k fld = M.speicher.slots t k fld := fun t k fld => rfl
  have hglobs : ∀ g : D.Glob, nachG.globs g = M.speicher.globs g := fun g => rfl
  refine ⟨M', ?_⟩
  exact kette_aus_maschinenlauf_schritt P O passes hO sp Nb M M' f
    hReach hReach' eG nachG hM'l hM'w hslots hglobs J hJw hmem hLink hsingle

#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_schritt
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_nimmt
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_gibt

end Gabbro.Grammatik

/-! ## 15. The scheduler atom identity (S12, slot-collapse fragment)

    What `Ziel.lean` §9b books as atom identity (S12): the scheduled counter at
    each step points at exactly the atom `stmtAtome_blatt_eq`
    (`Extraktion.lean` §14) yields for the fired statement -- per step and per
    run -- feeding the `hpc`/`hΛa`/`hcs` slots of `PCSchritt.leaf` (§12) and of
    the lifter `pcSchritt_blatt_progAus_ohne_axiomCall`.

    What closes HERE (no `sorry`, PC shapes only -- this file cannot see
    `Extraktion`: `Extraktion.lean` imports this file, so the instantiation
    `prog := Extraktion.progAus ...` with
    `cs₀ := Extraktion.stmtTraeger ... ++ Extraktion.stmtOrte ...` plus the
    `stmtAtome_blatt_eq` rewrite lives one level up, where both modules are
    visible):

    - `zaehler_zeigt_atom`: the three leaf slots collapse to one identity --
      from `hpc`/`hΛa`/`hcs` over any `prog`, the counter points at
      `leaf Λ cs₀`. Under the extraction instantiation this IS the
      `stmtAtome_blatt_eq` atom of the fired statement.
    - `hpc_hΛa_hcs_aus_zaehler`: the discharge corollary -- one posited
      identity feeds all three `PCSchritt.leaf` slots
      (`∃ Λa cs, hpc ∧ hΛa ∧ hcs`), so a witness positing the identity owes
      nothing more per leaf step.
    - `zaehler_zeigt_atom_lauf`: the per-run form -- any leaf step occurring
      anywhere in a generated run derivation (`SchrittImLauf`: the last step,
      or a step of the prefix) satisfies the same identity. The step proof
      `hs` evidences that the step fired, the membership proof that it fired
      in THIS run, the triple that it fired as this leaf.

    Remainder (booked, not hidden): deriving the identity FROM the run -- that
    a witness-built `PCReach` over `progAus` always posits the extracted atom
    -- is the scheduler-construction duty and stays open (S12); the `take`/
    `rel` bracket correspondence (`stmtAtome_locks` sides) and the `axiomCall`
    event contract (S13) likewise; calls and compounds never fire as leaves
    (`istBlatt = false`), so they owe no leaf identity. Positions stay
    derivation-external: proof irrelevance forbids computing a thread's step
    count off a `PCReach` derivation (large elimination -- measured above),
    so no endpoint-level atom identity is stated; per-run coverage IS
    per-step coverage at every occurring step.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The counter identity, leaf fragment.** The three `PCSchritt.leaf` counter
    slots (`hpc`: the counter points at `leaf Λa cs`; `hΛa`: that `Λa` is the
    fired footprint; `hcs`: those `cs` are the extracted carriers) collapse to
    one identity: the counter points at `leaf Λ cs₀`. Every premise is
    load-bearing: `prog`/`f`/`pc`/`Λa`/`cs` type `hpc`, `Λ`/`cs₀` type the
    rewrites and the conclusion. -/
theorem zaehler_zeigt_atom (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (prog f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ) (hcs : cs = cs₀) :
    (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀) := by
  rw [hΛa, hcs] at hpc
  exact hpc

/-- **The discharge corollary: one identity feeds the three leaf slots.** A
    witness positing the counter identity owes `hpc`/`hΛa`/`hcs` of
    `PCSchritt.leaf` (and hence of the `progAus` lifter) at once: the triple
    is the unpacked existential. Every premise is load-bearing:
    `prog`/`f`/`pc`/`Λ`/`cs₀` type `hident`, `hident` is the witness. -/
theorem hpc_hΛa_hcs_aus_zaehler (prog : PCProg D) (f : Faden) (pc : PCStand)
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (hident : (prog f)[pc f]? = some (PCAtom.leaf Λ cs₀)) :
    ∃ Λa : List (Res D), ∃ cs : List (D.Tab ⊕ D.Glob),
      (prog f)[pc f]? = some (PCAtom.leaf Λa cs) ∧ Λa = Λ ∧ cs = cs₀ := by
  exact ⟨Λ, cs₀, hident, rfl, rfl⟩

/-- **A generated step occurring in a generated run derivation**: the last
    step (`letzter`), or a step of the prefix (`frueher`). The step proof is
    fixed; the run varies over derivations containing it. -/
inductive SchrittImLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc') :
    ∀ {M : GenMaschine D} {pc : PCStand},
    PCReach P O passes prog M0 M pc → Prop where
  | letzter (h : PCReach P O passes prog M0 Mmid pcmid) :
      SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs
        (PCReach.step Mmid M' pcmid pc' f h hs)
  | frueher {M'' : GenMaschine D} {pc'' : PCStand} {g : Faden}
      {M''' : GenMaschine D} {pc''' : PCStand}
      (h : PCReach P O passes prog M0 M'' pc'')
      (hs2 : PCSchritt P O passes prog M'' pc'' g M''' pc''')
      (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
      SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs
        (PCReach.step M'' M''' pc'' pc''' g h hs2)

/-- **The counter identity, per run.** Any leaf step occurring anywhere in a
    generated run derivation points at `leaf Λ cs₀`: the step proof `hs`
    evidences that the step fired, the membership proof that it fired in this
    run, the triple that it fired as this leaf. Every premise is load-bearing:
    `prog`/`M0`/`Mmid`/`pcmid`/`f`/`M'`/`pc'`/`P`/`O`/`passes` type `hs` and
    `hmem`, `hs` is the fired step, `Λ`/`cs₀`/`Λa`/`cs`/`hpc`/`hΛa`/`hcs`
    feed the per-step identity, `M`/`pc`/`h` type `hmem`, `hmem` is cased on. -/
theorem zaehler_zeigt_atom_lauf (prog : PCProg D) (M0 : GenMaschine D)
    (Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (prog f)[pcmid f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ) (hcs : cs = cs₀)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    (prog f)[pcmid f]? = some (PCAtom.leaf Λ cs₀) := by
  cases hmem with
  | letzter _ =>
      exact zaehler_zeigt_atom prog f pcmid Λ cs₀ Λa cs hpc hΛa hcs
  | frueher _ _ _ =>
      exact zaehler_zeigt_atom prog f pcmid Λ cs₀ Λa cs hpc hΛa hcs

#print axioms Gabbro.Grammatik.zaehler_zeigt_atom
#print axioms Gabbro.Grammatik.hpc_hΛa_hcs_aus_zaehler
#print axioms Gabbro.Grammatik.zaehler_zeigt_atom_lauf

end Gabbro.Grammatik

/-! ## 16. The counter identity from construction (S12, first-step fragment)

    Section 15 collapses the three leaf slots (`hpc`/`hΛa`/`hcs`) to one
    identity and books the remainder honestly: deriving the identity FROM the
    run -- that a witness-built `PCReach` over `progAus` always posits the
    extracted atom -- stays open as the scheduler-construction duty (S12).
    This section closes its first fragment, from the scheduler threading
    alone (start-zero counters, advance-only-the-acting-thread) plus one
    program-text posit per thread.

    The threading (read-only reuse of Section 12 shapes, nothing re-proved):
    counters start at zero (`PCReach.start`), each step advances exactly its
    acting thread by one (`pcSchritt_eigen`, i.e. `pcAdvance`) and moves no
    other (`pcSchritt_fremd`). From this follows, by induction over run
    derivations (propositions only -- no step counting, so no large
    elimination; cf. the proof-irrelevance booking in Section 15):

    - `pc_zero_without_prior_step`: a thread with no step yet in the
      derivation stands at zero;
    - `pc_ne_zero_with_prior_step`: a thread with a step in the derivation
      stands off zero.

    The program-text side is `HeadAtom`: thread `f`'s text head IS the
    extracted leaf atom `leaf Λ cs₀`. This restates locally, with a cite and
    without duplicating any proof, what `Extraktion.stmtAtome_blatt_eq`
    (Section 14 there) yields for the fired leaf statement together with
    `Extraktion.progAus` (which computes the thread text from bodies): this
    file cannot import `Extraktion` (`Extraktion.lean` imports this file),
    so the instantiation `prog := progAus ...` lives one level up, exactly
    as in Section 15. `HeadAtom` is the remainder of this section in
    concentrated form: posited once per thread (extraction output), it feeds
    every first step, where Section 15 posits three slots per step.

    What closes here (no `sorry`, scheduler shapes only):

    - `zaehler_aus_konstruktion_erstschritt`: the first step by `f` (no
      prior step of `f` in the prefix derivation) over head-shaped text
      fires at counter zero -- derived from the threading, not posited --
      points at the head atom -- computed from the text shape, never from
      the step's `hpc` slot -- and advances to one. Every premise is
      load-bearing: `hs` feeds the advance (`pcSchritt_eigen`), `h`/`hfrei`
      feed the zero (`pc_zero_without_prior_step`), `hprog` feeds the atom.
    - `zaehler_aus_konstruktion_einzelblatt_lauf`: the per-run form for
      single-leaf threads (`prog f = [leaf Λ cs₀]`): EVERY leaf step
      occurring anywhere in a generated run (`SchrittImLauf`, as in
      `zaehler_zeigt_atom_lauf`) satisfies the same identity, because over
      singleton text every occurring step IS a first step -- a prior step
      of `f` would stand the counter off zero, where the text has no atom
      (`List.getElem?_eq_none`), contradicting the step's own `hpc`. A
      second step by `f` is therefore impossible BY CONSTRUCTION, and
      `take`/`rel` steps are impossible over singleton-leaf text for the
      same reason (their `hpc` contradicts the text shape at every index).

    What still posits identity (booked, not hidden): the text shape itself
    (`HeadAtom`, resp. the singleton equation -- once per thread, justified
    by the `progAus` computation, never derived here); every non-first step
    over non-singleton text (the general scheduling argument: which
    statement fires at counter `k > 0` of a multi-atom text is still the
    witness/scheduler duty, as in Section 15); the exact footprint
    equalities inside each step occurrence (`Λa = Λ`, `cs = cs₀` there --
    positional identity is derived, naming an occurrence's slots is not);
    the `hmark`/`hcar` discharge (untouched, `Extraktion` Sections 17-18);
    the `take`/`rel` bracket correspondence (`stmtAtome_locks` sides) and
    the `axiomCall` event contract (S13) likewise. Section 15 stands
    unchanged; this section narrows its remainder without closing it.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The program-text head, restated locally (cite, no proof).** Thread
    `f`'s text head is the extracted leaf atom `leaf Λ cs₀`: what
    `Extraktion.stmtAtome_blatt_eq` (a leaf statement extracts to exactly
    one atom carrying its own `Λ`) yields for the fired statement, read at
    counter zero of the `Extraktion.progAus` text. This file cannot import
    `Extraktion` (`Extraktion.lean` imports this file), so the shape is
    restated here as the per-thread posit and its proof is never
    duplicated. Under the extraction instantiation this IS the
    `stmtAtome_blatt_eq` atom of the fired statement. -/
def HeadAtom (prog : PCProg D) (f : Faden) (Λ : List (Res D))
    (cs₀ : List (D.Tab ⊕ D.Glob)) : Prop :=
  (prog f)[0]? = some (PCAtom.leaf Λ cs₀)

/-- **A thread fired in a run derivation**: the acting thread of the last
    step (`here`), or of a prefix step (`later`). Proposition-valued (no
    step counting), so induction over it stays inside `Prop`. -/
inductive ThreadFiredIn (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) (f : Faden) :
    ∀ {M : GenMaschine D} {pc : PCStand},
    PCReach P O passes prog M0 M pc → Prop where
  | here {M M' : GenMaschine D} {pc pc' : PCStand}
      (h : PCReach P O passes prog M0 M pc)
      (hs : PCSchritt P O passes prog M pc f M' pc') :
      ThreadFiredIn P O passes prog M0 f (PCReach.step M M' pc pc' f h hs)
  | later {M M' : GenMaschine D} {pc pc' : PCStand} (g : Faden)
      (h : PCReach P O passes prog M0 M pc)
      (hs : PCSchritt P O passes prog M pc g M' pc')
      (hprev : ThreadFiredIn P O passes prog M0 f h) :
      ThreadFiredIn P O passes prog M0 f (PCReach.step M M' pc pc' g h hs)

/-- **Threading, zero direction.** A thread with no step yet in the
    derivation stands at zero: counters start at zero and only the acting
    thread advances (`pcSchritt_fremd` keeps every other). Every premise is
    load-bearing: `h` is cased on, `hfree` rules out the acting case and
    feeds the induction hypothesis. -/
theorem pc_zero_without_prior_step (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) (f : Faden)
    {M : GenMaschine D} {pc : PCStand}
    (h : PCReach P O passes prog M0 M pc)
    (hfree : ¬ ThreadFiredIn P O passes prog M0 f h) : pc f = 0 := by
  revert hfree
  induction h with
  | start =>
      intro _
      rfl
  | step _M _M' _pc _pc' g h hs ih =>
      intro hfree
      by_cases heq : g = f
      · subst heq
        exact absurd (ThreadFiredIn.here h hs) hfree
      · have hkeep :=
          pcSchritt_fremd _ _ _ _ _ _ _ _ _ _ hs (fun hcon : f = g => heq hcon.symm)
        rw [hkeep]
        apply ih
        intro hfire
        exact hfree (ThreadFiredIn.later g h hs hfire)

/-- **Threading, nonzero direction.** A thread with a step in the derivation
    stands off zero: its own step advances past zero (`pcSchritt_eigen`),
    others' steps keep a nonzero stand (`pcSchritt_fremd`). Induction runs
    over the firing evidence, propositions only. Every premise is
    load-bearing: `hfire` is cased on, `hs` feeds both advances. -/
theorem pc_ne_zero_with_prior_step (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) (f : Faden)
    {M : GenMaschine D} {pc : PCStand}
    (h : PCReach P O passes prog M0 M pc)
    (hfire : ThreadFiredIn P O passes prog M0 f h) : pc f ≠ 0 := by
  induction hfire with
  | here _h hs =>
      have hadv := pcSchritt_eigen _ _ _ _ _ _ _ _ _ hs
      rw [hadv]
      exact Nat.succ_ne_zero _
  | later g _h hs _ ih =>
      by_cases heq : g = f
      · subst heq
        have hadv := pcSchritt_eigen _ _ _ _ _ _ _ _ _ hs
        rw [hadv]
        exact Nat.succ_ne_zero _
      · have hkeep :=
          pcSchritt_fremd _ _ _ _ _ _ _ _ _ _ hs (fun hcon : f = g => heq hcon.symm)
        rw [hkeep]
        exact ih

/-- **The counter identity from construction, first-step fragment.** The
    first step by `f` (no prior step of `f` in the prefix derivation) over
    head-shaped text fires at counter zero -- derived from the threading,
    not posited -- points at the head atom -- computed from the text shape,
    never from the step's `hpc` slot -- and advances to one. Every premise
    is load-bearing: `hs` feeds the advance, `h`/`hfrei` feed the zero,
    `hprog` feeds the atom. -/
theorem zaehler_aus_konstruktion_erstschritt
    (prog : PCProg D) (f : Faden) (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : GenMaschine D) (Mmid : GenMaschine D) (pcmid : PCStand)
    (M' : GenMaschine D) (pc' : PCStand)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (h : PCReach P O passes prog M0 Mmid pcmid)
    (hfrei : ¬ ThreadFiredIn P O passes prog M0 f h)
    (hprog : HeadAtom prog f Λ cs₀) :
    pcmid f = 0 ∧ pc' f = 1 ∧ (prog f)[pcmid f]? = some (PCAtom.leaf Λ cs₀) := by
  have h0 : pcmid f = 0 :=
    pc_zero_without_prior_step P O passes prog M0 f h hfrei
  refine ⟨h0, ?_, ?_⟩
  · have hadv := pcSchritt_eigen P O passes prog Mmid M' pcmid pc' f hs
    rw [h0] at hadv
    exact hadv
  · rw [h0]
    exact hprog

/-- **The counter identity from construction, per-run singleton form.** Over
    single-leaf thread text (`prog f = [leaf Λ cs₀]`) EVERY leaf step
    occurring anywhere in a generated run satisfies the first-step identity:
    a prior step of `f` would stand the counter off zero, where singleton
    text has no atom, contradicting the step's own `hpc` -- so every
    occurring step is a first step, and a second step by `f` is impossible
    by construction. `take`/`rel` steps are impossible over singleton-leaf
    text for the same reason. Every premise is load-bearing: `hs` is cased
    on, `hprog` contradicts every off-zero and every bracket index,
    `h`/`hmem` feed prefix and membership. -/
theorem zaehler_aus_konstruktion_einzelblatt_lauf
    (prog : PCProg D) (f : Faden) (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : GenMaschine D) (Mmid : GenMaschine D) (pcmid : PCStand)
    (M' : GenMaschine D) (pc' : PCStand)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (hprog : prog f = [PCAtom.leaf Λ cs₀])
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    pcmid f = 0 ∧ pc' f = 1 ∧ (prog f)[pcmid f]? = some (PCAtom.leaf Λ cs₀) := by
  have hs0 := hs
  induction hmem with
  | letzter hpre =>
      rcases hs with
        ⟨_V, _l, _Γ, _Λs, _Λs', _s, _ρ, _hleaf, _hΛ, _σ', _neu, _hstep, _hneu,
          _hkn, _Λa, _cs, hpc, _hΛa, _hmark, _hcar⟩
        | ⟨_L, _hself, _hrang, _hfr, hpcT⟩
        | ⟨_L, _hhaelt, hpcR⟩
      · have hfrei : ¬ ThreadFiredIn P O passes prog M0 f hpre := by
          intro hfire
          have hne : pcmid f ≠ 0 :=
            pc_ne_zero_with_prior_step P O passes prog M0 f hpre hfire
          have hlt : 0 < pcmid f := Nat.pos_of_ne_zero hne
          have h1 : ([PCAtom.leaf Λ cs₀]).length = 1 := by simp
          have hlen : ([PCAtom.leaf Λ cs₀]).length ≤ pcmid f := by
            rw [h1]
            exact Nat.succ_le_of_lt hlt
          have hnone := List.getElem?_eq_none hlen
          rw [hprog, hnone] at hpc
          simp at hpc
        have hhead : HeadAtom prog f Λ cs₀ := by
          show (prog f)[0]? = some (PCAtom.leaf Λ cs₀)
          simp [hprog]
        exact zaehler_aus_konstruktion_erstschritt prog f Λ cs₀ P O passes M0
          Mmid pcmid _ _ hs0 hpre hfrei hhead
      · exfalso
        rw [hprog] at hpcT
        by_cases hz : pcmid f = 0
        · rw [hz] at hpcT
          simp at hpcT
        · have hlt : 0 < pcmid f := Nat.pos_of_ne_zero hz
          have h1 : ([PCAtom.leaf Λ cs₀]).length = 1 := by simp
          have hlen : ([PCAtom.leaf Λ cs₀]).length ≤ pcmid f := by
            rw [h1]
            exact Nat.succ_le_of_lt hlt
          have hnone := List.getElem?_eq_none hlen
          rw [hnone] at hpcT
          simp at hpcT
      · exfalso
        rw [hprog] at hpcR
        by_cases hz : pcmid f = 0
        · rw [hz] at hpcR
          simp at hpcR
        · have hlt : 0 < pcmid f := Nat.pos_of_ne_zero hz
          have h1 : ([PCAtom.leaf Λ cs₀]).length = 1 := by simp
          have hlen : ([PCAtom.leaf Λ cs₀]).length ≤ pcmid f := by
            rw [h1]
            exact Nat.succ_le_of_lt hlt
          have hnone := List.getElem?_eq_none hlen
          rw [hnone] at hpcR
          simp at hpcR
  | frueher _ _ _ ih =>
      exact ih

#print axioms Gabbro.Grammatik.pc_zero_without_prior_step
#print axioms Gabbro.Grammatik.pc_ne_zero_with_prior_step
#print axioms Gabbro.Grammatik.zaehler_aus_konstruktion_erstschritt
#print axioms Gabbro.Grammatik.zaehler_aus_konstruktion_einzelblatt_lauf

end Gabbro.Grammatik

/-! ## 17. The counter identity from construction, full run form (S12, positional fragment)

    Section 16 derives the positional identity for first steps (counter zero
    from the threading plus `HeadAtom`) and for single-leaf threads (every
    occurring step is a first step by construction). This section drops both
    restrictions -- no zero hypothesis, no text shape -- by reading the fired
    atom off the occurring step's own counter slot instead of computing it
    from the program text: every `PCSchritt` carries its fired atom in `hpc`
    (`leaf` / `take` / `rel`), advances exactly its acting thread
    (`pcSchritt_eigen`), and moves no other (`pcSchritt_fremd`).

    What closes here (no `sorry`, step shapes only, read-only reuse of
    Section 12 routing):

    - `zaehler_aus_konstruktion_voll`: every step occurring anywhere in a
      generated run (`SchrittImLauf`, as in `zaehler_zeigt_atom_lauf`) fires
      the atom its counter points at -- leaf, take, or rel, read off the
      step's own counter slot -- and advances its acting thread by one.
      Arbitrary counters (`k > 0` included: no zero hypothesis anywhere),
      arbitrary multi-atom text (no text-shape hypothesis anywhere), all
      three atom kinds (`take` / `rel` were impossible over singleton-leaf
      text in Section 16 and are covered here). Every premise is
      load-bearing: `hs` is cased on (feeds each disjunct's witness),
      `h` / `hmem` feed membership in this run, the advance reuses
      `pcSchritt_eigen`.
    - `zaehler_routing_fremd`: an occurring step by `f` moves no other
      thread's counter -- resumption is explicit at arbitrary `k`
      (`pcSchritt_fremd` read-only): between two firings of `g`, only `g`'s
      own steps move `g`'s counter.
    - `zaehler_routing_gen`: an occurring PC step projects to a generated
      step by the same thread (`pcSchritt_gen` read-only) -- the generated
      run's steps are counter-fired steps.

    What still posits identity (booked, not hidden): the extraction match --
    that the fired atom IS the `progAus` / `stmtAtome` output for the fired
    statement (`Λa = Λ`, `cs = cs₀` per occurrence, the `hmark` / `hcar`
    discharge, the `take` / `rel` bracket correspondence, the `axiomCall`
    event contract) -- stays witness duty per Section 15. This section
    closes the positional routing (the atom the counter points at fires),
    never the extraction naming (which atom the text holds at that
    counter). Sections 15 and 16 stand unchanged; the zero and singleton
    restrictions of Section 16 are lifted here without touching either.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The counter identity from construction, full run form.** Every step
    occurring anywhere in a generated run fires the atom its counter points
    at -- leaf, take, or rel, read off the step's own counter slot -- and
    advances its acting thread by one. No zero hypothesis, no text shape:
    arbitrary counters over arbitrary multi-atom text. Every premise is
    load-bearing: `hs` is cased on (feeds each disjunct), `h` / `hmem` feed
    membership, the advance reuses `pcSchritt_eigen`. -/
theorem zaehler_aus_konstruktion_voll
    (prog : PCProg D) (M0 : GenMaschine D)
    (Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    (∃ Λa : List (Res D), ∃ cs : List (D.Tab ⊕ D.Glob),
      (prog f)[pcmid f]? = some (PCAtom.leaf Λa cs) ∧ pc' f = pcmid f + 1) ∨
    (∃ L : D.Lock, (prog f)[pcmid f]? = some (PCAtom.take L) ∧ pc' f = pcmid f + 1) ∨
    (∃ L : D.Lock, (prog f)[pcmid f]? = some (PCAtom.rel L) ∧ pc' f = pcmid f + 1) := by
  have hadv : pc' f = pcmid f + 1 :=
    pcSchritt_eigen P O passes prog Mmid M' pcmid pc' f hs
  cases hmem with
  | letzter _ =>
      rcases hs with
        ⟨_V, _l, _Γ, _Λs, _Λs', _s, _ρ, _hleaf, _hΛ, _σ', _neu, _hstep, _hneu,
          _hkn, Λa, cs, hpc, _hΛa, _hmark, _hcar⟩
        | ⟨L, _hself, _hrang, _hfrei, hpcT⟩
        | ⟨L, _hhaelt, hpcR⟩
      · exact Or.inl ⟨Λa, cs, hpc, hadv⟩
      · exact Or.inr (Or.inl ⟨L, hpcT, hadv⟩)
      · exact Or.inr (Or.inr ⟨L, hpcR, hadv⟩)
  | frueher _ _ _ =>
      rcases hs with
        ⟨_V, _l, _Γ, _Λs, _Λs', _s, _ρ, _hleaf, _hΛ, _σ', _neu, _hstep, _hneu,
          _hkn, Λa, cs, hpc, _hΛa, _hmark, _hcar⟩
        | ⟨L, _hself, _hrang, _hfrei, hpcT⟩
        | ⟨L, _hhaelt, hpcR⟩
      · exact Or.inl ⟨Λa, cs, hpc, hadv⟩
      · exact Or.inr (Or.inl ⟨L, hpcT, hadv⟩)
      · exact Or.inr (Or.inr ⟨L, hpcR, hadv⟩)

/-- **Resumption is explicit: another thread's occurring step moves no
    counter but its own.** An occurring step by `f` keeps every other
    thread's counter where it stood, at arbitrary `k` over arbitrary text
    (`pcSchritt_fremd` read-only). Every premise is load-bearing: `hs`
    feeds the preservation, `g` / `hne` type it, `h` / `hmem` feed
    membership. -/
theorem zaehler_routing_fremd
    (prog : PCProg D) (M0 : GenMaschine D)
    (Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (g : Faden) (hne : g ≠ f)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    pc' g = pcmid g := by
  cases hmem with
  | letzter _ =>
      exact pcSchritt_fremd P O passes prog Mmid M' pcmid pc' f g hs hne
  | frueher _ _ _ =>
      exact pcSchritt_fremd P O passes prog Mmid M' pcmid pc' f g hs hne

/-- **Counter routing into the generated run.** An occurring PC step projects
    to a generated step by the same thread (`pcSchritt_gen` read-only): the
    generated run's steps are counter-fired steps. Every premise is
    load-bearing: `hs` feeds the projection, `h` / `hmem` feed membership. -/
theorem zaehler_routing_gen
    (prog : PCProg D) (M0 : GenMaschine D)
    (Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    GenSchritt P O passes Mmid f M' := by
  cases hmem with
  | letzter _ =>
      exact pcSchritt_gen P O passes prog Mmid M' pcmid pc' f hs
  | frueher _ _ _ =>
      exact pcSchritt_gen P O passes prog Mmid M' pcmid pc' f hs

#print axioms Gabbro.Grammatik.zaehler_aus_konstruktion_voll
#print axioms Gabbro.Grammatik.zaehler_routing_fremd
#print axioms Gabbro.Grammatik.zaehler_routing_gen

end Gabbro.Grammatik

/-! ## 18. The leaf-frame correspondence: fired leaf steps satisfy the chain-step frame

    `kette_aus_maschinenlauf_schritt` (§14) extends a tracking chain along one
    memory-preserving step: its `hslots` / `hglobs` premises close by `rfl`
    for lock steps, which keep memory by construction. A `blatt` step moves
    memory on writes, so `MaschinenKette.lean` books `blatt` steps as
    remainder under `hlock` (no `PCAtom.leaf` anywhere in `prog`): the
    induction covers exactly the steps that do nothing. This section wires
    the `execStmt` frame into that step: a fired leaf's post-world satisfies
    the chain-step `Rahmen`.

    What is proved (no `sorry`):

    - `blatt_rahmen_vertrag`: the contract frame of a fired step. From the
      firing data (`hstep` out of the thread world `M.weltVon f` under `hΛ`)
      and the oracle bound (`hO`), the post-world keeps the statement
      contract's frame (`Rahmen V.schreibt V.gschreibt`), by direct reuse of
      `stmt_gut` (`Satz.lean`, the `Gut` half that is the frame). The leaf
      shape is the caller's evidence: the frame holds for every fired
      statement, leaves included, so no `hleaf` premise is taken.
    - `blatt_rahmen_schritt`: the code frame of a fired step. The contract
      frame widened (`Rahmen.weiter`) to the thread's code frame
      (`D.schreibt (code f)` / `D.gschreibt (code f)`) under the
      contract-to-code wiring (`hW` / `hG`: the contract writes only where
      the code may write). This is the chain-step frame the induction's
      `hSchritt` consumes at the new step.
    - `kette_aus_maschinenlauf_blatt`: the chain extension along a fired
      framed step. The `kette_aus_maschinenlauf_schritt` construction with
      the same routing premises and the same conclusion, except the
      memory-preservation premises (`hslots` / `hglobs`) are replaced by the
      firing data plus the wiring, and the new-step `Rahmen` closes through
      `blatt_rahmen_schritt` (successor worlds share memory by
      construction, so the frame transfers across definitionally equal
      memories). The step-level lift of the `hlock` exclusion: a framed
      fired leaf extends the tracking chain.

    Read-only inputs, never modified: `stmt_gut`, `keinRuf_gut`,
    `Rahmen.weiter` (`Satz.lean`); the induction-step construction
    (`kette_aus_maschinenlauf_schritt` above, mirrored except for the
    new-step frame); the projection theorems it reuses (`gen_konsistent`,
    `gen_gut_obs`, `gen_ausschluss`, `genWelten_letzte`,
    `gen_eigen_getElem`).

    Event side (cited, not imported): a fired non-oracle leaf's new events
    carry the statement footprint
    (`Extraktion.execEreignis_aus_blatt_ohne_axiomCall`, `Extraktion.lean`
    §17). This file cannot import `Extraktion` (`Extraktion.lean` imports
    this file), so no event characterization is restated or re-proved here:
    the frame (`Rahmen`) compares slots and globals only, never events, and
    the run side travels through the successor equations (`hM'l` names
    `neu`, `hM'w` names `σ'`). The trace linkage (`hneu`) and the scheduler
    side (`hkein_nimmt`) belong to the `GenSchritt.blatt` evidence and are
    consumed where `hReach'` is built, so the chain step takes neither; the
    per-step footprint checks (`hmark` / `hcar`) stay with the `PCSchritt`
    lifter (`Ziel.lean`: `pcSchritt_blatt_progAus_ohne_axiomCall` and its
    oracle sibling).

    Coverage (exactly): one single-thread step by a member thread for any
    fired statement -- every leaf included, oracle leaves included (their
    frame is the same `stmt_gut` derivation under the same bound `hO`) --
    with `SerialLink` guarded-vacuous at the new step exactly as for lock
    steps (a writer owes no witness under the guard).

    Remainder (booked, not hidden): iterating the step over a whole
    `PCReach` run -- replacing the `hlock` premise of
    `MaschinenKette.kette_aus_lauf_voll` with per-step frame wiring;
    non-vacuous `SerialLink` witnesses at `zugriff` events for writing
    steps; globals and multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The contract frame of a fired step.** From the firing data out of the
    thread world (`hstep` under `hΛ`) and the oracle bound (`hO`), the
    post-world keeps the statement contract's frame -- the `Rahmen` half of
    `stmt_gut` (`Satz.lean`), read directly. Every premise is load-bearing:
    each feeds `stmt_gut` or its application. -/
theorem blatt_rahmen_vertrag
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ') :
    Rahmen V.schreibt V.gschreibt (M.weltVon f) σ' := by
  exact ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ) σ' hstep).1

/-- **The code frame of a fired step (`blatt_rahmen_schritt`).** A fired
    step's memory movement satisfies the chain-step frame: the contract
    frame widened to the thread's code frame under the contract-to-code
    wiring. Every premise is load-bearing: the firing data feeds
    `blatt_rahmen_vertrag`, `code` types the wiring and the conclusion,
    `hW` / `hG` feed the widening. -/
theorem blatt_rahmen_schritt
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (code : Faden → D.Fn)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (code f) g = true) :
    Rahmen (D.schreibt (code f)) (D.gschreibt (code f)) (M.weltVon f) σ' := by
  exact (blatt_rahmen_vertrag O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep).weiter hW hG

/-- **The chain from the machine, one framed leaf step.** A chain tracking
    `M` extends along a fired framed step of a member thread: worlds and run
    by construction (`rfl`), order and goodness from the read-only
    projection theorems, ownership and declaration side from the
    single-thread run, the new frame from `blatt_rahmen_schritt` instead of
    memory preservation, `SerialLink` inherited plus guarded-vacuous at the
    new step. The step-level lift of the `hlock` exclusion: a framed fired
    leaf enters the chain induction. Every premise is load-bearing: the
    firing data and the wiring feed the new-step frame, `neu` types `hM'l`,
    the routing premises feed the mirrored construction. -/
theorem kette_aus_maschinenlauf_blatt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [σ'])
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hW : ∀ t, V.schreibt t = true → D.schreibt (J.code f) t = true)
    (hG : ∀ g, V.gschreibt g = true → D.gschreibt (J.code f) g = true)
    (hLink : ∀ t₀ : D.Tab, SerialLink Nb J M.lauf t₀)
    (hsingle : ∀ st ∈ M.lauf, st.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      (∀ t₀ : D.Tab, TraegerSchreibt (J.code f) (.inl t₀) = false →
        SerialLink Nb J' M'.lauf t₀) := by
  have hlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hReach
  have hLastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  have hfaden : ∀ (i : Nat) (g : Faden) (ei : Ereignis D),
      M'.lauf[i]? = some (Schritt.mk g ei) → g = f := by
    intro i g ei hi
    rw [hM'l] at hi
    by_cases hlt : i < M.lauf.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hsingle _ (List.mem_of_getElem? hi)
    · have hle : M.lauf.length ≤ i := by omega
      rw [List.getElem?_append_right hle] at hi
      exact (gen_eigen_getElem f neu _ _ _ hi).1
  have hGes' : Gesittet M'.lauf := by
    refine ⟨gen_konsistent P O passes hO sp M' hReach',
            gen_gut_obs P O passes hO sp M' hReach',
            gen_ausschluss P O passes hO sp M' hReach', ?_, ?_⟩
    · intro i j g1 g2 m s s' e1 e2 hi hj _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
    · intro i j g1 g2 o e1 e2 hi hj _ _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
  have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
    intro i j g1 g2 e1 e2 hi hj hne
    have h1 := hfaden i g1 e1 hi
    have h2 := hfaden j g2 e2 hj
    exact absurd (h1.trans h2.symm) hne
  have hKette' : M'.welten.length = (J.schrittFaden ++ [f]).length + 1 := by
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp
    omega
  have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach0 : World D),
      (J.schrittFaden ++ [f])[k]? = some g0 → M'.welten[k]? = some vor →
      M'.welten[k + 1]? = some nach0 →
      g0 ∈ J.faeden ∧
        Rahmen (D.schreibt (J.code g0)) (D.gschreibt (J.code g0)) vor nach0 := by
    intro k g0 vor nach0 hk hkv hkn
    rw [hM'w] at hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
        List.getElem?_append_left hlt
      rw [e1] at hk
      have hltM : k < M.welten.length := by omega
      have e2 : (M.welten ++ [σ'])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [σ'])[k + 1]? = M.welten[k + 1]? :=
        List.getElem?_append_left hltM1
      rw [e3] at hkn
      have hJkn : J.welten[k + 1]? = some nach0 := by rw [hJw]; exact hkn
      exact J.hSchritt k g0 vor nach0 hk hJkv hJkn
    · by_cases heq : k = J.schrittFaden.length
      · subst heq
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk
        have hg0 : g0 = f := (Option.some_inj.mp hk).symm
        have eW : (M.welten ++ [σ'])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [σ'])[J.schrittFaden.length + 1]? = some σ' := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : σ' = nach0 := Option.some_inj.mp hkn
        rw [hg0, hvor, ← hnach0]
        have hR := blatt_rahmen_schritt O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep
          J.code hW hG
        refine ⟨hmem, ?_, ?_⟩
        · intro t ht k2 fld
          exact hR.1 t ht k2 fld
        · intro g hg
          exact hR.2 g hg
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, ?_⟩
  intro t₀ hnw k0 g0 hk0 hwr
  have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
  have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
  by_cases hlt : k0 < J.schrittFaden.length
  · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk0'
    obtain ⟨j, w, Λ, h, hw⟩ := hLink t₀ k0 g0 hk0' hwr0
    have hjlt : j < M.lauf.length := by
      by_cases h : j < M.lauf.length
      · exact h
      · have hle : M.lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp at hw
    have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λ h)) := by
      rw [hM'l, List.getElem?_append_left hjlt]
      exact hw
    exact ⟨j, w, Λ, h, hw'⟩
  · by_cases heq : k0 = J.schrittFaden.length
    · subst heq
      have hg0 : g0 = f := by
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk0'
        exact (Option.some_inj.mp hk0').symm
      rw [hg0] at hwr
      have hwrF : TraegerSchreibt (J.code f) (.inl t₀) = true := hwr
      rw [hnw] at hwrF
      simp at hwrF
    · have hle : J.schrittFaden.length ≤ k0 := by omega
      have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk0'
      simp at hk0'

#print axioms Gabbro.Grammatik.blatt_rahmen_vertrag
#print axioms Gabbro.Grammatik.blatt_rahmen_schritt
#print axioms Gabbro.Grammatik.kette_aus_maschinenlauf_blatt

end Gabbro.Grammatik

/-! ## 19. The single-thread discharge for Einfaedig runs (`hsingle_aus_einfaedig`)

    The `hsingle` premises of §14 (`kette_aus_maschinenlauf_schritt`,
    `_nimmt`, `_gibt`) and §18 (`kette_aus_maschinenlauf_blatt`) narrow
    everything to single-thread runs: every run step is `f`'s. Inside those
    proofs `hsingle` is consumed for exactly two duties:

    - the ownership fields of `Gesittet M'.lauf` (`marke_eindeutig`, W4, and
      `ungeteilt`, W5), via `hfaden` arithmetic;
    - `BeschraenkteVerschraenkung Nb M'.lauf`, vacuously via the same
      arithmetic.

    What is proved (no `sorry`):

    - `hsingle_aus_einfaedig`: the first duty discharged for multi-thread
      runs. From reachability (`h`, which yields W1-W3 through the §11
      projection theorems), the `Einfaedig` projection (`hEin`, W4 through
      `marke_eindeutig_aus_einfaedig`, `Wettlauf.lean` §7), and the
      declaration side (`hungeteilt`, W5, the exact shape `gen_gesittet`
      takes), the run is `Gesittet` -- with no single-thread premise
      anywhere. Read-only reuse of `gen_gesittet` (§11): one positional
      application, no duplicated proof. Every premise is load-bearing: each
      feeds `gen_gesittet` positionally, so deleting any premise breaks
      elaboration. There is no `have _ :=` discard, no `sorry`/`admit`/
      `axiom`, and no bare `Prop` slot.

    Coverage (exactly): the `Gesittet` half of `hsingle`'s duties, for every
    generated reachable run whose threads satisfy `Einfaedig` plus the
    declaration side -- multi-thread Einfaedig runs included. The
    `.marke_eindeutig` and `.ungeteilt` projections of the conclusion are
    the literal shapes `hsingle` supplied at the §14/§18 use sites.

    Remainder (booked, not hidden): `BeschraenkteVerschraenkung` does not
    follow from `Einfaedig` plus the declaration side -- it constrains which
    thread pairs may share a run (`Nb`), and under `hsingle` it held
    vacuously only because no second thread had steps. Multi-thread use
    sites keep it as an explicit `Nb` declaration premise (or keep
    `hsingle`); the step theorems themselves are not restated here.
    `hsingle_prog` (the program side, `Extraktion.lean` counter routing)
    is untouched, as are `SerialLink` witnesses, globals, and
    multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The single-thread narrowing discharged for Einfaedig runs.** A
    generated reachable run whose threads satisfy `Einfaedig` (plus the
    declaration side) is `Gesittet`: W1-W3 are generated, W4 travels as the
    `Einfaedig` projection, W5 as the declaration side. This is the
    `Gesittet` half of what `hsingle` supplies at the §14/§18 use sites,
    now without any single-thread premise, so multi-thread Einfaedig runs
    are covered. Every premise is load-bearing: each is passed whole to
    `gen_gesittet`. -/
theorem hsingle_aus_einfaedig
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet M.lauf :=
  gen_gesittet P O passes hO sp M h code hEin hungeteilt

#print axioms Gabbro.Grammatik.hsingle_aus_einfaedig

end Gabbro.Grammatik

/-! ## 20. The spec triple from execution: one fired step extends the thread triple
    (`spec_aus_fuehrung_schritt`)

    The Owicki-Gries bind (`InterferenzAllgemein.lean` section 19: `SpecTriple`,
    `seqTriple_from_spec`, `stabil_from_spec`, consumed by `owickiGries_stabil`)
    posits each thread's triple over chain positions: `requiresEigen` and
    `ensuresEigen` quantify over indices `k` with `schrittFaden[k]? = some f`,
    with no link to the steps the machine actually fired. The sequential side
    exists (`stabil_from_spec`) and the execution side exists (PC runs,
    section 12: where each thread stands, firing through `PCSchritt`); nothing
    binds the triple to the executed steps of the interleaving.

    What is proved (no `sorry`):

    - `spec_aus_fuehrung_schritt`: one executed PC step extends the thread
      triple. A chain `J` tracks the machine `M` (`hJw`: the same worlds); the
      thread's triple holds on `J` (`hSpec`, the prefix -- at the seed this is
      head validity alone, since a zero-step chain carries no eigen
      obligation); one `PCSchritt` of `f` fires (`hs`: where the thread stands
      plus the firing data, read as a generated step through `pcSchritt_gen`);
      the extended chain `J'` continues the history by construction
      (`hJ'sf` / `hJ'w` / `hJ'code`, exactly what the section 14 / `blatt`
      constructions supply definitionally). Then the triple holds on `J'`.
      Old indices transfer through the prefix triple; the new index -- the
      fired step -- transfers through the firing itself. Leaf steps go
      through the per-firing contract preservation (`hBlatt`, the
      sequential-verification duty, now stated over firings with `hstep`
      evidence rather than over chain positions); lock steps (`nimmt` /
      `gibt`, the section boundaries of the section 21 grain) go through
      live-memory constancy plus memory-only contracts (`hMem`): a lock step
      keeps the memory, and contracts read only memory, so `Pre` / `Post`
      survive with no user logic owed.
      Every premise is load-bearing: `hReach` / `hO` / `sp` feed the
      last-world memory fact (`genWelten_letzte` through `pcReach_gen`); `hs`
      feeds `pcSchritt_gen`; `hJw` / `hJ'sf` / `hJ'w` / `hJ'code` rewrite every
      index; `hMem` bridges both step kinds; `hBlatt` closes the leaf case;
      `hSpec` closes the old indices and both heads. There is no `have _ :=`
      discard, no `sorry` / `admit` / `axiom`, and no bare `Prop` slot.

    Coverage (exactly): one executed `PCSchritt` (`leaf` / `nimmt` / `gibt`)
    by a tracked thread, extending a tracked chain. `Pre` holds along the
    thread's executed steps and `Post` at its section ends, in the uniform
    eigen shape that `owickiGries_stabil` consumes -- the indexing is executed
    (chain positions are machine firings, worlds are machine history), while
    the per-statement contract content stays where it belongs (below).

    Remainder (booked, not hidden): iterating the step over a whole `PCReach`
    run (the induction that carries a seed triple -- head validity from the
    caller -- to the final chain); the per-step atom identity inside `hs`
    (S12, the scheduler and witness duty: the counter points at the extracted
    atom); the `axiomCall` oracle-event contract (S13: the oracle answers with
    an arbitrary world, so `hBlatt` for oracle leaves is owed on arbitrary
    answers); discharging `hMem` for `QRequires` / `QEnsures` (the
    per-expression induction showing `eval` reads only slots and globals,
    downstream where the contract instantiation lives); head validity from
    thread entry (the caller side).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Memory-only contracts.** `Pre` / `Post` read only live memory (slots and
    globals), never the trace: worlds over the same memory agree. Contract
    shapes (`QRequires` / `QEnsures`) satisfy this because `eval` reads only
    slots and globals; the per-expression induction stays downstream, where
    the contract instantiation lives. -/
structure SpeicherVertrag (Pre Post : D.Fn → World D → Prop) (fn : D.Fn) : Prop where
  /-- The requires-side agrees on worlds over the same memory. -/
  memPre : ∀ σ σ' : World D, σ.speicher = σ'.speicher → (Pre fn σ ↔ Pre fn σ')
  /-- The ensures-side agrees on worlds over the same memory. -/
  memPost : ∀ σ σ' : World D, σ.speicher = σ'.speicher → (Post fn σ ↔ Post fn σ')

/-- A world built over a memory carries that memory. -/
theorem speicher_welt_speicher (s : Speicher D) (tr : List (Ereignis D)) :
    (s.welt tr).speicher = s := by
  cases s
  rfl

#print axioms Gabbro.Grammatik.speicher_welt_speicher

/-- **One executed step extends the thread triple.** Where a tracked chain
    meets one fired PC step of its thread, the spec triple transfers to the
    extended chain: old positions keep the prefix triple, the fired position
    keeps the contract through the firing (leaf steps through per-firing
    preservation, lock steps through memory constancy). This is the step that
    binds spec triples to interleaved execution, so that `owickiGries_stabil`
    consumes executed triples, not posited ones. -/
theorem spec_aus_fuehrung_schritt
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hReach : PCReach P O passes prog (GenStart sp) M pc)
    (hs : PCSchritt P O passes prog M pc f M' pc')
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (Pre Post : D.Fn → World D → Prop)
    (hMem : SpeicherVertrag Pre Post (J.code f))
    (hBlatt : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M.spuren f)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' →
      σ'.spur = neu ++ M.spuren f →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre (J.code f) (M.weltVon f) ↔ Pre (J.code f) σ') ∧
        (Post (J.code f) (M.weltVon f) ↔ Post (J.code f) σ'))
    (hSpec : SpecTriple Pre Post Nb J f)
    (J' : GemeinsamerLauf (D := D) Nb)
    (hJ'sf : J'.schrittFaden = J.schrittFaden ++ [f])
    (hJ'w : J'.welten = M'.welten)
    (hJ'code : J'.code f = J.code f) :
    SpecTriple Pre Post Nb J' f := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog (GenStart sp) M pc hReach
  have hGen : GenSchritt P O passes M f M' :=
    pcSchritt_gen P O passes prog M M' pc pc' f hs
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hG
  have hMlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  have hlastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  have hwf : (M.weltVon f).speicher = M.speicher :=
    speicher_welt_speicher M.speicher (M.spuren f)
  -- positions below the frontier read through the prefix triple
  have hPrefix : ∀ (W : List (World D)), J'.welten = M.welten ++ W →
      ∀ (k : Nat) (vor nach : World D),
      k < J.schrittFaden.length →
      J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
    intro W hW k vor nach hlt hkg hkv hkn
    have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
      List.getElem?_append_left hlt
    rw [hJ'sf] at hkg
    rw [e1] at hkg
    have hltM : k < M.welten.length := by omega
    have hltM1 : k + 1 < M.welten.length := by omega
    have e2 : (M.welten ++ W)[k]? = M.welten[k]? :=
      List.getElem?_append_left hltM
    have e3 : (M.welten ++ W)[k + 1]? = M.welten[k + 1]? :=
      List.getElem?_append_left hltM1
    rw [hW] at hkv hkn
    rw [e2] at hkv
    rw [e3] at hkn
    have hJkv : J.welten[k]? = some vor := by
      rw [hJw]
      exact hkv
    have hJkn : J.welten[k + 1]? = some nach := by
      rw [hJw]
      exact hkn
    rw [hJ'code]
    exact ⟨hSpec.requiresEigen k vor nach hkg hJkv hJkn,
      hSpec.ensuresEigen k vor nach hkg hJkv hJkn⟩
  -- the head reads through the prefix
  have hHead : ∀ (W : List (World D)), J'.welten = M.welten ++ W →
      ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → J.welten[0]? = some σ₀ := by
    intro W hW σ₀ h0
    have hne : 0 < M.welten.length := by omega
    have e0 : (M.welten ++ W)[0]? = M.welten[0]? :=
      List.getElem?_append_left hne
    rw [hW, e0] at h0
    rw [hJw]
    exact h0
  -- the frontier world carries live memory
  have hFront : ∀ (W : List (World D)), J'.welten = M.welten ++ W →
      ∀ vor : World D, J'.welten[J.schrittFaden.length]? = some vor →
        vor.speicher = M.speicher := by
    intro W hW vor hkv
    have hltNew : J.schrittFaden.length < M.welten.length := by omega
    have eW : (M.welten ++ W)[J.schrittFaden.length]? =
        M.welten[J.schrittFaden.length]? :=
      List.getElem?_append_left hltNew
    rw [hW, eW, hlastIdx] at hkv
    have hvor : vor = M.speicher.welt (M.spuren f0) :=
      Option.some_inj.mp hkv.symm
    rw [hvor]
    exact speicher_welt_speicher _ _
  -- beyond the frontier there is no step
  have hBeyond : ∀ (k : Nat), J.schrittFaden.length < k →
      J'.schrittFaden[k]? = some f → False := by
    intro k hlt hkg
    have hle : J.schrittFaden.length ≤ k := by omega
    have eNone : (J.schrittFaden ++ [f])[k]? = none := by
      rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
        List.length_singleton]
      omega
    rw [hJ'sf] at hkg
    rw [eNone] at hkg
    simp at hkg
  rcases hGen with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkein⟩ |
    ⟨L, _hself, _hrang, _hfrei⟩ | ⟨L, _hhaelt⟩
  · -- the fired leaf appends its outcome world
    have hW : J'.welten = M.welten ++ [σ'] := hJ'w
    have eW2 : (M.welten ++ [σ'])[J.schrittFaden.length + 1]? = some σ' := by
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2]
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub]
      rfl
    have hNew : ∀ (vor nach : World D),
        J'.welten[J.schrittFaden.length]? = some vor →
        J'.welten[J.schrittFaden.length + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro vor nach hkv hkn
      have hvs : vor.speicher = M.speicher := hFront [σ'] hW vor hkv
      have hnach : σ' = nach := by
        rw [hW, eW2] at hkn
        exact Option.some_inj.mp hkn
      have hPre : Pre (J.code f) vor ↔ Pre (J.code f) σ' :=
        (hMem.memPre vor (M.weltVon f) (hvs.trans hwf.symm)).trans
          (hBlatt V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein).1
      have hPost : Post (J.code f) vor ↔ Post (J.code f) σ' :=
        (hMem.memPost vor (M.weltVon f) (hvs.trans hwf.symm)).trans
          (hBlatt V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein).2
      rw [hJ'code, ← hnach]
      exact ⟨hPre, hPost⟩
    have hReqH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Pre (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.requiresHead σ₀ (hHead [σ'] hW σ₀ h0)
    have hEnsH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Post (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.ensuresHead σ₀ (hHead [σ'] hW σ₀ h0)
    have hReqE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix [σ'] hW k vor nach hlt hkg hkv hkn).1
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).1
        · exact (hBeyond k (by omega) hkg).elim
    have hEnsE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix [σ'] hW k vor nach hlt hkg hkv hkn).2
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).2
        · exact (hBeyond k (by omega) hkg).elim
    exact ⟨hReqH, hEnsH, hReqE, hEnsE⟩
  · -- the fired take keeps live memory: contracts survive with no user logic
    have hW : J'.welten =
        M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)] :=
      hJ'w
    have eW2 : (M.welten ++
        [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)])[J.schrittFaden.length + 1]? =
        some (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)) := by
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2]
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub]
      rfl
    have hNew : ∀ (vor nach : World D),
        J'.welten[J.schrittFaden.length]? = some vor →
        J'.welten[J.schrittFaden.length + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro vor nach hkv hkn
      have hvs : vor.speicher = M.speicher :=
        hFront _ hW vor hkv
      have hnach : M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) = nach := by
        rw [hW, eW2] at hkn
        exact Option.some_inj.mp hkn
      have hNs : (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)).speicher =
          M.speicher :=
        speicher_welt_speicher _ _
      have hBrPre : Pre (J.code f) vor ↔
          Pre (J.code f) (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)) :=
        hMem.memPre vor _ (hvs.trans hNs.symm)
      have hBrPost : Post (J.code f) vor ↔
          Post (J.code f) (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)) :=
        hMem.memPost vor _ (hvs.trans hNs.symm)
      rw [hJ'code, ← hnach]
      exact ⟨hBrPre, hBrPost⟩
    have hReqH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Pre (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.requiresHead σ₀ (hHead _ hW σ₀ h0)
    have hEnsH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Post (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.ensuresHead σ₀ (hHead _ hW σ₀ h0)
    have hReqE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).1
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).1
        · exact (hBeyond k (by omega) hkg).elim
    have hEnsE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).2
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).2
        · exact (hBeyond k (by omega) hkg).elim
    exact ⟨hReqH, hEnsH, hReqE, hEnsE⟩
  · -- the fired release keeps live memory: the section end keeps the contract
    have hW : J'.welten =
        M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)] :=
      hJ'w
    have eW2 : (M.welten ++
        [M.speicher.welt (Ereignis.gibt L :: M.spuren f)])[J.schrittFaden.length + 1]? =
        some (M.speicher.welt (Ereignis.gibt L :: M.spuren f)) := by
      have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
      rw [List.getElem?_append_right hle2]
      have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
      rw [hsub]
      rfl
    have hNew : ∀ (vor nach : World D),
        J'.welten[J.schrittFaden.length]? = some vor →
        J'.welten[J.schrittFaden.length + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro vor nach hkv hkn
      have hvs : vor.speicher = M.speicher :=
        hFront _ hW vor hkv
      have hnach : M.speicher.welt (Ereignis.gibt L :: M.spuren f) = nach := by
        rw [hW, eW2] at hkn
        exact Option.some_inj.mp hkn
      have hNs : (M.speicher.welt (Ereignis.gibt L :: M.spuren f)).speicher =
          M.speicher :=
        speicher_welt_speicher _ _
      have hBrPre : Pre (J.code f) vor ↔
          Pre (J.code f) (M.speicher.welt (Ereignis.gibt L :: M.spuren f)) :=
        hMem.memPre vor _ (hvs.trans hNs.symm)
      have hBrPost : Post (J.code f) vor ↔
          Post (J.code f) (M.speicher.welt (Ereignis.gibt L :: M.spuren f)) :=
        hMem.memPost vor _ (hvs.trans hNs.symm)
      rw [hJ'code, ← hnach]
      exact ⟨hBrPre, hBrPost⟩
    have hReqH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Pre (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.requiresHead σ₀ (hHead _ hW σ₀ h0)
    have hEnsH : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → Post (J'.code f) σ₀ := by
      intro σ₀ h0
      rw [hJ'code]
      exact hSpec.ensuresHead σ₀ (hHead _ hW σ₀ h0)
    have hReqE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).1
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).1
        · exact (hBeyond k (by omega) hkg).elim
    have hEnsE : ∀ (k : Nat) (vor nach : World D),
        J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach → (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
      intro k vor nach hkg hkv hkn
      by_cases hlt : k < J.schrittFaden.length
      · exact (hPrefix _ hW k vor nach hlt hkg hkv hkn).2
      · by_cases heq : k = J.schrittFaden.length
        · subst heq
          exact (hNew vor nach hkv hkn).2
        · exact (hBeyond k (by omega) hkg).elim
    exact ⟨hReqH, hEnsH, hReqE, hEnsE⟩

#print axioms Gabbro.Grammatik.spec_aus_fuehrung_schritt

end Gabbro.Grammatik

/-! ## 21. The spec triple from execution: whole-run induction (`spec_aus_lauf_voll`)

    `spec_aus_fuehrung_schritt` (§20) extends one thread triple over one fired
    PC step; `owickiGries_stabil` (consumed via `stabil_from_spec`, §19 of
    `InterferenzAllgemein.lean`) needs triples over the FINAL chain. This
    section is the induction between them: a seed triple (head validity from
    the caller -- a zero-step chain carries no eigen obligation) carried over
    a whole `PCReach` run to the final chain.

    What is proved (no `sorry`):

    - `PCSpur`: the thread trace of a run -- `tr` lists the acting thread of
      every machine step, in order. Each `schritt` case carries its own
      `PCReach` evidence `h` and firing `hs`, so a spur determines the run it
      traces; `pcSpur_von_reach` shows every `PCReach` derivation has one.
      The main induction runs over the spur (not over `PCReach` directly),
      because the chain equations (`J.schrittFaden = tr`) must follow the
      acting threads step by step, and a machine state alone does not record
      how many run events each step contributed.
    - `spec_aus_fuehrung_fremd`: a foreign step preserves the thread triple.
      Where the tracked chain meets one fired PC step of a DIFFERENT thread
      (`hne`), the spec triple of `f` transfers to the extended chain with no
      sequential duty owed: old positions keep the prefix triple, the new
      position holds the other thread, heads transfer through the world
      prefix. No `hBlatt`, no `hMem`, no reachability -- the firing `hs`
      supplies only the world-history shape (`M'.welten = M.welten ++ [w]`).
    - `spec_aus_lauf_voll`: the run induction for one thread `f`. Seed heads
      plus a uniform per-firing preservation duty (`hBlattAll`, over every
      reachable intermediate machine) plus memory-only contracts (`hMem`)
      give the triple on every chain `J` that tracks the run end
      (`J.welten = M.welten`, `J.schrittFaden = tr`, stable code
      `J.code f = fn`). The seed case is head validity with vacuous eigen
      obligations; each step splits the final chain into its prefix (same
      members, code, and run -- only worlds and step list restricted, so no
      `Gesittet` work is owed) and either extends through the firing
      (`spec_aus_fuehrung_schritt`, own step) or persists
      (`spec_aus_fuehrung_fremd`, foreign step). The top-level `PCReach`
      derivation is not a premise: the spur already carries per-step
      reachability evidence, and `pcSpur_von_reach` bridges callers that hold
      only the derivation.
    - `stabil_aus_lauf`: the consumer corollary. Per-thread run triples feed
      `stabil_from_spec` (read-only reuse -- that file is not touched), whose
      one-line application closes executed contract assertions at the last
      world. `hInv` / `hDeck` / `hAb` / `hFree` keep their exact §19 shapes.

    Coverage (exactly): whole `PCReach` runs (`leaf` / `nimmt` / `gibt`
    steps, any interleaving), one thread triple per induction instance, all
    threads jointly at the consumer. Every premise is load-bearing (each is
    consumed by its proof; there is no `have _ :=` discard).

    Remainder (booked, not hidden): the per-step atom identity inside `hs`
    (S12, scheduler and witness duty); the `axiomCall` oracle-event contract
    (S13); discharging `hMem` for `QRequires` / `QEnsures` (per-expression
    induction downstream, where the contract instantiation lives); head
    validity from thread entry (caller side); discharging `hFree` per program
    (the Owicki-Gries check itself, verifier duty).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Thread trace of a PC run.** `tr` lists the acting thread of every
    machine step, in order: empty at the start, one entry per fired step.
    Each step case carries its `PCReach` evidence and firing, so the spur
    determines the traced run. -/
inductive PCSpur (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) :
    GenMaschine D → PCStand → List Faden → Prop where
  | leer : PCSpur P O passes prog M0 M0 (fun _ => 0) []
  | schritt (M M' : GenMaschine D) (pc pc' : PCStand) (g : Faden)
      (h : PCReach P O passes prog M0 M pc)
      (hs : PCSchritt P O passes prog M pc g M' pc')
      (tr : List Faden) (htr : PCSpur P O passes prog M0 M pc tr) :
      PCSpur P O passes prog M0 M' pc' (tr ++ [g])

/-- **Every reachable run has a thread trace.** By induction on the
    derivation: empty at the start, one entry per fired step. This bridges
    callers that hold only the `PCReach` derivation to the spur induction. -/
theorem pcSpur_von_reach (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc) :
    ∃ tr : List Faden, PCSpur P O passes prog M0 M pc tr := by
  induction h with
  | start => exact ⟨[], PCSpur.leer⟩
  | step M M' pc pc' g h hs ih =>
      obtain ⟨tr, htr⟩ := ih
      exact ⟨tr ++ [g], PCSpur.schritt M M' pc pc' g h hs tr htr⟩

#print axioms Gabbro.Grammatik.pcSpur_von_reach

/-- **A foreign step preserves the thread triple.** Where a tracked chain
    meets one fired PC step of a different thread, the spec triple of `f`
    transfers to the extended chain: old positions keep the prefix triple,
    the fired position holds the other thread (so `f` owes nothing there),
    heads transfer through the world prefix. No per-firing preservation and
    no memory constancy are owed -- the firing supplies only the
    world-history shape. -/
theorem spec_aus_fuehrung_fremd
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D)
    (M M' : GenMaschine D) (pc pc' : PCStand) (g f : Faden)
    (hs : PCSchritt P O passes prog M pc g M' pc')
    (hne : g ≠ f)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (Pre Post : D.Fn → World D → Prop)
    (hSpec : SpecTriple Pre Post Nb J f)
    (J' : GemeinsamerLauf (D := D) Nb)
    (hJ'sf : J'.schrittFaden = J.schrittFaden ++ [g])
    (hJ'w : J'.welten = M'.welten)
    (hJ'code : J'.code f = J.code f) :
    SpecTriple Pre Post Nb J' f := by
  have hGen : GenSchritt P O passes M g M' :=
    pcSchritt_gen P O passes prog M M' pc pc' g hs
  have hAppend : ∃ w : World D, M'.welten = M.welten ++ [w] := by
    rcases hGen with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkein⟩ |
      ⟨L, _hself, _hrang, _hfrei⟩ | ⟨L, _hhaelt⟩
    · exact ⟨σ', rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, hMw⟩ := hAppend
  have hW : J'.welten = M.welten ++ [w] := by
    rw [hJ'w, hMw]
  have hMlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  -- positions below the frontier read through the prefix triple
  have hPrefix : ∀ (k : Nat) (vor nach : World D),
      k < J.schrittFaden.length →
      J'.schrittFaden[k]? = some f → J'.welten[k]? = some vor →
        J'.welten[k + 1]? = some nach →
        (Pre (J'.code f) vor ↔ Pre (J'.code f) nach) ∧
          (Post (J'.code f) vor ↔ Post (J'.code f) nach) := by
    intro k vor nach hlt hkg hkv hkn
    have e1 : (J.schrittFaden ++ [g])[k]? = J.schrittFaden[k]? :=
      List.getElem?_append_left hlt
    rw [hJ'sf] at hkg
    rw [e1] at hkg
    have hltM : k < M.welten.length := by omega
    have hltM1 : k + 1 < M.welten.length := by omega
    have e2 : (M.welten ++ [w])[k]? = M.welten[k]? :=
      List.getElem?_append_left hltM
    have e3 : (M.welten ++ [w])[k + 1]? = M.welten[k + 1]? :=
      List.getElem?_append_left hltM1
    rw [hW] at hkv hkn
    rw [e2] at hkv
    rw [e3] at hkn
    have hJkv : J.welten[k]? = some vor := by
      rw [hJw]
      exact hkv
    have hJkn : J.welten[k + 1]? = some nach := by
      rw [hJw]
      exact hkn
    rw [hJ'code]
    exact ⟨hSpec.requiresEigen k vor nach hkg hJkv hJkn,
      hSpec.ensuresEigen k vor nach hkg hJkv hJkn⟩
  -- the head reads through the prefix
  have hHead : ∀ σ₀ : World D, J'.welten[0]? = some σ₀ → J.welten[0]? = some σ₀ := by
    intro σ₀ h0
    have hne0 : 0 < M.welten.length := by omega
    have e0 : (M.welten ++ [w])[0]? = M.welten[0]? :=
      List.getElem?_append_left hne0
    rw [hW, e0] at h0
    rw [hJw]
    exact h0
  -- at and beyond the frontier there is no step of `f`: the new position
  -- holds the other thread, later positions hold none
  have hNew : ∀ (k : Nat), J.schrittFaden.length ≤ k →
      J'.schrittFaden[k]? = some f → False := by
    intro k hle hkg
    by_cases heq : k = J.schrittFaden.length
    · subst heq
      have eNew : (J.schrittFaden ++ [g])[J.schrittFaden.length]? = some g := by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hJ'sf, eNew] at hkg
      exact hne (Option.some_inj.mp hkg)
    · have hlt : J.schrittFaden.length < k := by omega
      have eNone : (J.schrittFaden ++ [g])[k]? = none := by
        rw [List.getElem?_append_right (by omega : J.schrittFaden.length ≤ k),
          List.getElem?_eq_none_iff, List.length_singleton]
        omega
      rw [hJ'sf, eNone] at hkg
      simp at hkg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ₀ h0
    rw [hJ'code]
    exact hSpec.requiresHead σ₀ (hHead σ₀ h0)
  · intro σ₀ h0
    rw [hJ'code]
    exact hSpec.ensuresHead σ₀ (hHead σ₀ h0)
  · intro k vor nach hkg hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · exact (hPrefix k vor nach hlt hkg hkv hkn).1
    · exact (hNew k (by omega) hkg).elim
  · intro k vor nach hkg hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · exact (hPrefix k vor nach hlt hkg hkv hkn).2
    · exact (hNew k (by omega) hkg).elim

#print axioms Gabbro.Grammatik.spec_aus_fuehrung_fremd

/-- **The whole-run induction: seed triple to final chain.** For one thread
    `f`, seed heads plus a uniform per-firing preservation duty (over every
    reachable intermediate machine) plus memory-only contracts give the spec
    triple on every chain that tracks the run end. Induction is over the
    thread trace: the seed case is head validity with vacuous eigen
    obligations; each step restricts the final chain to its prefix (same
    members, code, and run -- only worlds and step list move) and either
    extends through the firing (own step, `spec_aus_fuehrung_schritt`) or
    persists (foreign step, `spec_aus_fuehrung_fremd`). -/
theorem spec_aus_lauf_voll
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (f : Faden) (fn : D.Fn)
    (Nb : Nebeneinander)
    (Pre Post : D.Fn → World D → Prop)
    (hMem : SpeicherVertrag Pre Post fn)
    (hSeedPre : ∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Pre fn σ₀)
    (hSeedPost : ∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Post fn σ₀)
    (hBlattAll : ∀ (M₀ : GenMaschine D) (pc₀ : PCStand),
      PCReach P O passes prog (GenStart sp) M₀ pc₀ →
      ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren f)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M₀.weltVon f) ρ).welt = some σ' →
      σ'.spur = neu ++ M₀.spuren f →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre fn (M₀.weltVon f) ↔ Pre fn σ') ∧
        (Post fn (M₀.weltVon f) ↔ Post fn σ'))
    (M : GenMaschine D) (pc : PCStand) (tr : List Faden)
    (htr : PCSpur P O passes prog (GenStart sp) M pc tr)
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hJsf : J.schrittFaden = tr)
    (hJcode : J.code f = fn) :
    SpecTriple Pre Post Nb J f := by
  revert hJcode hJsf hJw J
  induction htr with
  | leer =>
      intro J hJw hJsf hJcode
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro σ₀ h0
        rw [hJcode]
        exact hSeedPre σ₀ (by rw [← hJw]; exact h0)
      · intro σ₀ h0
        rw [hJcode]
        exact hSeedPost σ₀ (by rw [← hJw]; exact h0)
      · intro k vor nach hkg _ _
        rw [hJsf] at hkg
        simp at hkg
      · intro k vor nach hkg _ _
        rw [hJsf] at hkg
        simp at hkg
  | schritt M M' pc pc' g h hs tr htr ih =>
      intro J' hJ'w hJ'sf hJ'code
      have hGen : GenSchritt P O passes M g M' :=
        pcSchritt_gen P O passes prog M M' pc pc' g hs
      have hMlen' : M'.welten.length = (tr ++ [g]).length + 1 := by
        have hK := J'.hKette
        rw [hJ'sf, hJ'w] at hK
        exact hK
      have hAppend : ∃ w : World D, M'.welten = M.welten ++ [w] := by
        rcases hGen with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkein⟩ |
          ⟨L, _hself, _hrang, _hfrei⟩ | ⟨L, _hhaelt⟩
        · exact ⟨σ', rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨w, hMw⟩ := hAppend
      have hPreLen : M.welten.length = tr.length + 1 := by
        have h1 := hMlen'
        rw [hMw] at h1
        simp only [List.length_append, List.length_singleton] at h1 ⊢
        omega
      -- the prefix chain: same members, code, and run, restricted worlds
      -- and step list (no `Gesittet` work is owed, the run is kept whole)
      have hSchrittP : ∀ (k : Nat) (f' : Faden) (vor nach : World D),
          tr[k]? = some f' → M.welten[k]? = some vor → M.welten[k + 1]? = some nach →
          f' ∈ J'.faeden ∧ Rahmen (D.schreibt (J'.code f')) (D.gschreibt (J'.code f')) vor nach := by
        intro k f' vor nach hkg hkv hkn
        have hlt : k < tr.length := by
          by_cases hle : tr.length ≤ k
          · rw [List.getElem?_eq_none hle] at hkg
            simp at hkg
          · omega
        have hltM : k < M.welten.length := by omega
        have hltM1 : k + 1 < M.welten.length := by omega
        have e1 : (tr ++ [g])[k]? = tr[k]? :=
          List.getElem?_append_left hlt
        have e2 : (M.welten ++ [w])[k]? = M.welten[k]? :=
          List.getElem?_append_left hltM
        have e3 : (M.welten ++ [w])[k + 1]? = M.welten[k + 1]? :=
          List.getElem?_append_left hltM1
        have hkg' : J'.schrittFaden[k]? = some f' := by
          rw [hJ'sf, e1]
          exact hkg
        have hkv' : J'.welten[k]? = some vor := by
          rw [hJ'w, hMw, e2]
          exact hkv
        have hkn' : J'.welten[k + 1]? = some nach := by
          rw [hJ'w, hMw, e3]
          exact hkn
        exact J'.hSchritt k f' vor nach hkg' hkv' hkn'
      let Jpre : GemeinsamerLauf (D := D) Nb :=
        { faeden := J'.faeden, code := J'.code, eintritt := J'.eintritt,
          welten := M.welten, schrittFaden := tr, l := J'.l,
          hKette := hPreLen, hSchritt := hSchrittP, hPaar := J'.hPaar,
          hGesittet := J'.hGesittet, hBeschraenkt := J'.hBeschraenkt,
          hEintritt := J'.hEintritt, hSchuld := J'.hSchuld,
          hInvSicht := J'.hInvSicht }
      have hJprew : Jpre.welten = M.welten := rfl
      have hJpresf : Jpre.schrittFaden = tr := rfl
      have hJprecode : Jpre.code f = fn := hJ'code
      have hSpecPre : SpecTriple Pre Post Nb Jpre f :=
        ih Jpre hJprew hJpresf hJprecode
      have hCodePre : J'.code f = Jpre.code f :=
        hJ'code.trans hJprecode.symm
      by_cases heq : g = f
      · subst g
        have hMemPre : SpeicherVertrag Pre Post (Jpre.code f) := by
          rw [hJprecode]
          exact hMem
        have hBlattPre : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
            (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
            s.istBlatt = true → HeldGenau Λ (offen (M.spuren f)) →
            ∀ (σ' : World D) (neu : List (Ereignis D)),
            (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' →
            σ'.spur = neu ++ M.spuren f →
            (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
            (Pre (Jpre.code f) (M.weltVon f) ↔ Pre (Jpre.code f) σ') ∧
              (Post (Jpre.code f) (M.weltVon f) ↔ Post (Jpre.code f) σ') := by
          intro V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein
          rw [hJprecode]
          exact hBlattAll M pc h V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein
        have hExt : J'.schrittFaden = Jpre.schrittFaden ++ [f] := hJ'sf
        exact spec_aus_fuehrung_schritt P O passes hO prog sp M _ pc pc' f h hs Nb Jpre
          hJprew Pre Post hMemPre hBlattPre hSpecPre J' hExt hJ'w hCodePre
      · have hExt : J'.schrittFaden = Jpre.schrittFaden ++ [g] := hJ'sf
        exact spec_aus_fuehrung_fremd P O passes prog M _ pc pc' g f hs heq Nb Jpre
          hJprew Pre Post hSpecPre J' hExt hJ'w hCodePre

#print axioms Gabbro.Grammatik.spec_aus_lauf_voll

/-- **Executed triples feed stability.** Per-thread run triples (from
    `spec_aus_lauf_voll`, one instance per member thread) supply the
    sequential premise of `stabil_from_spec` -- read-only reuse with exact
    §19 premise shapes (`hInv` / `hDeck` / `hAb` / `hFree` untouched, that
    file not edited) -- whose one-line application closes executed contract
    assertions at the last world. -/
theorem stabil_aus_lauf
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (M : GenMaschine D) (pc : PCStand)
    (tr : List Faden)
    (htr : PCSpur P O passes prog (GenStart sp) M pc tr)
    (hJw : J.welten = M.welten)
    (hJsf : J.schrittFaden = tr)
    (Pre Post : D.Fn → World D → Prop)
    (I : TraegerInv (D := D))
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hMemAll : ∀ (g : Faden), g ∈ J.faeden → SpeicherVertrag Pre Post (J.code g))
    (hSeedAll : ∀ (g : Faden), g ∈ J.faeden →
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Pre (J.code g) σ₀) ∧
      (∀ σ₀ : World D, (GenStart sp).welten[0]? = some σ₀ → Post (J.code g) σ₀))
    (hBlattAll : ∀ (g : Faden), g ∈ J.faeden → ∀ (M₀ : GenMaschine D) (pc₀ : PCStand),
      PCReach P O passes prog (GenStart sp) M₀ pc₀ →
      ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren g)) →
      ∀ (σ' : World D) (neu : List (Ereignis D)),
      (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ' →
      σ'.spur = neu ++ M₀.spuren g →
      (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) →
      (Pre (J.code g) (M₀.weltVon g) ↔ Pre (J.code g) σ') ∧
        (Post (J.code g) (M₀.weltVon g) ↔ Post (J.code g) σ'))
    (hFree : InterferenceFree Nb J (SpecQ Pre Post Nb J)) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ := by
  have hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f := by
    intro f hf
    exact spec_aus_lauf_voll P O passes hO prog sp f (J.code f) Nb Pre Post
      (hMemAll f hf) (hSeedAll f hf).1 (hSeedAll f hf).2
      (hBlattAll f hf) M pc tr htr J hJw hJsf rfl
  exact stabil_from_spec Nb J I Pre Post hInv hDeck hAb hSpec hFree

#print axioms Gabbro.Grammatik.stabil_aus_lauf

end Gabbro.Grammatik

/-! ## 22. The execution link, memory-preserving fragment
    (`hBlattAll_speicherfest_aus_feuerung`)

    BEFUND (rank HOCH, two checkers): `hBlattAll` per leaf (execution link) is
    open -- the uniform per-firing preservation over every reachable
    intermediate machine (the `spec_aus_lauf_voll` / `stabil_aus_lauf` premise,
    re-exported by the goal variant `ziel_nutzer_last_aus_pc_stabil`) has no
    discharger.

    What is proved (no `sorry`):

    - `Stmt.speicherfest`: the memory-preserving leaf test. The nine leaves
      whose every `some`-valued `execStmt` outcome keeps `speicher` (slots and
      globals) test true: `assignVar` and `regSchreib` (read into the
      environment / the device, trace grows, memory stands), `transition`
      (device mirror step, the world passes through untouched), `advances`
      and `retires` (mark bookkeeping, `.ok` on the input world), `ret`
      (reads only, `.zurueck` on the read world), `retGrund`, `leave`, `next`
      (pass-through outcomes on the input world). Everything else tests false:
      the four writes (`assignSlot`, `assignDurch`, `assignGlob`,
      `schreibBytes`), the conditional write (`uebergang`), the oracle answer
      (`axiomCall`), the global publish (`publish`), and all eleven compounds.
    - `speicherfest_speicher`: firing evidence for a `speicherfest` leaf keeps
      live memory. Case analysis on the statement: excluded shapes die at the
      test (`simp [Stmt.speicherfest] at hFest`); the nine included shapes
      compute through `execStmt` / `Ausgang.welt` / `Option.some.injEq` to a
      read-only or unchanged world, whose `speicher` is the input's by
      construction (`lese` / `merke` extend only the trace, §6).
    - `hBlattAll_speicherfest_aus_feuerung`: the `hBlattAll` conclusion for the
      memory-preserving fragment, uniformly over every intermediate machine,
      from firing evidence (`hstep`) plus memory-only contracts (`hMem`):
      memory constancy bridges both the `Pre` and the `Post` iff. No
      reachability is owed -- a pure `execStmt` fact holds at every machine,
      reachable or not, so the uniform shape is the easy direction: each
      `hBlattAll` application site whose fired leaf tests `speicherfest`
      discharges through this theorem instead of a posit.

    Coverage (exactly): the nine memory-preserving leaf shapes, every thread,
    every intermediate machine. Every premise is load-bearing: `O` / `passes`
    feed the firing in `hstep`; `Pre` / `Post` / `fn` name the conclusion;
    `hMem` bridges both iffs; `M₀` / `g` supply the two worlds; `s` / `ρ` /
    `hFest` select the fragment and compute; `σ'` / `hstep` carry the firing.
    Deleting any premise breaks elaboration. There is no `have _ :=`
    discard, no `sorry` / `admit` / `axiom`, and no bare `Prop` slot.

    Remainder (booked, not hidden): the seven memory-changing / oracle leaves
    (`assignSlot`, `assignDurch`, `assignGlob`, `schreibBytes`, `uebergang`,
    `axiomCall`, `publish`) stay owed per program and contract -- the
    sequential-verification duty. The full `hBlattAll` over abstract
    `Pre` / `Post` (which takes no memory hypothesis) is unprovable, not
    merely unproved: a writing leaf can break an arbitrary memory predicate,
    so no induction over `PCSpur` can conjure it. The step lemma's universal
    `hBlatt` premise still owes those seven leaves; `axiomCall` stays with
    S13 (arbitrary oracle answers); the `hMem` discharge per contract and
    head validity from thread entry stay where §21 books them.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Memory-preserving leaves.** The nine leaves whose every `some`-valued
    `execStmt` outcome keeps `speicher`: reads and pass-through outcomes only,
    never a slot / global write and never an oracle answer. -/
def Stmt.speicherfest : Stmt D V l Γ Λ Λ' → Bool
  | .assignVar _ _ => true
  | .regSchreib _ _ _ => true
  | .transition _ _ _ _ _ _ _ => true
  | .advances _ _ _ _ => true
  | .retires _ _ _ _ => true
  | .ret _ _ => true
  | .retGrund _ _ => true
  | .leave _ => true
  | .next _ => true
  | _ => false

/-- **Firing a memory-preserving leaf keeps live memory.** From the firing
    evidence alone: excluded shapes die at the `speicherfest` test, the nine
    included shapes compute to a read-only or unchanged world. -/
theorem speicherfest_speicher
    (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hFest : s.speicherfest = true)
    (σ σ' : World D)
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ') :
    σ'.speicher = σ.speicher := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignDurch p t ht f i e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignGlob g e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp [Stmt.speicherfest] at hFest
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | uebergang t f hτ i von nach hn he hw hL =>
      simp [Stmt.speicherfest] at hFest
  | ite c t e =>
      simp [Stmt.speicherfest] at hFest
  | onOption o p a =>
      simp [Stmt.speicherfest] at hFest
  | onTag v arms =>
      simp [Stmt.speicherfest] at hFest
  | onGrund r arms =>
      simp [Stmt.speicherfest] at hFest
  | call f args hp hr =>
      simp [Stmt.speicherfest] at hFest
  | callInd p args hp hr =>
      simp [Stmt.speicherfest] at hFest
  | locks L hr body =>
      simp [Stmt.speicherfest] at hFest
  | breaking i body =>
      simp [Stmt.speicherfest] at hFest
  | traverse t inv body =>
      simp [Stmt.speicherfest] at hFest
  | retry n bis body ueberlauf =>
      simp [Stmt.speicherfest] at hFest
  | forever a inv body =>
      simp [Stmt.speicherfest] at hFest
  | axiomCall a args h hw hg =>
      simp [Stmt.speicherfest] at hFest
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | publish g e payload hp hw hL =>
      simp [Stmt.speicherfest] at hFest
  | advances m a h hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retires m s h a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | ret e hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retGrund r hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | leave h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | next h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl

#print axioms Gabbro.Grammatik.speicherfest_speicher

/-- **Per-firing preservation for memory-preserving leaves, uniformly over
    every intermediate machine.** The `hBlattAll` conclusion for the
    `speicherfest` fragment, from firing evidence plus memory-only contracts:
    the fired leaf keeps live memory (`speicherfest_speicher`), and contracts
    read only live memory (`hMem`), so `Pre` / `Post` survive with no user
    logic owed. -/
theorem hBlattAll_speicherfest_aus_feuerung
    (O : Orakel D) (passes : Nat)
    (Pre Post : D.Fn → World D → Prop) (fn : D.Fn)
    (hMem : SpeicherVertrag Pre Post fn)
    (M₀ : GenMaschine D) (g : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hFest : s.speicherfest = true)
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ') :
    (Pre fn (M₀.weltVon g) ↔ Pre fn σ') ∧ (Post fn (M₀.weltVon g) ↔ Post fn σ') := by
  have hspeicher : σ'.speicher = (M₀.weltVon g).speicher :=
    speicherfest_speicher O passes V l Γ Λ Λ' s ρ hFest _ _ hstep
  exact ⟨hMem.memPre _ _ hspeicher.symm, hMem.memPost _ _ hspeicher.symm⟩

#print axioms Gabbro.Grammatik.hBlattAll_speicherfest_aus_feuerung

end Gabbro.Grammatik

