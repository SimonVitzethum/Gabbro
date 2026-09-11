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

  Remainder (booked, not hidden): thread programs are over-approximated (any
  leaf any time -- no program counters or continuations yet), so W4 needs the
  `Einfaedig` projection as premise and W5 the declaration side; full
  program-counter generation is the open lane.
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

end Gabbro.Grammatik
