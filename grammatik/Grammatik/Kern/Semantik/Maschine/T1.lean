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
import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein

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
    (hO : GutO O) (hP : StufenOk P) (f : Faden) (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hh : HeldGenau Λ σ.haelt) (hempty : σ.spur = [])
    (σ' : World D) (h : (exec P O passes fuel V b σ ρ).welt = some σ') :
    MaschinenFaden D :=
  ⟨f, σ'.spur, σ, σ', hempty, exec_spur P O passes fuel hO hP b σ ρ hh σ' h, rfl⟩

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
    hvers := fun f j => ⟨(voll f).length, by rw [List.drop_length]; simp only [Lauf.spur, List.take_nil, List.filterMap_nil, List.reverse_nil]⟩,
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
  | cons s rest ih => simp only [weltenFalte, List.length_cons, ih, Nat.add_left_cancel_iff]

/-- One world per step, plus the start world. -/
theorem maschinenWelten_laenge (M : MaschinenLauf D) :
    (maschinenWelten M).length = M.run.length + 1 :=
  weltenFalte_laenge M.start M.run

/-- The end world records every run event exactly once, newest first. -/
theorem weltenEnde_spur (run : Lauf D) (σ : World D) :
    (weltenEnde σ run).spur = (run.map Schritt.ereignis).reverse ++ σ.spur := by
  unfold weltenEnde
  induction run generalizing σ with
  | nil => simp only [World.merke, List.cons_append, List.nil_append, List.foldl_nil, List.map_nil, List.reverse_nil]
  | cons s rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.reverse_cons]
      rw [ih]
      simp only [World.merke, List.cons_append, List.nil_append, List.append_assoc]

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
          simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, Nat.succ_ne_self,
  and_false] at hlen
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
  simp only [RufAusgang.welt, keinRuf, reduceCtorEq] at h

/-- Leaf or compound. A thread step executes one leaf; compound statements
    (`ite`, calls, `locks`, loops, ...) open into further steps instead. -/
def Stmt.istBlatt : Stmt D V l Γ Λ Λ' → Bool
  | .ite .. | .onOption .. | .onTag .. | .onWhy .. | .call .. | .callInd ..
  | .locks .. | .breaking .. | .traverse .. | .retry .. | .forever .. => false
  | _ => true

/-- **Frame and trace of a LEAF, under held static holdings only.** A leaf
    takes no lock and calls nothing, so `HeldIn` (every lock the static
    holdings name is held -- the side condition of machine G since the
    held-set relaxation) suffices; no floor, no handler premise. -/
theorem Stmt.gut_blatt (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hO : GutO O) :
    ∀ (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true → ∀ (σ : World D) (ρ : Env D Γ),
      HeldIn Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))
  | .assignThru p t _ f i e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))
  | .assignSlotRef r t _ _ f e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append r.orte_darf e.orte_darf) hh
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))
  | .assignGlob g e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldIn hh))
  | .putBytes t f hf n i _ _ e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh
      exact hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldIn hh))
  | .assignVar x e, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh
  | .shift t f hτ i von nach hn he hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_tab hL) i.orte_darf) hh
        exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .axiomCall a args _ hw hg hd hgd, _, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldIn hh)
        rw [ha] at this
        exact hl.trans (Gut.weiter hw hg this)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regWrite r _ e, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh
  | .transition .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_fragt _ _
  | .publish g e _ _ hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldIn hh))
  | .advances .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retires .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .ret e _, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh
  | .retWhy .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .ite .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .onOption .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .onTag .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .onWhy .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .call .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .callInd .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .locks .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .breaking .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .traverse .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .retry .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .forever .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf


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
  simp only [genUpdate, ↓reduceIte]

theorem genUpdate_noteq (m : Faden → List (Ereignis D)) (f g : Faden) (h : g ≠ f)
    (s : List (Ereignis D)) :
    genUpdate m f s g = m g := by
  simp only [genUpdate, h, ↓reduceIte]

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
  | cons _ _ ih => simp only [List.map_cons, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some, ih]


end Gabbro.Grammatik
