/-
  File:      Grammatik/Zielsatz/Akzeptiert.lean
  Subject:   PLAN-ZIELSATZ.md step 3 -- what the CHECKER decides, as ONE Bool
             (`Akzeptiert`), and what the START must meet, as one Prop
             (`StartZulaessig`) with a Bool for finite start tables
             (`startB`).

  `Akzeptiert P S fs ls ws` is the conjunction of every premise of the
  flagship theorems that is a decidable fact about the PROGRAM:

  | component      | Bool                   | Prop it decides (`AkzeptiertP`)                     | used by |
  |----------------|------------------------|-----------------------------------------------------|---------|
  | `frag`         | `programmImFragmentG`  | the same Bool                                       | `hFrag` of `ziel_ort_mehrfaden_ende` |
  | `abg`          | `abgAlleB`             | `∀ w, AbgK P fs (reachB P fs w)`                    | `hAbg` (with `K t := reachB P fs (init t).1`) |
  | `fuss`         | `fussWB`               | `∀ f, FussS P S (getrenntW P fs ws) f`              | `hFuss` (with `StartPasst`) |
  | `stufen`       | `stufenB`              | `StufenM P`                                         | `hSt` of `keine_verklemmungG` |
  | `sperrOrte`    | `sperrOrteB`           | `∀ L c, c ∈ S.orte L → Bewacht c L`                 | first half of `hS : SperrInvOk S` |
  | `wurzeln`      | `wurzelnB`             | `∀ w ∈ ws, D.haelt w = []`                          | `hLeer` / `hex` (with `StartPasst`) |
  | `zeit`         | `zeitB`                | `∀ g, rufTief P (fs.length + 1) g = true`           | `hadm` of `frame_schritte_beschraenkt` (n := fs.length) |

  `akzeptiert_iff`: the Bool is EXACTLY the Prop `AkzeptiertP` (both
  directions), given the member lists are complete.

  **Two arguments beyond the plan's `Akzeptiert P S fs`, and why:**
  * `ls : List D.Lock` -- the lock member list. `SperrInvOk`'s first half
    quantifies over every lock, and `D.Lock` carries no enumeration; the
    deadlock theorem needs the same list anyway (`hls`).
  * `ws : List D.Fn` -- the program's DECLARED THREAD STARTS (the checker's
    `concurrent { … }` members and `entry`/`boot` dispatch roots,
    `crates/gabbro-check/src/startexklusiv.rs`). Whether a carrier is
    thread-local depends on which functions start threads: `hauptA` may
    write its private table unguarded only because no second thread runs
    `hauptA` or anything that writes it. `Programm D` has no field for the
    starts, so the list is an argument; the call graphs are COMPUTED from
    it (`reachB`), never supplied.

  **Classification of every premise of the four flagships** (`ziel_ort_mehrfaden_ende`,
  ZielOrtStart.lean; `keine_verklemmungG`, Verklemmung.lean; `rennfrei_g_voll`,
  RennfreiVoll.lean; `frame_schritte_beschraenkt`, KostenG.lean). Groups:
  **C** = `Akzeptiert` (checker), **Z** = `StartZulaessig` (restricts the
  universally quantified start `sp`/`init`), **U** = user obligation,
  **H** = hardware assumption, **R** = run data, universally quantified,
  **M** = member-list completeness / declaration datum (see "not decidable").

  | flagship | premise | group | where |
  |---|---|---|---|
  | mehrfaden_ende | `P`, `S`, `Q`, `fs` | data | quantified in `GabbroZiel` |
  | mehrfaden_ende | `O` | R | quantified, restricted only by H |
  | mehrfaden_ende | `passes`, `sp`, `init`, the run `M` | R | quantified; `sp`/`init` restricted by Z |
  | mehrfaden_ende | `e0 : Ereignis D` | M | declaration datum (a lock/table/global exists) |
  | mehrfaden_ende | `K` | -- | NOT a premise any more: `K t := reachB P fs (init t).1` (`kVon`) |
  | mehrfaden_ende | `hO : GutO O` | H | |
  | mehrfaden_ende | `hRL : RegLokal O` | H | |
  | mehrfaden_ende | `hQ : AxVertragO Q O` | H | |
  | mehrfaden_ende | `hlok : AxEnsLokal Q` | U | well-formedness of the declared axiom ensures (not decidable) |
  | mehrfaden_ende | `hS : SperrInvOk S`, half 1 | C | `sperrOrte` |
  | mehrfaden_ende | `hS : SperrInvOk S`, half 2 (`SperrInvLokal`) | U | not decidable: `S.inv` is a function on memory |
  | mehrfaden_ende | `hvoll : ∀ g, g ∈ fs` | M | not decidable: `D.Fn` has no enumeration |
  | mehrfaden_ende | `hFrag` | C | `frag` |
  | mehrfaden_ende | `hAbg : ∀ t, AbgK P fs (K t)` | C | `abg` (for EVERY possible root, so no `init` needed) |
  | mehrfaden_ende | `hWurzel : ∀ t, K t (init t).1` | -- | a theorem: `reachB_wurzel` |
  | mehrfaden_ende | `hFuss : ∀ f, FussS P S (lokK P K) f` | C + Z | `fuss` over the declared starts, plus `StartPasst` (each busy start on one thread) |
  | mehrfaden_ende | `hK : ∀ f, KoerperGutS …` | U | |
  | mehrfaden_ende | `hI : ∀ f, InvGutS …` | U | |
  | mehrfaden_ende | `hStart : StartGut P sp init` | Z | `StartZulaessig.req` |
  | mehrfaden_ende | `hSstart : ∀ L, S.inv L sp` | Z | `StartZulaessig.sperren` |
  | mehrfaden_ende | `hex : StartExklusiv init` | C + Z | from `wurzeln` + `StartPasst` (`startExklusiv_ohne_haelt`) |
  | verklemmung | `hO` | H | |
  | verklemmung | `hSt : StufenM P` | C | `stufen` |
  | verklemmung | `sp`, `init`, `M`, `hr` | R | |
  | verklemmung | `hLeer : ∀ t, D.haelt (init t).1 = []` | C + Z | `wurzeln` + `StartPasst` |
  | verklemmung | `ls`, `hls : ∀ L, L ∈ ls` | M | not decidable: `D.Lock` has no enumeration |
  | verklemmung | `hW` (all unfinished wait) | -- | antecedent of the conclusion, not a premise |
  | rennfrei_g_voll | `hO` | H | |
  | rennfrei_g_voll | `hex` | C + Z | as above |
  | rennfrei_g_voll | `ms`, `fs`, `n`, `hl`, `i`, `j`, `hij`, `hjn`, `hfg`, `c`, `L`, `hB`, `hzi`, `hzj` | R | the run and the two accesses |
  | frame_schritte | `hadm : rufTief P (n+1) g` | C | `zeit`, at `n := fs.length` |
  | frame_schritte | `f`, `g`, `rho`, `s0`, `k`, `M1`, `M2`, `hE`, `run`, `hA` | R | |

  **What could NOT be made decidable, and why:**
  * `hvoll`, `hls` (member lists complete): `D.Fn`, `D.Lock` are bare types
    without an enumeration; the exporter's `inductive`s are finite, and the
    proof is `cases` per declaration, not a Bool.
  * `SperrInvLokal S` (half 2 of `SperrInvOk`) and `AxEnsLokal Q`: `S.inv L`
    and `Q a` are Bool-valued FUNCTIONS on memory, not syntax; "reads only
    the listed carriers" quantifies over all memories. Decidable once both
    are carried as expressions (then by `Expr.orte`), which the model does
    not do today. Classified as user well-formedness.
  * `e0 : Ereignis D`: an inhabitant, not a fact; exists whenever the
    declaration has a lock, table or global (`Ereignis.gibt L`).
  * `StartGut`, `∀ L, S.inv L sp`: decidable for a given start (`startB`),
    but in `GabbroZiel` they RESTRICT the quantified start -- the theorem
    covers every start that meets them; they cannot be a program fact
    because they speak about `sp` and the start parameters.
  * `StartPasst` (busy starts on one thread each): it speaks about `init`,
    i.e. about which thread runs which start; it is decidable for a finite
    start table (`startB`), and `init : Faden → …` over `Faden = Nat` is not
    finite in general.
  * NOT in `Akzeptiert`, although decidable per instance:
    `kostenPasst P passes decl fs` (`kosten_passt_deklaration`, the DECLARED
    costs): `decl` is not part of `Programm D` (`costs` has no G form,
    Export104 CUT 3), and the check depends on `passes`, which `GabbroZiel`
    quantifies universally -- a body with `forever` fails it for large
    `passes`. The time leg carried here is the model bound
    `kostenTief P passes (fs.length + 1) g` (`zeit`).

  **Consequences that are findings, not premises:**
  * `zeit` refuses every program with an indirect call or a recursive call
    (`rufTief` admits neither) -- the time flagship covers no such frame.
  * `wurzeln` is the STRONG form of `N240`: the checker refuses only a
    lock COMMON to two starts; the deadlock leg needs starts that hold NO
    lock by signature (`hLeer`, SATZKARTE §16.6).
  * `StartZulaessig` can be unsatisfiable (then `GabbroZiel` says nothing
    about the program): the export of `beispiele/104` has no idle function,
    so no `init` passes `StartPasst` (`gP_start_leer`, AkzeptiertZeuge.lean).
    `Proben.lean` must show `∃ sp init, StartZulaessig …` on its witness.
  * A write-write race on an UNGUARDED carrier that no footprint reads is
    NOT refused: no flagship premise sees it. The race leg
    (`rennfrei_g_voll`, `DatenRasse`) covers lock-guarded carriers only, and
    the footprint (`fussOrte`) lists contract and read carriers, not
    writes. Two declared starts that both write an unguarded table and never
    read it pass `Akzeptiert` (the refusal witness `ak1_zwei_schreiber`
    needs `a`'s `ensures` to read the table). The checker's `H013` ("an
    entry writes `z`, and nothing declares it shared") has no counterpart in
    the model; adding one needs a syntactic list of the carriers a body
    writes, which the model does not have (only declared write permissions,
    which are not enumerable).
  * "Idle" (`ruheB`) and "thread-local" (`getrenntW`) are judged against
    DECLARED write permissions and footprints, as `GetrenntK` is (SATZKARTE
    §16.6): a function whose footprint is empty and that writes no footprint
    carrier counts as idle even if it writes some table.
-/
import Grammatik.Verklemmung
import Grammatik.KostenG

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Akzeptiert

variable [DecidableEq D.Fn]

/-! ## 1. Thread-locality over the declared starts -/

/-- **`c` is thread-local among the declared starts**: for every two
    DIFFERENT declared starts, no function the first reaches has `c` in its
    footprint while a function the second reaches may write it. -/
def getrenntW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w1 => ws.all fun w2 => decide (w1 = w2) ||
    (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) ||
    (fs.all fun g => !(reachB P fs w2 g) || !(TraegerSchreibt g c))

/-- What `getrenntW` decides. -/
def GetrenntW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w1, w1 ∈ ws → ∀ w2, w2 ∈ ws → w1 ≠ w2 →
    ∀ f, reachB P fs w1 f = true → c ∈ fussOrteG P f →
      ∀ g, reachB P fs w2 g = true → TraegerSchreibt g c = false

theorem getrenntW_iff {P : Programm D} {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {c : D.Tab ⊕ D.Glob} : getrenntW P fs ws c = true ↔ GetrenntW P fs ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne f hf hc g hg
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with (h1 | h1) | h1
    · exact absurd h1 hne
    · have h2 := (List.all_eq_true.mp h1) f (hvoll f)
      rw [hf, istIn_iff.mpr hc] at h2
      simp at h2
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [hg] at h2
      simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2
    · simp [hne]
    by_cases hfr : (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) = true
    · simp [hfr]
    · have hex : ∃ f, reachB P fs w1 f = true ∧ c ∈ fussOrteG P f := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun f _ => ?_)
        cases hr : reachB P fs w1 f
        · rfl
        · cases hi : istIn (fussOrteG P f) c
          · rfl
          · exact absurd ⟨f, hr, istIn_iff.mp hi⟩ hn
      obtain ⟨f, hf, hc⟩ := hex
      have hw : (fs.all fun g => !(reachB P fs w2 g) || !(TraegerSchreibt g c)) = true :=
        List.all_eq_true.mpr fun g _ => by
          cases hg : reachB P fs w2 g
          · rfl
          · simp [h w1 hw1 w2 hw2 hne f hf hc g hg]
      simp [hw]

/-! ## 2. The components -/

/-- Every computed call graph is closed -- for EVERY function as a root, so
    no start assignment is needed. -/
def abgAlleB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun w => abgB P fs (reachB P fs w)

/-- **The footprint check over the declared starts**: `fussMehrB` with
    thread-locality judged over `ws` (`getrenntW`) instead of over threads
    below a bound. -/
def fussWB (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || getrenntW P fs ws c || (waechterVon c).any fun L => istIn (S.orte L) c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || getrenntW P fs ws c)

/-- The lock floors on every body (`StufenM`). -/
def stufenB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => mE (bodenM f) (P.rumpf f)

/-- Every protected carrier is guarded by its lock (first half of
    `SperrInvOk`). -/
def sperrOrteB (S : SperrInv D) (ls : List D.Lock) : Bool :=
  ls.all fun L => (S.orte L).all fun c => decide (L ∈ waechterVon c)

/-- No declared start holds a lock by signature (`N240`, strong form). -/
def wurzelnB (ws : List D.Fn) : Bool :=
  ws.all fun w => (D.haelt w).isEmpty

/-- Every function is admitted at call depth `fs.length + 1` (no indirect
    call, no recursion): the premise of the frame bound. -/
def zeitB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun g => rufTief P (fs.length + 1) g

/-- **`Akzeptiert` -- what the checker decides, as ONE Bool.** -/
def Akzeptiert (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (ws : List D.Fn) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && zeitB P fs

/-- **What `Akzeptiert` decides, as Props** (field by field, the premises
    of the flagships they feed). -/
structure AkzeptiertP (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussS P S (getrenntW P fs ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w, w ∈ ws → D.haelt w = []
  zeit : ∀ g, rufTief P (fs.length + 1) g = true

/-! ## 3. Each component decides its Prop -/

section Komponenten

variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock} {ws : List D.Fn}

theorem abgAlleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    abgAlleB P fs = true ↔ ∀ w, AbgK P fs (reachB P fs w) := by
  constructor
  · intro h w
    exact abgB_ok hvoll ((List.all_eq_true.mp h) w (hvoll w))
  · intro h
    refine List.all_eq_true.mpr fun w _ => List.all_eq_true.mpr fun f _ => ?_
    cases hf : reachB P fs w f
    · rfl
    · simp [h w f hf]

theorem fussWB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    fussWB P S fs ws = true ↔ ∀ f, FussS P S (getrenntW P fs ws) f := by
  constructor
  · intro h f
    have h1 := (List.all_eq_true.mp h) f (hvoll f)
    simp only [Bool.and_eq_true] at h1
    refine ⟨fun c hc => ?_, fun c hc => (List.all_eq_true.mp h1.2) c hc⟩
    have h2 := (List.all_eq_true.mp h1.1) c hc
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact Or.inl (by simp only [Bool.or_eq_true]; exact h2)
    · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
      exact Or.inr ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩
  · intro h
    refine List.all_eq_true.mpr fun f _ => ?_
    simp only [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr fun c hc => ?_, List.all_eq_true.mpr fun c hc => (h f).2 c hc⟩
    rcases (h f).1 c hc with h2 | ⟨L, hL, hc'⟩
    · simp only [Bool.or_eq_true] at h2 ⊢
      exact Or.inl h2
    · simp only [Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨L, waechterVon_mem.mpr hL, istIn_iff.mpr hc'⟩)

omit [DecidableEq D.Fn] in
theorem stufenB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) : stufenB P fs = true ↔ StufenM P :=
  ⟨fun h f => (List.all_eq_true.mp h) f (hvoll f), fun h => List.all_eq_true.mpr fun f _ => h f⟩

omit [DecidableEq D.Fn] in
theorem sperrOrteB_iff (hls : ∀ L : D.Lock, L ∈ ls) :
    sperrOrteB S ls = true ↔ ∀ L c, c ∈ S.orte L → Bewacht c L := by
  constructor
  · intro h L c hc
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) L (hls L))) c hc
    exact waechterVon_mem.mp (of_decide_eq_true h1)
  · intro h
    exact List.all_eq_true.mpr fun L _ => List.all_eq_true.mpr fun c hc =>
      decide_eq_true (waechterVon_mem.mpr (h L c hc))

omit [DecidableEq D.Fn] in
theorem wurzelnB_iff : wurzelnB (D := D) ws = true ↔ ∀ w, w ∈ ws → D.haelt w = [] := by
  unfold wurzelnB
  rw [List.all_eq_true]
  exact forall_congr' fun w => imp_congr_right fun _ => List.isEmpty_iff

omit [DecidableEq D.Fn] in
theorem zeitB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    zeitB P fs = true ↔ ∀ g, rufTief P (fs.length + 1) g = true :=
  ⟨fun h g => (List.all_eq_true.mp h) g (hvoll g), fun h => List.all_eq_true.mpr fun g _ => h g⟩

/-- **`Akzeptiert` decides exactly `AkzeptiertP`** (given complete member
    lists). -/
theorem akzeptiert_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) :
    Akzeptiert P S fs ls ws = true ↔ AkzeptiertP P S fs ls ws := by
  unfold Akzeptiert
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨h1, (abgAlleB_iff hvoll).mp h2, (fussWB_iff hvoll).mp h3, (stufenB_iff hvoll).mp h4,
      (sperrOrteB_iff hls).mp h5, wurzelnB_iff.mp h6, (zeitB_iff hvoll).mp h7⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h.frag, (abgAlleB_iff hvoll).mpr h.abg⟩, (fussWB_iff hvoll).mpr h.fuss⟩,
      (stufenB_iff hvoll).mpr h.stufen⟩, (sperrOrteB_iff hls).mpr h.sperrOrte⟩,
      wurzelnB_iff.mpr h.wurzeln⟩, (zeitB_iff hvoll).mpr h.zeit⟩

theorem akzeptiertP_of {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (h : Akzeptiert P S fs ls ws = true) : AkzeptiertP P S fs ls ws :=
  (akzeptiert_iff hvoll hls).mp h

end Komponenten

/-! ## 4. The start -/

/-- **An idle start**: holds no lock by signature, and every function it
    reaches has an empty footprint and writes no carrier of any footprint.
    Arbitrarily many threads may run it. -/
def ruheB (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && fs.all fun f => !(reachB P fs w f) ||
    ((fussOrteG P f).isEmpty && fs.all fun h => (fussOrteG P h).all fun c => !(TraegerSchreibt f c))

theorem ruheB_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) {w : D.Fn}
    (h : ruheB P fs w = true) :
    D.haelt w = [] ∧ ∀ f, reachB P fs w f = true →
      fussOrteG P f = [] ∧ ∀ h c, c ∈ fussOrteG P h → TraegerSchreibt f c = false := by
  unfold ruheB at h
  simp only [Bool.and_eq_true] at h
  refine ⟨List.isEmpty_iff.mp h.1, fun f hf => ?_⟩
  have h1 := (List.all_eq_true.mp h.2) f (hvoll f)
  rw [hf] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
  refine ⟨List.isEmpty_iff.mp h1.1, fun g c hc => ?_⟩
  have h2 := (List.all_eq_true.mp ((List.all_eq_true.mp h1.2) g (hvoll g))) c hc
  simpa using h2

/-- **The start fits the declared starts**: every thread runs a declared
    start or an idle one, and a start that is not idle runs on ONE thread. -/
structure StartPasst (P : Programm D) (fs ws : List D.Fn)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  wurzel : ∀ t, (init t).1 ∈ ws ∨ ruheB P fs (init t).1 = true
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → ruheB P fs (init t).1 = true

/-- **`StartZulaessig` -- the starts the goal speaks about.** The start
    assignment fits the declared starts; the start functions' `requires`
    hold at the start memory with the start parameters; every lock
    invariant holds at the start memory. Not a program fact: it speaks about
    `sp` and `init`, which `GabbroZiel` quantifies universally. -/
structure StartZulaessig (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  passt : StartPasst P fs ws init
  req : StartGut P sp init
  sperren : ∀ L, S.inv L sp = true

/-- The call graph of thread `t`, computed from its start function. -/
def kVon (P : Programm D) (fs : List D.Fn) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) : D.Fn → Bool :=
  reachB P fs (init t).1

section Start

variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock} {ws : List D.Fn}
  {init : Faden → Σ f : D.Fn, Env D (D.params f)}

/-- The declared-start test gives thread-locality for the computed graphs
    of every start that fits. -/
theorem getrenntK_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hZ : StartPasst P fs ws init)
    {c : D.Tab ⊕ D.Glob} (hc : getrenntW P fs ws c = true) : GetrenntK P (kVon P fs init) c := by
  intro t u htu f hf hcf g hg
  by_cases hrt : ruheB P fs (init t).1 = true
  · rw [((ruheB_ok hvoll hrt).2 f hf).1] at hcf
    exact absurd hcf List.not_mem_nil
  by_cases hru : ruheB P fs (init u).1 = true
  · exact ((ruheB_ok hvoll hru).2 g hg).2 f c hcf
  have hwt := (hZ.wurzel t).resolve_right hrt
  have hwu := (hZ.wurzel u).resolve_right hru
  have hne : (init t).1 ≠ (init u).1 := fun he => hrt (hZ.einmal t u htu he)
  exact (getrenntW_iff hvoll).mp hc _ hwt _ hwu hne f hf hcf g hg

/-- No thread starts holding a lock by signature. -/
theorem leer_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertP P S fs ls ws)
    (hZ : StartPasst P fs ws init) (t : Faden) : D.haelt (init t).1 = [] := by
  rcases hZ.wurzel t with h | h
  · exact hA.wurzeln _ h
  · exact (ruheB_ok hvoll h).1

/-- **`Akzeptiert_ok` -- the checker's Bool and an admitted start give every
    decidable premise of the four flagships**, with the call graphs
    computed from the program (`kVon`). -/
theorem Akzeptiert_ok (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hA : Akzeptiert P S fs ls ws = true) {sp : Speicher D}
    (hZ : StartZulaessig P S fs ws sp init) :
    programmImFragmentG P fs = true ∧
    (∀ t, AbgK P fs (kVon P fs init t)) ∧
    (∀ t, kVon P fs init t (init t).1 = true) ∧
    (∀ f, FussS P S (lokK P (kVon P fs init)) f) ∧
    (∀ L c, c ∈ S.orte L → Bewacht c L) ∧
    StartGut P sp init ∧ (∀ L, S.inv L sp = true) ∧ StartExklusiv init ∧
    StufenM P ∧ (∀ t, D.haelt (init t).1 = []) ∧
    (∀ g, rufTief P (fs.length + 1) g = true) := by
  have hP := akzeptiertP_of hvoll hls hA
  have hLeer := leer_of hvoll hP hZ.passt
  refine ⟨hP.frag, fun t => hP.abg _, fun t => reachB_wurzel P fs _, fun f => ?_, hP.sperrOrte,
    hZ.req, hZ.sperren, startExklusiv_ohne_haelt init hLeer, hP.stufen, hLeer, hP.zeit⟩
  exact fussS_mono (fun c _ hc => lokK_of (getrenntK_of hvoll hZ.passt hc)) (hP.fuss f)

end Start

end Akzeptiert

/-! ## 5. `SperrInvOk`: the decided half and the user's half -/

/-- The second half of `SperrInvOk`: the invariant reads only the protected
    carriers. NOT decidable (`S.inv L` is a function on memory); holds by
    construction for an invariant written over the listed carriers. -/
def SperrInvLokal (S : SperrInv D) : Prop :=
  ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s'

theorem sperrInvOk_iff (S : SperrInv D) :
    SperrInvOk S ↔ (∀ L c, c ∈ S.orte L → Bewacht c L) ∧ SperrInvLokal S :=
  Iff.rfl

/-! ## 6. Finite start tables: `StartZulaessig` decided -/

/-- **A finite start table**: thread `i` below `aktiv.length` runs
    `aktiv[i]`, every later thread runs `ruhe` (G starts every thread of
    `Faden = Nat`). -/
structure StartTafel (D : Deklaration) where
  aktiv : List (Σ f : D.Fn, Env D (D.params f))
  ruhe : Σ f : D.Fn, Env D (D.params f)

/-- The start assignment of a table. -/
def StartTafel.init (st : StartTafel D) : Faden → Σ f : D.Fn, Env D (D.params f) :=
  fun t => st.aktiv.getD t st.ruhe

theorem StartTafel.init_mem (st : StartTafel D) (t : Faden) :
    st.init t = st.ruhe ∨ st.init t ∈ st.aktiv := by
  unfold StartTafel.init
  rw [List.getD_eq_getElem?_getD]
  cases h : st.aktiv[t]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_of_getElem? h)

theorem StartTafel.init_ab (st : StartTafel D) {t : Faden} (ht : st.aktiv.length ≤ t) :
    st.init t = st.ruhe := by
  unfold StartTafel.init
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht]
  rfl

section Tafel

variable [DecidableEq D.Fn]

/-- **`StartZulaessig` for a start table, as a Bool.** -/
def startB (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (ws : List D.Fn) (st : StartTafel D) (sp : Speicher D) : Bool :=
  ruheB P fs st.ruhe.1 &&
  (List.range st.aktiv.length).all (fun i =>
    (decide ((st.init i).1 ∈ ws) || ruheB P fs (st.init i).1) &&
    (List.range st.aktiv.length).all fun j =>
      decide (i = j) || !(decide ((st.init i).1 = (st.init j).1)) || ruheB P fs (st.init i).1) &&
  (st.ruhe :: st.aktiv).all (fun a =>
    wahr? (eval (sp.welt []) (P.requires a.1) (sp.welt []) a.2)) &&
  ls.all fun L => S.inv L sp

theorem startB_ok {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {ws : List D.Fn} {st : StartTafel D} {sp : Speicher D} (hls : ∀ L : D.Lock, L ∈ ls)
    (h : startB P S fs ls ws st sp = true) : StartZulaessig P S fs ws sp st.init := by
  unfold startB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hi : ∀ i, i < st.aktiv.length →
      ((st.init i).1 ∈ ws ∨ ruheB P fs (st.init i).1 = true) ∧
      ∀ j, j < st.aktiv.length → i ≠ j → (st.init i).1 = (st.init j).1 →
        ruheB P fs (st.init i).1 = true := by
    intro i hi
    have e := (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at e
    refine ⟨e.1, fun j hj hij he => ?_⟩
    have e2 := (List.all_eq_true.mp e.2) j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      at e2
    rcases e2 with (e2 | e2) | e2
    · exact absurd e2 hij
    · exact absurd he e2
    · exact e2
  refine ⟨⟨fun t => ?_, fun t u htu he => ?_⟩, fun t => ?_,
    fun L => (List.all_eq_true.mp h4) L (hls L)⟩
  · by_cases ht : t < st.aktiv.length
    · exact (hi t ht).1
    · rw [st.init_ab (Nat.le_of_not_lt ht)]
      exact Or.inr h1
  · by_cases ht : t < st.aktiv.length
    · by_cases hu : u < st.aktiv.length
      · exact (hi t ht).2 u hu htu he
      · rw [he, st.init_ab (Nat.le_of_not_lt hu)]
        exact h1
    · rw [st.init_ab (Nat.le_of_not_lt ht)]
      exact h1
  · show wahr? (eval (sp.welt []) (P.requires (st.init t).1) (sp.welt []) (st.init t).2) = true
    rcases st.init_mem t with e | e
    · rw [e]
      exact (List.all_eq_true.mp h3) _ List.mem_cons_self
    · exact (List.all_eq_true.mp h3) _ (List.mem_cons_of_mem _ e)

end Tafel

#print axioms Gabbro.Grammatik.getrenntW_iff
#print axioms Gabbro.Grammatik.akzeptiert_iff
#print axioms Gabbro.Grammatik.getrenntK_of
#print axioms Gabbro.Grammatik.Akzeptiert_ok
#print axioms Gabbro.Grammatik.startB_ok

end Gabbro.Grammatik
