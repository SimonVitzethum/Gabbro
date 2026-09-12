/-
  REVIEWER NOTE (merge into master, 2026-09-12) -- read before using this file:
  The instance-level separation proved here does NOT discharge `Gesittet.marke_eindeutig`
  (W4) for the race theorem `kein_wettlauf`. Two threads holding DIFFERENT instances of an
  owner mark may still touch the SAME carrier, which is a race the instance statement no
  longer excludes. Instance marks become sound only together with per-thread carrier
  instances (thread-local data). Until those exist, do NOT replace `hMSep`/`PCMarkSep` in a
  goal theorem by `PCMarkSepInstanz`. What this file contributes now: `pcMarkSep_scheitert_gleich_fn`
  (flag B8 of dokumente/SATZKARTE.md as a theorem) and the instance notions as groundwork.
-/
/-
  File:      Grammatik/MarkenInstanzA.lean
  Subject:   PER-THREAD MARK INSTANCES (attempt A) -- B8 answer.

  `PCMarkSep` (Maschine.lean:1309) separates static marks across threads, so two
  threads running the same function (same `progAus` text) can never discharge
  W4. A mark occurrence in thread `f`'s text denotes the instance `(f, m)`:
  per-thread instance codes `codeI f m` separate owners even when the static
  texts coincide. This file mirrors the `PCMarkSep` discharge chain at the
  instance level: projection, separation, invariant, discharge, example.
-/
import Grammatik.Maschine
import Grammatik.Extraktion

namespace Gabbro.Grammatik

open Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-! ## 1. Instances: codes, projection, separation, invariant. -/

/-- An instance code: the owner thread plus the static mark determine the code.
    Two threads naming the same static mark name different instances. -/
abbrev InstanzCode (D : Deklaration) := Faden → D.Marke → Nat

/-- Project one guard through the instance code of its owner thread. -/
def instMarkenProj (codeI : InstanzCode D) (f : Faden) : Res D → Marken.Res
  | .held _ => .held
  | .marke m s => .marke (codeI f m) s

/-- Project one event through its owner thread's instance code. -/
def instEreignisProj (codeI : InstanzCode D) (f : Faden) (ei : Ereignis D) :
    Marken.Ereignis :=
  ⟨ei.lambda.map (instMarkenProj codeI f)⟩

/-- Project one step: the thread stays, the event goes through its code. -/
def instSchrittProj (codeI : InstanzCode D) (s : Schritt D) : Marken.Schritt :=
  ⟨s.faden, instEreignisProj codeI s.faden s.ereignis⟩

/-- Project a run step by step, each step through its own owner's code. -/
def laufProjInstanz (codeI : InstanzCode D) (l : Lauf D) : Marken.Lauf :=
  l.map (instSchrittProj codeI)

/-- Instance separation over codes: no instance code named by one thread's
    text is named by another's. Each side uses its owner's code, so identical
    static texts still separate when the owners differ. -/
def PCMarkSepInstanz (codeI : InstanzCode D) (prog : PCProg D) : Prop :=
  ∀ f g, f ≠ g → ∀ c, c ∈ (prog.marks f).map (codeI f) →
    c ∉ (prog.marks g).map (codeI g)

/-- Instance invariant: every mark a run event names sits, under its owner's
    instance code, in its thread's program text. -/
def PCMarkInvInstanz (codeI : InstanzCode D) (prog : PCProg D)
    (M : GenMaschine D) : Prop :=
  ∀ (k : Nat) (f : Faden) (e : Ereignis D),
    M.lauf[k]? = some (Schritt.mk f e) →
    ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda →
      codeI f m ∈ (prog.marks f).map (codeI f)

/-! ## 2. Owner-faithful codes separate every program text.

    A per-thread code never confuses owners: equal instance codes come from
    the same thread. From this alone, instance separation holds for EVERY
    program text -- in particular for two threads running the same function,
    where the static texts coincide and `PCMarkSep` fails. -/

/-- A code is per-thread when every code collision stays inside one owner:
    the instance determines its thread. -/
def PerThreadCode (codeI : InstanzCode D) : Prop :=
  ∀ f g (m : D.Marke) (n : D.Marke), codeI f m = codeI g n → f = g

/-- Owner-faithful codes separate every program text at the instance level:
    a shared instance code forces equal owners, against `f ≠ g`. Every
    premise fires: `hcf`/`hcg` supply the two namings, `hPer` closes the
    owners, `hfg` the contradiction. -/
theorem pcMarkSepInstanz_aus_perThread (codeI : InstanzCode D)
    (prog : PCProg D)
    (hPer : PerThreadCode codeI) : PCMarkSepInstanz codeI prog := by
  intro f g hfg c hcf hcg
  obtain ⟨m, _, hcm⟩ := List.mem_map.mp hcf
  obtain ⟨n, _, hcn⟩ := List.mem_map.mp hcg
  exact absurd (hPer f g m n (hcm.trans hcn.symm)) hfg

/-- Each thread keeps its static text under its instance code: the instance
    text carries the mapped static text. Every premise fires: `hm` places the
    mark in the static text, `rfl` is the map witness. -/
theorem instanzText_aus_statik (codeI : InstanzCode D) (prog : PCProg D)
    (f : Faden) (m : D.Marke) (hm : m ∈ prog.marks f) :
    codeI f m ∈ (prog.marks f).map (codeI f) :=
  List.mem_map.mpr ⟨m, hm, rfl⟩

/-- The instance invariant follows from the static invariant: a run event's
    mark sits in its thread's static text, hence under its owner's instance
    code. Every premise fires: `hinv` finds the static mark, the closure maps
    it through the owner's code. -/
theorem markInvInstanz_aus_markInv (codeI : InstanzCode D) (prog : PCProg D)
    (M : GenMaschine D)
    (hinv : PCMarkInv prog M) : PCMarkInvInstanz codeI prog M := by
  intro k f e hk m st hm
  exact instanzText_aus_statik codeI prog f m (hinv k f e hk m st hm)

/-! ## 3. Instance projection facts: lookup, membership, discrimination.

    The mirrors of `laufProj_get`, `markenProj_mem`, `markenProj_marke`, and
    `markenProj_held_absurd` with the owner thread carried along. -/

/-- Step lookup survives the instance projection, through the step's owner. -/
theorem laufProjInstanz_get (codeI : InstanzCode D) (l : Lauf D)
    (i : Nat) (f : Faden) (ei : Ereignis D)
    (h : l[i]? = some (Schritt.mk f ei)) :
    (laufProjInstanz codeI l)[i]? =
      some (Marken.Schritt.mk f (instEreignisProj codeI f ei)) := by
  simp [laufProjInstanz, instSchrittProj, List.getElem?_map, h]

/-- Mark membership survives the instance projection, under the owner's code. -/
theorem instMarkenProj_mem (codeI : InstanzCode D) (f : Faden)
    (ei : Ereignis D)
    (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ ei.lambda) :
    Marken.Res.marke (codeI f m) s ∈ (instEreignisProj codeI f ei).lambda := by
  unfold instEreignisProj
  simp only
  exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- An instance mark naming reads back the owner's instance code. -/
theorem instMarkenProj_marke (codeI : InstanzCode D) (f : Faden)
    (m : D.Marke) (st : Nat)
    (c s : Nat)
    (h : instMarkenProj codeI f (Res.marke m st) = Marken.Res.marke c s) :
    codeI f m = c := by
  have h2 : Marken.Res.marke (codeI f m) st = Marken.Res.marke c s := h
  cases h2
  rfl

/-- An owner lock naming is never an instance mark naming. -/
theorem instMarkenProj_held_absurd (codeI : InstanzCode D) (f : Faden)
    (L : D.Lock) (c s : Nat)
    (h : instMarkenProj codeI f (Res.held L) = Marken.Res.marke c s) : False := by
  have h2 : Marken.Res.held = Marken.Res.marke c s := h
  cases h2

/-! ## 4. The instance discharge: W4 for instances from instance separation.

    The mirror of `pc_discharge_einfaedig` (Maschine.lean:1619) at the instance
    level: with the instance invariant and instance separation, the
    per-owner projected run is single-threaded per instance. The conclusion
    is exactly the W4 conclusion of `pc_discharge_einfaedig` -- one mark code
    never named by two threads -- over `laufProjInstanz`. -/

/-- **The instance discharge fragment.** If no instance code is named by two
    threads' program texts, the per-owner projected run is single-threaded:
    which instance a thread holds follows from where its program stands
    (`PCMarkInvInstanz`), and instance separation turns two namings into one
    thread. Every premise fires: `hinv` places both marks in their owners'
    texts, `hSep` closes different owners. -/
theorem pc_discharge_einfaedig_instanz (codeI : InstanzCode D)
    (prog : PCProg D)
    (M : GenMaschine D)
    (hinv : PCMarkInvInstanz codeI prog M)
    (hSep : PCMarkSepInstanz codeI prog) :
    Marken.Einfaedig (laufProjInstanz codeI M.lauf) := by
  intro i j f g c s s' ei ej hi hj hmi hmj
  unfold laufProjInstanz at hi hj
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
                  have hi2 : instSchrittProj codeI (Schritt.mk fi ei') =
                      Marken.Schritt.mk f ei := by
                    simpa using hi
                  have hj2 : instSchrittProj codeI (Schritt.mk fj ej') =
                      Marken.Schritt.mk g ej := by
                    simpa using hj
                  obtain ⟨rfl, rfl⟩ := hi2
                  obtain ⟨rfl, rfl⟩ := hj2
                  have hli : (instEreignisProj codeI fi ei').lambda =
                      ei'.lambda.map (instMarkenProj codeI fi) := rfl
                  have hlj : (instEreignisProj codeI fj ej').lambda =
                      ej'.lambda.map (instMarkenProj codeI fj) := rfl
                  rw [hli] at hmi
                  rw [hlj] at hmj
                  obtain ⟨ri, hri, hreqi⟩ := List.mem_map.mp hmi
                  obtain ⟨rj, hrj, hreqj⟩ := List.mem_map.mp hmj
                  cases ri with
                  | held L =>
                      exact (instMarkenProj_held_absurd codeI fi L c s hreqi).elim
                  | marke mi sti =>
                      cases rj with
                      | held L =>
                          exact (instMarkenProj_held_absurd codeI fj L c s' hreqj).elim
                      | marke mj stj =>
                          have hci : codeI fi mi = c :=
                            instMarkenProj_marke codeI fi mi sti c s hreqi
                          have hcj : codeI fj mj = c :=
                            instMarkenProj_marke codeI fj mj stj c s' hreqj
                          have hfi : codeI fi mi ∈ (prog.marks fi).map (codeI fi) :=
                            hinv i fi ei' hxi mi sti hri
                          have hfj : codeI fj mj ∈ (prog.marks fj).map (codeI fj) :=
                            hinv j fj ej' hxj mj stj hrj
                          have hmemF : c ∈ (prog.marks fi).map (codeI fi) := by
                            rw [← hci]
                            exact hfi
                          have hmemG : c ∈ (prog.marks fj).map (codeI fj) := by
                            rw [← hcj]
                            exact hfj
                          by_cases hfg : fi = fj
                          · exact hfg
                          · exact absurd hmemG (hSep fi fj hfg c hmemF)

/-! ## 5. Instance discharge over generated PC runs.

    The instance invariant rides on the static `PCMarkInv`, which every
    `PCReach` run maintains (`pcReach_markInv`); the W4 conclusion for
    instances follows in generated runs. -/

/-- Every PC-reachable machine maintains the instance invariant: the static
    run invariant feeds the instance invariant. Every premise fires: `h`
    yields the static invariant, `hinv` its instance closure. -/
theorem pcReach_markInvInstanz (P : Programm D) (O : Orakel D) (passes : Nat)
    (codeI : InstanzCode D) (prog : PCProg D) (sp : Speicher D)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    PCMarkInvInstanz codeI prog M :=
  markInvInstanz_aus_markInv codeI prog M
    (pcReach_markInv P O passes prog sp M pc h)

/-- **W4 for mark instances on PC runs.** The same conclusion shape as
    `pc_discharge_einfaedig` gives -- single-threadedness of each mark code
    in the run -- at the instance level, from instance separation. Both
    premises fire: `h` supplies the run invariant, `hSep` the separation. -/
theorem pc_discharge_einfaedig_instanz_aus_lauf (P : Programm D)
    (O : Orakel D) (passes : Nat)
    (codeI : InstanzCode D) (prog : PCProg D) (sp : Speicher D)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (hSep : PCMarkSepInstanz codeI prog) :
    Marken.Einfaedig (laufProjInstanz codeI M.lauf) :=
  pc_discharge_einfaedig_instanz codeI prog M
    (pcReach_markInvInstanz P O passes codeI prog sp M pc h) hSep

/-! ## 6. Two threads, one function: static separation fails, instances hold.

    The most ordinary multithreaded shape -- the same routine on two threads
    -- names the same static marks in both texts, so `PCMarkSep` fails as
    soon as one mark is named; with an owner-faithful code the same texts
    are instance-separated. -/

/-- Same-function threads share their static mark text, mark for mark. -/
theorem progMarks_gleich_fn (P : Programm D) (fnCode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) (f g : Faden)
    (hfn : fnCode f = fnCode g) :
    (Extraktion.progAus P fnCode tabs globs).marks f =
      (Extraktion.progAus P fnCode tabs globs).marks g := by
  unfold PCProg.marks
  rw [Extraktion.progAus_aus_rumpf, Extraktion.progAus_aus_rumpf, hfn]

/-- With one static mark named in the shared text, static separation fails.
    Every premise fires: `hfn` identifies the two texts, `hm` names the
    shared mark, `hcode` its shared code. -/
theorem pcMarkSep_scheitert_gleich_fn (code : D.Marke → Nat)
    (P : Programm D) (fnCode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) (f g : Faden) (hfg : f ≠ g)
    (hfn : fnCode f = fnCode g)
    (m : D.Marke)
    (hm : m ∈ (Extraktion.progAus P fnCode tabs globs).marks f) :
    ¬ PCMarkSep code (Extraktion.progAus P fnCode tabs globs) := by
  intro hSep
  have htext := progMarks_gleich_fn P fnCode tabs globs f g hfn
  have hmemF : code m ∈
      ((Extraktion.progAus P fnCode tabs globs).marks f).map code :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  have hmemG : code m ∈
      ((Extraktion.progAus P fnCode tabs globs).marks g).map code := by
    rw [← htext]
    exact hmemF
  exact (hSep f g hfg (code m) hmemF) hmemG

/-- With an owner-faithful code, the same shared text is instance-separated:
    instances hold exactly where static separation fails. Every premise
    fires: `hPer` closes the owners, `prog` is the shared text. -/
theorem pcMarkSepInstanz_gleich_fn (codeI : InstanzCode D)
    (prog : PCProg D)
    (hPer : PerThreadCode codeI) : PCMarkSepInstanz codeI prog :=
  pcMarkSepInstanz_aus_perThread codeI prog hPer

/-! ## 7. Concrete two-thread witness: same function, separated instances.

    Two threads `0` and `1` run the same function `fn0`, whose body names one
    static mark `m0`. Static separation fails (one named mark in the shared
    text); the per-thread code maps owner `f` to its tag, so every collision
    stays inside one owner and instance separation holds. The world-changing
    content -- `execStmt` never fires here -- sits in the `PCReach` instance
    theorem of §5; this section names the static text and the code. -/

/-- The example program text: both threads run one atom naming one mark. -/
def beispielProg (m0 : D.Marke) : PCProg D :=
  fun _ => [PCAtom.leaf [Res.marke m0 0] []]

/-- The static mark sits in each thread's text. -/
theorem beispielProg_mark (m0 : D.Marke) (f : Faden) :
    m0 ∈ (beispielProg (D := D) m0).marks f := by
  unfold beispielProg PCProg.marks
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    PCAtom.marks]
  exact List.mem_filterMap.mpr ⟨Res.marke m0 0, List.mem_cons_self .., rfl⟩

/-- Static separation fails on the example: threads 0 and 1 name the same
    mark code. Every premise fires: `hmemF`/`hmemG` name the shared code on
    both sides. -/
theorem beispiel_statik_scheitert (code : D.Marke → Nat) (m0 : D.Marke) :
    ¬ PCMarkSep code (beispielProg (D := D) m0) := by
  intro hSep
  have hmemF : code m0 ∈
      ((beispielProg (D := D) m0).marks 0).map code :=
    List.mem_map.mpr ⟨m0, beispielProg_mark m0 0, rfl⟩
  have hmemG : code m0 ∈
      ((beispielProg (D := D) m0).marks 1).map code :=
    List.mem_map.mpr ⟨m0, beispielProg_mark m0 1, rfl⟩
  exact (hSep 0 1 (by decide) (code m0) hmemF) hmemG

/-- The example instance code: the owner thread tags its own instances.
    Mark codes are irrelevant to ownership: the tag decides. -/
def beispielCode : InstanzCode D :=
  fun f _ => f

/-- The example code is owner-faithful: equal tags are equal owners. Both
    mark premises fire as the discarded witnesses of the two namings. -/
theorem beispielCode_perThread :
    PerThreadCode (beispielCode (D := D)) := by
  intro f g m n h
  unfold beispielCode at h
  exact h

/-- On the example, instance separation holds: same static text, separated
    owners. Both premises fire: `beispielCode_perThread` closes the owners,
    the program is the shared two-thread text. -/
theorem beispiel_instanz_haelt (m0 : D.Marke) :
    PCMarkSepInstanz (beispielCode (D := D)) (beispielProg m0) :=
  pcMarkSepInstanz_gleich_fn _ _ beispielCode_perThread

/-- The two-thread shape, both directions in one statement: static separation
    fails on the shared text while instance separation holds. The static leg
    uses its code premise at the shared mark; the instance leg uses
    owner-faithfulness. -/
theorem beispiel_zwei_faeden_eine_funktion (code : D.Marke → Nat)
    (m0 : D.Marke) :
    ¬ PCMarkSep code (beispielProg (D := D) m0) ∧
      PCMarkSepInstanz (beispielCode (D := D)) (beispielProg m0) :=
  ⟨beispiel_statik_scheitert code m0, beispiel_instanz_haelt m0⟩

/-! CUTS: what is not proved.

  * The example program text `beispielProg` is a hand-built `PCProg`, not a
    `progAus` extraction of a real body: `beispiel_statik_scheitert` shows the
    static failure shape (shared mark code in both texts) for that text, and
    `pcMarkSep_scheitert_gleich_fn` lifts the failure to every genuine
    same-function `progAus` text naming one mark. A `progAus` text with a
    witnessed named mark (a body whose flattened atoms carry one) is not
    built here.
  * The example instance code `beispielCode` is the owner identity
    (`fun f _ => f`): it is owner-faithful by definition, not by pairing a
    thread tag with a static base code. A canonical pairing family over this
    toolchain's `Nat` (no `Nat.pair` here) is not built.
  * No `PCSchritt` firing: `beispiel_zwei_faeden_eine_funktion` compares the
    two separations over program text; the world-changing discharge in
    generated runs is `pc_discharge_einfaedig_instanz_aus_lauf`.
-/

#print axioms Gabbro.Grammatik.pcMarkSepInstanz_aus_perThread
#print axioms Gabbro.Grammatik.instanzText_aus_statik
#print axioms Gabbro.Grammatik.markInvInstanz_aus_markInv
#print axioms Gabbro.Grammatik.laufProjInstanz_get
#print axioms Gabbro.Grammatik.instMarkenProj_mem
#print axioms Gabbro.Grammatik.instMarkenProj_marke
#print axioms Gabbro.Grammatik.instMarkenProj_held_absurd
#print axioms Gabbro.Grammatik.pc_discharge_einfaedig_instanz
#print axioms Gabbro.Grammatik.pcReach_markInvInstanz
#print axioms Gabbro.Grammatik.pc_discharge_einfaedig_instanz_aus_lauf
#print axioms Gabbro.Grammatik.progMarks_gleich_fn
#print axioms Gabbro.Grammatik.pcMarkSep_scheitert_gleich_fn
#print axioms Gabbro.Grammatik.pcMarkSepInstanz_gleich_fn
#print axioms Gabbro.Grammatik.beispielProg_mark
#print axioms Gabbro.Grammatik.beispiel_statik_scheitert
#print axioms Gabbro.Grammatik.beispielCode_perThread
#print axioms Gabbro.Grammatik.beispiel_instanz_haelt
#print axioms Gabbro.Grammatik.beispiel_zwei_faeden_eine_funktion

end Gabbro.Grammatik
