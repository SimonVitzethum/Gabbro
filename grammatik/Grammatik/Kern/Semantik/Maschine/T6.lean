/- Part 6 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T5

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

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
          have h1 : ([PCAtom.leaf Λ cs₀]).length = 1 := by simp only [List.length_cons, List.length_nil, Nat.zero_add]
          have hlen : ([PCAtom.leaf Λ cs₀]).length ≤ pcmid f := by
            rw [h1]
            exact Nat.succ_le_of_lt hlt
          have hnone := List.getElem?_eq_none hlen
          rw [hprog, hnone] at hpc
          simp only [reduceCtorEq] at hpc
        have hhead : HeadAtom prog f Λ cs₀ := by
          show (prog f)[0]? = some (PCAtom.leaf Λ cs₀)
          simp only [hprog, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero]
        exact zaehler_aus_konstruktion_erstschritt prog f Λ cs₀ P O passes M0
          Mmid pcmid _ _ hs0 hpre hfrei hhead
      · exfalso
        rw [hprog] at hpcT
        by_cases hz : pcmid f = 0
        · rw [hz] at hpcT
          simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, reduceCtorEq] at hpcT
        · have hlt : 0 < pcmid f := Nat.pos_of_ne_zero hz
          have h1 : ([PCAtom.leaf Λ cs₀]).length = 1 := by simp only [List.length_cons, List.length_nil, Nat.zero_add]
          have hlen : ([PCAtom.leaf Λ cs₀]).length ≤ pcmid f := by
            rw [h1]
            exact Nat.succ_le_of_lt hlt
          have hnone := List.getElem?_eq_none hlen
          rw [hnone] at hpcT
          simp only [reduceCtorEq] at hpcT
      · exfalso
        rw [hprog] at hpcR
        by_cases hz : pcmid f = 0
        · rw [hz] at hpcR
          simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, reduceCtorEq] at hpcR
        · have hlt : 0 < pcmid f := Nat.pos_of_ne_zero hz
          have h1 : ([PCAtom.leaf Λ cs₀]).length = 1 := by simp only [List.length_cons, List.length_nil, Nat.zero_add]
          have hlen : ([PCAtom.leaf Λ cs₀]).length ≤ pcmid f := by
            rw [h1]
            exact Nat.succ_le_of_lt hlt
          have hnone := List.getElem?_eq_none hlen
          rw [hnone] at hpcR
          simp only [reduceCtorEq] at hpcR
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


end Gabbro.Grammatik
