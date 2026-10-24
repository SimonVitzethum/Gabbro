/- Part 8 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T7

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- The `PCSchritt` footprint checks discharged against `progAus` atoms for
    oracle leaves: a fired `axiomCall` leaf whose counter points at its
    extracted atom, under the recording oracle bound (`hO`), names only that
    atom's marks (reads name `Λ`; oracle writes name the mark-free `Λe`) and
    touches only its carriers (declared writes over the caller's domains --
    hence the completeness premises -- plus the read hull) -- hence the
    thread's program text (`pcAtom_mem_marks`/`pcAtom_mem_carriers`). The
    atom-identity premise (`hcs`) stays the scheduler/witness duty (remainder
    S12 of §17). -/
theorem hmark_hcar_aus_progAus_axiomCall
    (O : Orakel D) (passes : Nat)
    (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hO : GutO O)
    (hct : ∀ t, D.aschreibt a t = true → t ∈ tabs)
    (hcg : ∀ g, D.agschreibt a g = true → g ∈ globs)
    (M : GenMaschine D) (f : Faden) (ρ : Env D Γ)
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ (M.weltVon f).spur)
    (hh : HeldGenau Λ (M.weltVon f).haelt)
    (pc : PCStand) (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (progAus P code tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = stmtTraeger tabs globs
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
      stmtOrte (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ)) :
    (∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda →
      m ∈ (progAus P code tabs globs).marks f) ∧
    (∀ e ∈ neu, ∀ o, e.traeger = some o →
      o ∈ (progAus P code tabs globs).carriers f) := by
  obtain ⟨Λe, hmf, hlam, hcar⟩ :=
    execEreignis_aus_axiomCall O passes a args h hw hg hd hgd hO tabs globs
      hct hcg _ ρ σ' neu hh hstep hneu
  have ha : PCAtom.leaf Λa cs ∈ progAus P code tabs globs f :=
    List.mem_of_getElem? hpc
  constructor
  · intro e he m st hm
    rcases hlam e he with hL | hLe
    · rw [hL] at hm
      rw [← hΛa] at hm
      exact pcAtom_mem_marks _ _ _ ha m
        (by simp only [PCAtom.marks]
            exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩)
    · rw [hLe] at hm
      exact absurd hm (hmf m st)
  · intro e he o ho
    have hmem : o ∈ stmtTraeger tabs globs
        (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
        stmtOrte (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) :=
      hcar e he o ho
    apply pcAtom_mem_carriers _ _ _ ha o
    simp only [PCAtom.carriers]
    rw [hcs]
    exact hmem

#print axioms Gabbro.Grammatik.Extraktion.execEreignis_aus_axiomCall
#print axioms Gabbro.Grammatik.Extraktion.hmark_hcar_aus_progAus_axiomCall

/-! ## 19. The hwit discharger: fired steps produce their zugriff events

    What `Ziel.lean` §10 books as its two remaining witness duties: the step
    witness (`hneu_wit`: the fired leaf's `neu` carries the `zugriff` event
    when the code writes the carrier) and the prefix witness (`hwit_old`:
    the old run's accesses are still posited, as scheduler duty). This
    section discharges the step duty at its source -- production by
    construction -- and names the induction base for the prefix duty.
    Read-only use of the §17 event shapes and the `execStmt` neu-event
    constructions (`schreibSlot`, `schreibBytes`, the taken `uebergang`
    branch); nothing existing moves.

    * `hwit_aus_feuerung_ohne_axiomCall` is the producer: a fired non-oracle
      leaf whose written carrier is the tracked table `t₀` (read as
      `.inl t₀ ∈ stmtTraeger tabs globs s`, §14) leaves a `zugriff` event
      for `t₀` in `neu` -- the write the `execStmt` shape puts there by
      construction. The `hneu_wit` duty of `kette_mit_zeugen[_orakel]` is
      then `fun _ => hwit_aus_feuerung_ohne_axiomCall ...`: the code
      predicate is vacuous once the leaf produces -- the event exists
      whenever the writing leaf fires, with `w = true` and the statement
      `Λ`.
    * `hwit_leer` is the prefix base: with no thread steps owed, no witness
      is owed -- the duty holds vacuously over any run. The induction step
      is the read-only `kette_mit_zeugen_schritt` link construction
      (`Ziel.lean` §10): old steps inherit from the package, the new
      writing step rides `genEigen_wit_index` on exactly the event produced
      here.

    Coverage (exactly): non-oracle leaves writing the tracked TABLE carrier
    (`assignSlot`, `assignDurch`, `uebergang`, `schreibBytes` with `0 < n`
    via `hbytes`); every premise is load-bearing (`hbytes` feeds the byte
    case, `hax` kills the oracle case, `hleaf` kills the compounds, `hmem`
    names the carrier in every other case).

    Remainder (booked, not hidden): `axiomCall` leaves (the oracle adds no
    events under `GutO`, §18 -- closing them needs the per-event oracle
    contract, same class as the S13 remainder); empty `schreibBytes`
    (`n = 0` writes nothing though the carrier is declared); leaves that
    write no table (`assignGlob`, `publish`, reads, terminals -- no table
    event exists to produce); globals (`gzugriff`, as `Ziel.lean` §10
    books); the full-run fold of the prefix duty over `PCReach`
    derivations (base here, step read-only, induction unwritten).
-/

/-- A fired non-oracle leaf that writes the tracked table produces its
    witness: `neu` carries a `zugriff` event for `t₀` (with `w = true` and
    the statement `Λ`). The byte writer needs `0 < n` (`hbytes`); `hstep`
    forces the taken `uebergang` branch, as in §17. -/
theorem hwit_aus_feuerung_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (t₀ : D.Tab) (hmem : .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes : match s with | .putBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
      Ereignis.zugriff t₀ w Λw hwL ∈ neu := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
          (i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      refine ⟨true, Λ, (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  | assignThru p t ht f i e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] ++
          (p.orte ++ i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      refine ⟨true, Λ, (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  | assignSlotRef r t ht ho f e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (r.orte ++ e.orte)).haelt] ++
          (r.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      refine ⟨true, Λ, (σ.lese Λ (r.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  | assignGlob g e hw hL =>
      simp [stmtTraeger] at hmem
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          List.replicate (zahlZuBytes n
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length
            (Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt) ++
          ((i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur) := by
        rw [← hstep, schreibBytes_spur_eq]; rfl
      rw [hspur, ← List.append_assoc] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      have hlen : (zahlZuBytes n
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length = n :=
        zahlZuBytes_length n _
      refine ⟨true, Λ, (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr
        (Or.inl (List.mem_replicate.mpr ⟨by rw [hlen]; omega, rfl⟩))
  | assignVar x e =>
      simp [stmtTraeger] at hmem
  | shift t f hτ i von nach hn he hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt] at hstep
      split at hstep
      · simp only [Ausgang.welt, Option.some.injEq] at hstep
        have hspur : σ'.spur =
            [Ereignis.zugriff t true Λ (σ.lese Λ (.inl t :: i.orte)).haelt] ++
            (.inl t :: i.orte).map (fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
          rw [← hstep]; rfl
        rw [hspur] at hneu
        have hneueq := List.append_cancel_right hneu
        subst hneueq
        refine ⟨true, Λ, (σ.lese Λ (.inl t :: i.orte)).haelt, ?_⟩
        rw [hteq]
        exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
      · simp only [Ausgang.welt] at hstep
        simp at hstep
  | ite c t e => simp [Stmt.istBlatt] at hleaf
  | onOption o p a => simp [Stmt.istBlatt] at hleaf
  | onTag v arms => simp [Stmt.istBlatt] at hleaf
  | onWhy r arms => simp [Stmt.istBlatt] at hleaf
  | call f args hp hr => simp [Stmt.istBlatt] at hleaf
  | callInd p args hp hr => simp [Stmt.istBlatt] at hleaf
  | locks L hr body => simp [Stmt.istBlatt] at hleaf
  | breaking i body => simp [Stmt.istBlatt] at hleaf
  | traverse t inv body => simp [Stmt.istBlatt] at hleaf
  | retry n bis body ueberlauf => simp [Stmt.istBlatt] at hleaf
  | forever a inv body => simp [Stmt.istBlatt] at hleaf
  | axiomCall a args h hw hg hd hgd => exact False.elim hax
  | regWrite r hk e =>
      simp [stmtTraeger] at hmem
  | transition r hk m hm hl maske bits =>
      simp [stmtTraeger] at hmem
  | publish g e payload hp hw hL =>
      simp [stmtTraeger] at hmem
  | advances m a h hs =>
      simp [stmtTraeger] at hmem
  | retires m s h a =>
      simp [stmtTraeger] at hmem
  | ret e hΛ =>
      simp [stmtTraeger] at hmem
  | retWhy r hΛ =>
      simp [stmtTraeger] at hmem
  | leave h =>
      simp [stmtTraeger] at hmem
  | next h =>
      simp [stmtTraeger] at hmem

/-- The prefix base: with no thread steps owed, no witness is owed -- the
    witness duty holds vacuously over any run. `hempty` types the
    contradiction; `run`/`t₀` type the conclusion. -/
theorem hwit_leer (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (t₀ : D.Tab) (hempty : J.schrittFaden = []) :
    ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  intro k g hk _
  rw [hempty] at hk
  simp at hk

#print axioms Gabbro.Grammatik.Extraktion.hwit_aus_feuerung_ohne_axiomCall
#print axioms Gabbro.Grammatik.Extraktion.hwit_leer

/-! ## 20. The hwit prefix fold over whole `PCReach` runs

    What `Ziel.lean` section 10 books as the prefix witness duty (`hwit_old`:
    the old run's accesses are still posited, as scheduler duty) is folded here
    over whole `PCReach` derivations: the empty prefix holds vacuously
    (read-only `hwit_leer`, section 19), each non-oracle leaf step produces its
    witness by construction (read-only `hwit_aus_feuerung_ohne_axiomCall`,
    section 19, transported into the extended run), and each lock step inherits
    the posited prefix witness (`hwit_lock`, the same shape
    `MaschinenKette.kette_aus_lauf_bezeugt` posits). Nothing existing moves.

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `hwit_alt_transport` (list only): an event of `neu` sits in the extended
      run `lauf ++ genEigen f neu` at a computed index. It is proved locally:
      the same transport lives in `Ziel.lean` (`genEigen_wit_index`), which
      imports this file and hence cannot be reused here. Every premise is
      load-bearing: `he` yields the index, `lauf`/`f`/`neu` type the
      conclusion.
    - `hwit_alt_schritt`: one-step prefix extension. A duty over
      (`schrittFaden`, `lauf`) plus a witness for the acting thread inside
      the extended run yields the duty over (`schrittFaden ++ [f]`,
      `lauf ++ genEigen f neu`): old entries inherit through the left append
      leg, the new entry is exactly the supplied witness, past-the-end indices
      are impossible. Every premise is load-bearing.
    - `hwit_alt_faltung`: the fold over whole `PCReach` derivations. The
      scheduler steps accumulate as a bare list (`[]` at `start`, discharged
      by `hwit_leer` over a posited empty joint run, `++ [f]` per step);
      counter routing (`hsingle_prog`) rules out foreign steps; every fired
      leaf meets the producer premises (`hax_all`/`hmem_all`/`hbytes_all`
      feed exactly `hwit_aus_feuerung_ohne_axiomCall`, nothing else);
      lock steps inherit the posited prefix witness (`hwit_lock`).
      Every premise is load-bearing, and there is no `have _ :=` discard.

    Coverage (exactly): single-thread `PCReach` runs whose every fired leaf
    is a non-oracle leaf writing the tracked TABLE carrier `t₀` (with `0 < n`
    for `schreibBytes`), plus lock steps whose witness the prefix already
    records.

    Remainder (booked, not hidden): `axiomCall` leaves (the oracle adds no
    events under `GutO`, same class as the section-19 remainder -- `hax_all`
    marks exactly this fragment); leaves that write no table and empty
    `schreibBytes` (no event exists to produce, so `hmem_all`/`hbytes_all`
    cannot hold for them); globals (`gzugriff`); the seed joint run `J₀`
    (the glue that instantiates the fold supplies it); multi-thread runs.
-/

/-- List-level witness transport: an event of `neu` sits in the extended run
    `lauf ++ genEigen f neu` at index `lauf.length + i`, where `i` is its
    index in `neu.reverse` (the order `genEigen` maps over). Every premise is
    load-bearing: `he` yields the index, `lauf`/`f`/`neu` type the
    conclusion. -/
theorem hwit_alt_transport (lauf : Lauf D) (f : Faden) (neu : List (Ereignis D))
    (e : Ereignis D) (he : e ∈ neu) :
    ∃ (j : Nat), (lauf ++ genEigen f neu)[j]? = some (Schritt.mk f e) := by
  have hmem : e ∈ neu.reverse := List.mem_reverse.mpr he
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨lauf.length + i, ?_⟩
  have hmap : (genEigen f neu)[i]? = some (Schritt.mk f e) := by
    simp only [genEigen, List.getElem?_map, List.getElem?_eq_getElem hi, hget,
      Option.map_some]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  have hsub : lauf.length + i - lauf.length = i := by omega
  rw [hsub]
  exact hmap

#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_transport

/-- One-step prefix extension: a witness duty over (`schrittFaden`, `lauf`)
    plus a witness for the acting thread `f` inside the extended run yields
    the duty over (`schrittFaden ++ [f]`, `lauf ++ genEigen f neu`). Old
    entries inherit from the prefix duty through the left append leg, the new
    entry is the supplied witness, past-the-end indices are impossible. Every
    premise is load-bearing: `hold` closes the old entries, `hnew` closes the
    new one, the rest type the conclusion. -/
theorem hwit_alt_schritt
    (code : Faden → D.Fn)
    (schrittFaden : List Faden) (lauf : Lauf D)
    (f : Faden) (neu : List (Ereignis D)) (t₀ : D.Tab)
    (hold : ∀ (k : Nat) (g : Faden), schrittFaden[k]? = some g →
      TraegerSchreibt (code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hnew : TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        (lauf ++ genEigen f neu)[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he))) :
    ∀ (k : Nat) (g : Faden), (schrittFaden ++ [f])[k]? = some g →
      TraegerSchreibt (code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        (lauf ++ genEigen f neu)[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  intro k g hk hwr
  by_cases hlt : k < schrittFaden.length
  · have eOld : (schrittFaden ++ [f])[k]? = schrittFaden[k]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk
    obtain ⟨j, w, Λe, he, hw⟩ := hold k g hk hwr
    have hjlt : j < lauf.length := by
      by_cases h : j < lauf.length
      · exact h
      · have hle : lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp at hw
    refine ⟨j, w, Λe, he, ?_⟩
    rw [List.getElem?_append_left hjlt]
    exact hw
  · by_cases heq : k = schrittFaden.length
    · subst heq
      have eNew : (schrittFaden ++ [f])[schrittFaden.length]? = some f := by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [eNew] at hk
      have hg : g = f := (Option.some_inj.mp hk).symm
      subst hg
      exact hnew hwr
    · have hle : schrittFaden.length ≤ k := by omega
      have eNone : (schrittFaden ++ [f])[k]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk
      simp at hk

#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_schritt


end Gabbro.Grammatik.Extraktion
