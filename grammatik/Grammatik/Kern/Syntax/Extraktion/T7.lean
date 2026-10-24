/- Part 7 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T6

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- A fired non-oracle leaf step carries exactly its statement footprint:
    every new event names the statement `Λ`, and every carrier it touches
    sits in the written carrier plus the `stmtOrte` read hull. `axiomCall`
    is excluded: the oracle (`O.wirkt`) answers with an arbitrary world, so
    its events carry arbitrary `Λ`/carriers (remainder S13 below). -/
theorem execEreignis_aus_blatt_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    (∀ e ∈ neu, e.lambda = Λ) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs s ++ stmtOrte s) := by
  cases s with
  | assignSlot t f i e hw hL =>
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
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignThru p t ht f i e hw hL =>
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
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ p.orte ++ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignSlotRef r t ht ho f e hw hL =>
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
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ r.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.gzugriff g true Λ (σ.lese Λ e.orte).haelt] ++
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | putBytes t f hf n i hlo hhi e hw hL =>
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
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · have heq : e' =
              Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt :=
            (List.mem_replicate.mp h1).2
          rw [heq]
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · have heq : e' =
              Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt :=
            (List.mem_replicate.mp h1).2
          rw [heq] at ho
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | shift t f hτ i von nach hn he hw hL =>
      exact uebergang_ereignis_aus_blatt O passes l tabs globs t f hτ i von nach
        hn he hw hL σ ρ σ' neu hstep hneu
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
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.gzugriff g true Λ (σ.lese Λ e.orte).haelt] ++
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | advances m a h hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | retires m s h a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | ret e hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | retWhy r hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | leave h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | next h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'

/-- The `PCSchritt` footprint checks discharged against `progAus` atoms: a
    fired non-oracle leaf step whose counter points at its extracted atom
    names only that atom's marks and touches only its carriers -- hence the
    thread's program text (`pcAtom_mem_marks`/`pcAtom_mem_carriers`). The
    atom-identity premise (`hcs`) is the scheduler/witness duty: the counter
    must point at the atom `stmtAtome_blatt_eq` yields for `s` (remainder S12 below). -/
theorem hmark_hcar_aus_progAus_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (M : GenMaschine D) (f : Faden) (ρ : Env D Γ)
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ (M.weltVon f).spur)
    (pc : PCStand) (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (progAus P code tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = stmtTraeger tabs globs s ++ stmtOrte s) :
    (∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda →
      m ∈ (progAus P code tabs globs).marks f) ∧
    (∀ e ∈ neu, ∀ o, e.traeger = some o →
      o ∈ (progAus P code tabs globs).carriers f) := by
  obtain ⟨hlam, hcar⟩ :=
    execEreignis_aus_blatt_ohne_axiomCall O passes s hleaf hax tabs globs
      _ ρ σ' neu hstep hneu
  have ha : PCAtom.leaf Λa cs ∈ progAus P code tabs globs f :=
    List.mem_of_getElem? hpc
  constructor
  · intro e he m st hm
    rw [hlam e he] at hm
    rw [← hΛa] at hm
    exact pcAtom_mem_marks _ _ _ ha m
      (by simp only [PCAtom.marks]
          exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩)
  · intro e he o ho
    have hmem : o ∈ stmtTraeger tabs globs s ++ stmtOrte s := hcar e he o ho
    apply pcAtom_mem_carriers _ _ _ ha o
    simp only [PCAtom.carriers]
    rw [hcs]
    exact hmem

#print axioms Gabbro.Grammatik.Extraktion.mem_leseEr
#print axioms Gabbro.Grammatik.Extraktion.rep_append_single
#print axioms Gabbro.Grammatik.Extraktion.schreibBytes_spur_eq
#print axioms Gabbro.Grammatik.Extraktion.uebergang_ereignis_aus_blatt
#print axioms Gabbro.Grammatik.Extraktion.execEreignis_aus_blatt_ohne_axiomCall
#print axioms Gabbro.Grammatik.Extraktion.hmark_hcar_aus_progAus_ohne_axiomCall

/-! ## 18. The oracle bound: event characterization for `axiomCall` leaves

    (Closes the S13 remainder of §17 for the bounded-oracle fragment.)

    The contract is the tree's own named oracle bound, `GutO` (`Satz.lean`):
    for every axiom, entry world, and environment, the oracle answer respects
    the declared footprint (`Rahmen (D.aschreibt a) (D.agschreibt a)`) and keeps
    the held locks; in worlds where the axiom's lock guards are held it
    records its declared writes as `axiomSpur` events over its own domains
    (with a mark-free guard trace `Λe` it holds). It
    travels as a hypothesis -- the `dma_inhalt` class (`Geraet.lean`): a NAMED
    assumption, never derived here, never an axiom.

    Under that bound a fired `axiomCall` leaf emits its argument reads plus
    the oracle's recorded writes: `neu` is the `axiomSpur` prefix over the
    `args.orte` read prefix (`mem_leseEr`); reads name the statement `Λ`,
    writes name the oracle's mark-free `Λe`, and every carrier touched sits
    in the declared writes (over the caller's domains, via completeness) plus
    the read hull (`stmtTraeger ++ stmtOrte`).

    * `execEreignis_aus_axiomCall` is the characterization per oracle leaf.
    * `hmark_hcar_aus_progAus_axiomCall` discharges the `PCSchritt`
      footprint checks (`hmark`/`hcar`) against `progAus` atoms for oracle
      leaves -- the `hmark_hcar_aus_progAus_ohne_axiomCall` shape with the
      contract premise (`hO`) in place of the exclusion premise (`hax`), plus
      the domain-completeness premises (the oracle's writes land in the
      extracted atom only over domains covering them).
      The proof consumes the `GutO` witness domains; `Rahmen` and `haelt`
      ride along as the value-side bound (used by `stmt_gut`, harmless here).

    Remainder (booked, not hidden): the caller-side domain completeness
    (`hct`/`hcg` -- the extracted `tabs`/`globs` cover the axiom's declared
    writes). Same class, scheduler-side duty, carried explicitly.
-/

/-- A fired oracle leaf step carries its argument reads plus the oracle's
    recorded writes, under the recording oracle bound: the oracle (`O.wirkt`)
    answers with its declared write events (`axiomSpur` over its own domains,
    `GutO`), so every new event names the statement `Λ` (a read) or the
    oracle's `Λe` (a write, mark-free by `GutO`), and every carrier it touches
    sits in the declared writes (over the caller's domains, hence the
    completeness premises) plus the `args.orte` read hull. -/
theorem execEreignis_aus_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hO : GutO O)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hct : ∀ t, D.aschreibt a t = true → t ∈ tabs)
    (hcg : ∀ g, D.agschreibt a g = true → g ∈ globs)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hh : HeldGenau Λ σ.haelt)
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    ∃ Λe : List (Res D),
      (∀ m st, Res.marke m st ∉ Λe) ∧
      (∀ e ∈ neu, e.lambda = Λ ∨ e.lambda = Λe) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs
          (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
          stmtOrte
            (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ)) := by
  have hhaelt : (σ.lese Λ args.orte).haelt = σ.haelt := lese_haelt _ _ _
  have hhL : HeldGenau Λ (σ.lese Λ args.orte).haelt := by
    rw [hhaelt]
    exact hh
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
      L ∈ (σ.lese Λ args.orte).haelt :=
    fun t hwr L hL => (hhL L).mp (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
      L ∈ (σ.lese Λ args.orte).haelt :=
    fun g hwr L hL => (hhL L).mp (hgd g hwr _ hL)
  obtain ⟨_, _, hcond⟩ := hO a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
  obtain ⟨tabs₀, globs₀, Λe, _, _, _, _, hmf₀, _, hspurO⟩ := hcond hgt hgg
  simp only [execStmt] at hstep
  split at hstep
  · rename_i σ1 v ha
    simp only [Ausgang.welt, Option.some.injEq] at hstep
    subst hstep
    have hσ1 : σ1 = (O.wirkt a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 := by
      have hfst := congrArg Prod.fst ha
      simp only [axiomAntwort] at hfst
      exact hfst.symm
    have hlese : (σ.lese Λ args.orte).spur =
        (args.orte.map fun o => match o with
          | .inl t => Ereignis.zugriff t false Λ σ.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := rfl
    rw [hσ1, hspurO, hlese, ← List.append_assoc] at hneu
    have hneueq : axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
        (args.orte.map fun o => match o with
          | .inl t => Ereignis.zugriff t false Λ σ.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ.haelt) = neu :=
      List.append_cancel_right hneu
    subst hneueq
    refine ⟨Λe, hmf₀, ?_, ?_⟩
    · intro e he
      rw [List.mem_append] at he
      rcases he with hor | hrd
      · rcases axiomSpur_mem hor with ⟨t, _, _, rfl⟩ | ⟨g, _, _, rfl⟩
        · exact Or.inr rfl
        · exact Or.inr rfl
      · exact Or.inl (mem_leseEr hrd).1
    · intro e he o ho
      rw [List.mem_append] at he
      rcases he with hor | hrd
      · rcases axiomSpur_mem hor with ⟨t, _, hwr, rfl⟩ | ⟨g, _, hwr, rfl⟩
        · have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          rw [ho']
          simp only [stmtTraeger, stmtOrte]
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_map.mpr
          exact ⟨t, List.mem_filter.mpr ⟨hct t hwr, hwr⟩, rfl⟩
        · have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          rw [ho']
          simp only [stmtTraeger, stmtOrte]
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_append.mpr; apply Or.inr
          apply List.mem_map.mpr
          exact ⟨g, List.mem_filter.mpr ⟨hcg g hwr, hwr⟩, rfl⟩
      · have hmem : o ∈ args.orte := (mem_leseEr hrd).2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  · simp [Ausgang.welt] at hstep


end Gabbro.Grammatik.Extraktion
