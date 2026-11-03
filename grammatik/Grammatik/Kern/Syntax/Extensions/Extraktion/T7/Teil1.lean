module

public import Grammatik.Kern.Syntax.Extensions.Extraktion.T7.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Extraktion
variable {D : Deklaration}

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
    rcases hlam e he with hl | hl
    · rw [hl, ← hΛa] at hm
      exact pcAtom_mem_marks _ _ _ ha m
        (by simp only [PCAtom.marks]
            exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩)
    · rw [hl] at hm
      exact absurd hm List.not_mem_nil
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

end Gabbro.Grammatik.Extraktion
