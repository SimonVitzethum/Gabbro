/- Part 3 of 3 of `FremdRuf` (split by instrumente/teile/lean-teilen.py; the umbrella `FremdRuf.lean` imports all parts). -/
import Grammatik.Logik.Ruf.FremdRuf.T2

namespace Gabbro.Grammatik

/-- The caller's obligation over a whole sequence: every call meets its gate's
    precondition in the world the sequence has reached there. Stated over the
    machine's oracle's worlds; the coincidence below says the re-dressed
    oracle reaches the same ones. -/
def RufFolgePflicht {D : Deklaration} (Pre : AxPre D) (O : Orakel D) : World D →
    List (Σ a : D.Ax, Env D (D.aparams a)) → Prop
  | _, [] => True
  | σ, ⟨a, ρ⟩ :: rest =>
    Pre a σ ρ = true ∧ RufFolgePflicht Pre O (O.wirkt a σ ρ).1 rest

/-- **Run-level coincidence at the oracle layer.** Under the caller's obligation
    at every call of the sequence, folding the re-dressed oracle gives the same
    worlds and raw answers as folding the machine's oracle. Induction over the
    sequence with the single-call coincidence (`mitVorbedingung_gleich`) at the
    head: the head call agrees, so both folds reach the same world, and the
    tail obligation -- stated over the machine's worlds -- is the induction
    hypothesis. Every premise is used: `h` gives the head obligation and the
    tail, `e` the head agreement. -/
theorem mitVorbedingung_folge_gleich {D : Deklaration} (Pre : AxPre D) (O : Orakel D)
    (raus : D.Ax → Int) (σ : World D) (ks : List (Σ a : D.Ax, Env D (D.aparams a)))
    (h : RufFolgePflicht Pre O σ ks) :
    rufFolgeWirkt (mitVorbedingung Pre O raus) σ ks = rufFolgeWirkt O σ ks := by
  induction ks generalizing σ with
  | nil => rfl
  | cons k rest ih =>
    obtain ⟨a, ρ⟩ := k
    have e := mitVorbedingung_gleich Pre O raus a σ ρ h.1
    have t := ih _ h.2
    simp only [rufFolgeWirkt, e, t]

/-- The witness sequence: open at the start world, then read with the handed-out
    descriptor `3` in the world the open answered. -/
def fdFolge : List (Σ a : fdD.Ax, Env fdD (fdD.aparams a)) :=
  [⟨fdOpen, Env.nil⟩, ⟨fdRead, fdRho3⟩]

/-- The open gate's precondition holds at the start world (the terminator stands). -/
theorem fdFolge_offen_pflicht : AufruferPflicht fdPre fdOpen fdWelt0 Env.nil := by
  show decide ((fdWelt0.slots () 1 ()).n = 0) = true
  exact decide_eq_true rfl

/-- The read gate's precondition holds after the open (descriptor `3` handed out). -/
theorem fdFolge_lesen_pflicht :
    AufruferPflicht fdPre fdRead (fdObad.wirkt fdOpen fdWelt0 Env.nil).1 fdRho3 := by
  show decide (fdKopf fdRho3 = 3) = true
  exact decide_eq_true rfl

/-- ZEUGE for the sequence coincidence: its premises hold jointly on the fixture
    with the BAD oracle -- the open's precondition at the start world, the read's
    after the open -- so both folds agree on the two-call sequence. Non-degenerate
    in the file's sense: the same oracle breaks the full premise
    (`fdObad_nicht_voll`), and the program `fdP` writes the table on a reached
    run (`fdPC_schreibt`). -/
theorem mitVorbedingung_folge_gleich_zeuge :
    RufFolgePflicht fdPre fdObad fdWelt0 fdFolge ∧
    rufFolgeWirkt (mitVorbedingung fdPre fdObad fdRaus) fdWelt0 fdFolge =
      rufFolgeWirkt fdObad fdWelt0 fdFolge :=
  ⟨⟨fdFolge_offen_pflicht, fdFolge_lesen_pflicht, trivial⟩,
    mitVorbedingung_folge_gleich fdPre fdObad fdRaus fdWelt0 fdFolge
      ⟨fdFolge_offen_pflicht, fdFolge_lesen_pflicht, trivial⟩⟩

/-! ## CUTS: what is not proved.

  - The dispatch labels, register bindings and costs of `GateData`
    are uninterpreted: no theorem connects them to emitted code. That
    is the emitter's stub contract (PLAN-SYSCALL.md S6), not the
    model's. The model shows they constrain no answer and no memory
    step (`fremdruf_gate_gilt`, `fremdruf_offen_lesen` never consult
    `num`, `regs` or `kosten`).
  - The kernel side is a hypothesis, not a verification: there is no
    pairing with a proved dispatch entry (that is `SyscallPaarung`),
    only the oracle-side reading of premise (c) for gates.
  - The reached run fires a plain writing leaf, not a gate call: the
    gate calls appear as oracle answers at concrete call sites
    (`fdFitO`, `fdFitR`), not as machine steps. A run stepping
    through `bindAxiom` would need the F-machine residue shape.
  - The fixture is narrower than lane 226's example 150 (review G10):
    no `opaque type Fd = u32` (the descriptor is `.int 0 7`), no
    `buf : ptr`/`len` parameters, and the witness read gate writes no
    memory. Widening it was not cheap (every environment and fit above
    names the one-parameter read) and was not done in fix lane F5.
   - Argument preconditions (section 9, fix lane F5): the split premise
     (`AxVertragOP` + the caller's `AufruferPflicht`) and the bridge
     (`hardware_aus_vertragP`) are proved; `gabbro_ziel`'s premise (c)
     is UNCHANGED (`AxVertragO` over every argument) and `Spec.lean` is
     untouched. Section 10 (lane 262) lifts the coincidence from one call to
     call SEQUENCES at the oracle layer (`mitVorbedingung_folge_gleich` over
     `rufFolgeWirkt` under `RufFolgePflicht`): under the caller's obligation
     at every call site both oracles reach the same worlds with the same raw
     answers. What is NOT proved: that a run in which every gate call
     meets its precondition is the same run under the machine's oracle
     and under the re-dressed one at the MACHINE level -- no `Stmt`, no
     `execStmt`, no `bindAxiom` is involved here, and a run stepping through
     gate calls would need the F-machine residue shape; no Rust exporter
     produces `AxPre` from a gate's `requires`; the bridge needs a raw word
     outside every declared result type (`hraus`), which a gate without a
     result (`aerg = none`) does not have; and the fixture's preconditions
     (a terminator slot, the handed-out descriptor) are analogs of example
     149's `path_nul_terminated` and example 150's `len <= lenof(buf)`, not
     those clauses.
   - The fixture is narrower than example 150 (review G10, lane 262 verdict:
     widening was NOT cheap and was not done): no `opaque type Fd = u32`
     (the descriptor is `.int 0 7`), no `buf : ptr`/`len` parameters, and the
     witness read gate writes no memory. A `buf`/`len` read gate needs a third
     `Ax` value (today `Ax := Bool` with its two gates), which changes every
     environment and fit in the file; an opaque descriptor needs the language
     opacity the model does not carry (review G10). The sequence section (§10)
     reuses the two-gate shape unchanged.
  - The planted-defect check: `fremdruf_falsch_abgelehnt` proves the
    negation (an ensures demanding `6` is refused); the positive
    attempt `AxVertragO fdQfalsch fdO` fails at the `3 = 6`
    obligation (see MUSE-REPORT-233.md for the failure line).
-/

#print axioms Gabbro.Grammatik.gate_daten_gleich
#print axioms Gabbro.Grammatik.fdO_gut
#print axioms Gabbro.Grammatik.fdQ_vertrag
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt
#print axioms Gabbro.Grammatik.fremdruf_offen_lesen
#print axioms Gabbro.Grammatik.fd_opak
#print axioms Gabbro.Grammatik.fremdruf_falsch_abgelehnt
#print axioms Gabbro.Grammatik.fdPC_erreicht
#print axioms Gabbro.Grammatik.fdPC_schreibt
#print axioms Gabbro.Grammatik.fremdruf_fd_zeuge
#print axioms Gabbro.Grammatik.fremdruf_offen_lesen_zeuge
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt_zeuge
#print axioms Gabbro.Grammatik.axVertragOP_of_O
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt_pre
#print axioms Gabbro.Grammatik.mitVorbedingung_gleich
#print axioms Gabbro.Grammatik.hardware_aus_vertragP
#print axioms Gabbro.Grammatik.fdObad_vertragP
#print axioms Gabbro.Grammatik.fdObad_nicht_voll
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt_pre_zeuge
#print axioms Gabbro.Grammatik.hardware_aus_vertragP_zeuge
#print axioms Gabbro.Grammatik.mitVorbedingung_folge_gleich
#print axioms Gabbro.Grammatik.fdFolge_offen_pflicht
#print axioms Gabbro.Grammatik.fdFolge_lesen_pflicht
#print axioms Gabbro.Grammatik.mitVorbedingung_folge_gleich_zeuge


end Gabbro.Grammatik
