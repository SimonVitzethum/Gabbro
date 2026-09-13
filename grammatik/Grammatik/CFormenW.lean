/-
  File:      Grammatik/CFormenW.lean
  Subject:   T4, the `retry` loop: which side is right, the corrected model
             definition `retryLaufC`, exactly where it differs from
             `retryLauf`, and the correspondence of the emitted loop.

  THE EMITTED LOOP (emit.rs `fn retry`, read 2026-09-13 at 9552ff.)

      {
          uint32_t _rT = 0;
          for (; !(bis) && _rT < Nu; _rT += 1) {
              body
              [m_weiter: ;]
          }
          if (_rT >= Nu && !(bis)) { ausgang(); }
      }
      [m_ende: ;]

  `N` is the pass count the `bounded … ops` budget yields, `ausgang` the
  `on_exceeded` function, which the emitter requires to return `never`.

  THE FINDING (previous pass, CFormenI.lean CUTS) AND ITS DECISION
    Gabbro's `retryLauf` (Semantik.lean 446) runs the overflow block as
    soon as the budget is spent: `retryLauf … 0 σ ρ = ueberlauf σ ρ`,
    without looking at `bis`. The emitted C evaluates `bis` once more
    after the last pass (the loop header, then the check after the loop):
    a pass that makes the condition true is a SUCCESS there. The emitter's
    comment says this is deliberate ("the bound arm leaves the loop and
    stands after it … `if (z >= N && !(cond))`"), and it is what the
    source means: `retry until p bounded N` promises that `p` holds when
    the loop is left normally, and after the N-th pass `p` may hold.

    DECISION: the model moves, not the emitter. The one definition that
    must change is `retryLauf`'s `0` case in `Grammatik/Semantik.lean`:

        | 0, σ, ρ => ueberlauf σ ρ
    becomes
        | 0, σ, ρ => if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ
                     else ueberlauf (bis σ ρ).1 ρ

    That is `retryLaufC` below (`retryLaufC_eq`: it IS `retryLauf` with
    the overflow block guarded by one more check, `ueberC`). Semantik.lean
    is the sequential semantics other lanes are editing; this file does
    not touch it. `retryLauf_C_gleich` / `retryLauf_C_erschoepft` say
    exactly where the two differ: only at the state where the budget is
    spent, and there only if `bis` holds (a success in C, the overflow
    block in the model) -- or, if `bis` does not hold, by the read of
    `bis` itself (the overflow block starts from the world that recorded
    the read). `retry_unterschied_zeuge` (CFormenWZeuge.lean) is a run
    where they differ.

    Why the model's side does not break correspondence today: the emitter
    admits only a `never` overflow (a foreign exit, a hardware-assumption
    outcome in Gabbro, an error with no C obligation). So wherever the two
    definitions differ, the MODEL reports an error run and the C succeeds:
    the model is stricter than the program, never weaker
    (`scorr_retry`, the correspondence against the real `execStmt`, under
    exactly that premise). What the model loses is precision: a checker
    that must prove the overflow unreachable proves more than the C
    needs.

  WHAT THE C MODEL OF THE LOOP IS (`retryCS`)
    `.set z 0; forC (!(cb) && z < N) (z = z + 1) body m'; if (z >= N &&
    !(cb)) cexc else skip`. Two modelling notes:
    * `m_ende:` stands after the check in the C, so a `leave` jumps past
      it; in `CS`, the loop consumes `goto m'_ende` and the check runs.
      The check is then `z >= N` with `z < N` (a `leave` ends a pass
      before the increment) -- false, and `&&` does not evaluate `bis`:
      the same effect, proved, not assumed (the `leave` case of
      `retryC_run`).
    * `bis` is evaluated twice on the bound path (the header, then the
      check). Under `ExprCorr` both evaluations give the same value
      (expressions change no memory, `ev_same`); a condition that reads a
      device register (the corpus's usual `retry`: `until g.fertig == 1`)
      has no `ExprCorr` (device reads are per-step lemmas, H9), so those
      loops are outside this lemma. The corpus's pure conditions:
      `beispiele/66` (`until bereit`), `beispiele/42` (`until stand >= 1`).
-/
import Grammatik.CFormenH

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The corrected definition and where it differs -/

section Lauf

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- THE CORRECTED `retry` RUN: `retryLauf` with the check of `bis` after
    the last pass (the emitted C's `if (z >= N && !(bis))`). -/
def retryLaufC (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ) :
    Nat → World D → Env D Γ → Ausgang V l Γ
  | 0, σ, ρ => if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ else ueberlauf (bis σ ρ).1 ρ
  | n + 1, σ, ρ =>
      if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ else
      match schritt (bis σ ρ).1 ρ with
      | .ok σ' ρ' => retryLaufC schritt bis ueberlauf n σ' ρ'
      | .next _ σ' ρ' => retryLaufC schritt bis ueberlauf n σ' ρ'
      | .leave _ σ' ρ' => .ok σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- The overflow block guarded by one more check of `bis`. -/
def ueberC (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) : World D → Env D Γ → Ausgang V l Γ :=
  fun σ ρ => if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ else ueberlauf (bis σ ρ).1 ρ

/-- THE CHANGE, AS ONE EQUATION: the corrected run is the model's run with
    the overflow block replaced by `ueberC` -- nothing else differs. -/
theorem retryLaufC_eq (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueb : World D → Env D Γ → Ausgang V l Γ) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      retryLaufC schritt bis ueb n σ ρ = retryLauf schritt bis (ueberC bis ueb) n σ ρ
  | 0, _, _ => rfl
  | n + 1, σ, ρ => by
      simp only [retryLaufC, retryLauf]
      split
      · rfl
      · cases schritt (bis σ ρ).1 ρ with
        | ok σ' ρ' => exact retryLaufC_eq schritt bis ueb n σ' ρ'
        | next h σ' ρ' => exact retryLaufC_eq schritt bis ueb n σ' ρ'
        | leave h σ' ρ' => rfl
        | zurueck σ' v => rfl
        | grund σ' r => rfl
        | logik e => rfl
        | hardware e => rfl

/-- Where the budget runs out: the state after the last pass, if the run
    gets there (no early success, no `leave`, `return` or error). -/
def retryErschoepft (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) :
    Nat → World D → Env D Γ → Option (World D × Env D Γ)
  | 0, σ, ρ => some (σ, ρ)
  | n + 1, σ, ρ =>
      if (bis σ ρ).2 = true then none else
      match schritt (bis σ ρ).1 ρ with
      | .ok σ' ρ' => retryErschoepft schritt bis n σ' ρ'
      | .next _ σ' ρ' => retryErschoepft schritt bis n σ' ρ'
      | _ => none

/-- WHERE THEY AGREE: every run that does not spend the budget is the same
    run in both definitions. -/
theorem retryLauf_C_gleich (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueb : World D → Env D Γ → Ausgang V l Γ) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), retryErschoepft schritt bis n σ ρ = none →
      retryLaufC schritt bis ueb n σ ρ = retryLauf schritt bis ueb n σ ρ
  | 0, _, _, h => by simp [retryErschoepft] at h
  | n + 1, σ, ρ, h => by
      simp only [retryErschoepft] at h
      simp only [retryLaufC, retryLauf]
      split
      · rfl
      · rename_i hb
        rw [if_neg hb] at h
        cases hs : schritt (bis σ ρ).1 ρ with
        | ok σ' ρ' =>
            rw [hs] at h
            exact retryLauf_C_gleich schritt bis ueb n σ' ρ' h
        | next hn σ' ρ' =>
            rw [hs] at h
            exact retryLauf_C_gleich schritt bis ueb n σ' ρ' h
        | leave hl σ' ρ' => rfl
        | zurueck σ' v => rfl
        | grund σ' r => rfl
        | logik e => rfl
        | hardware e => rfl

/-- WHERE THEY DIFFER: at the state where the budget is spent, the model
    runs the overflow block, the corrected run checks `bis` first. -/
theorem retryLauf_C_erschoepft (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueb : World D → Env D Γ → Ausgang V l Γ) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ0 : World D) (ρ0 : Env D Γ),
      retryErschoepft schritt bis n σ ρ = some (σ0, ρ0) →
      retryLauf schritt bis ueb n σ ρ = ueb σ0 ρ0 ∧
        retryLaufC schritt bis ueb n σ ρ = ueberC bis ueb σ0 ρ0
  | 0, σ, ρ, σ0, ρ0, h => by
      simp only [retryErschoepft, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | n + 1, σ, ρ, σ0, ρ0, h => by
      simp only [retryErschoepft] at h
      simp only [retryLaufC, retryLauf]
      split at h
      · exact absurd h (by simp)
      · rename_i hb
        rw [if_neg hb, if_neg hb]
        cases hs : schritt (bis σ ρ).1 ρ with
        | ok σ' ρ' =>
            rw [hs] at h
            exact retryLauf_C_erschoepft schritt bis ueb n σ' ρ' σ0 ρ0 h
        | next hn σ' ρ' =>
            rw [hs] at h
            exact retryLauf_C_erschoepft schritt bis ueb n σ' ρ' σ0 ρ0 h
        | leave hl σ' ρ' => rw [hs] at h; exact absurd h (by simp)
        | zurueck σ' v => rw [hs] at h; exact absurd h (by simp)
        | grund σ' r => rw [hs] at h; exact absurd h (by simp)
        | logik e => rw [hs] at h; exact absurd h (by simp)
        | hardware e => rw [hs] at h; exact absurd h (by simp)

/-- A spent budget with `bis` true at the end: the model ran the overflow
    block, the corrected run (and the C) succeeded. -/
theorem retryLauf_C_verschieden (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueb : World D → Env D Γ → Ausgang V l Γ)
    (n : Nat) (σ : World D) (ρ : Env D Γ) (σ0 : World D) (ρ0 : Env D Γ)
    (h : retryErschoepft schritt bis n σ ρ = some (σ0, ρ0)) (hb : (bis σ0 ρ0).2 = true) :
    retryLauf schritt bis ueb n σ ρ = ueb σ0 ρ0 ∧
      retryLaufC schritt bis ueb n σ ρ = .ok (bis σ0 ρ0).1 ρ0 := by
  obtain ⟨h1, h2⟩ := retryLauf_C_erschoepft schritt bis ueb n σ ρ σ0 ρ0 h
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [ueberC, if_pos hb]

end Lauf

/-! ## 2. The emitted loop, in `CS` -/

/-- `{ uint32_t z = 0; for (; !(cb) && z < N; z += 1) { body } if (z >= N
    && !(cb)) { cexc } }`. -/
def retryCS (z N : Nat) (cb : CX) (cbody : CS) (m' : Nat) (cexc : CS) : CS :=
  .seq (.set z CIT.u32.ty (.lit 0))
    (.seq (.forC (.land (.lnot cb) (.cmp .lt CIT.u32 (.var z) (.lit N)))
        (.set z CIT.u32.ty (.bin .add CIT.u32 (.var z) (.lit 1))) cbody m')
      (.ite (.land (.cmp .ge CIT.u32 (.var z) (.lit N)) (.lnot cb)) cexc .skip))

/-- Evaluation rule of `!(e)`. -/
theorem ev_lnot {L : CLayout} {orc : DevOrc} {fr : Nat} {e : CX} {st st1 : CSt} {ρ : CLok}
    {v : CVal} {b : Bool} (h : ev L orc fr e st ρ = some (v, st1)) (ht : truth v = some b) :
    ev L orc fr (.lnot e) st ρ = some (.int (b2i (!b)), st1) := by
  simp only [ev, h, ht]

/-- `l && r` with `l` false: `r` is not evaluated. -/
theorem ev_land_F {L : CLayout} {orc : DevOrc} {fr : Nat} {l r : CX} {st st1 : CSt} {ρ : CLok}
    {v : CVal} (h : ev L orc fr l st ρ = some (v, st1)) (ht : truth v = some false) :
    ev L orc fr (.land l r) st ρ = some (.int 0, st1) := by
  simp only [ev, h, ht]

/-- `l && r` with `l` true: the truth of `r`. -/
theorem ev_land_T {L : CLayout} {orc : DevOrc} {fr : Nat} {l r : CX} {st st1 st2 : CSt}
    {ρ : CLok} {v w : CVal} {b : Bool} (h : ev L orc fr l st ρ = some (v, st1))
    (ht : truth v = some true) (hr : ev L orc fr r st1 ρ = some (w, st2))
    (hw : truth w = some b) : ev L orc fr (.land l r) st ρ = some (.int (b2i b), st2) := by
  simp only [ev, h, ht, hr, hw]

/-! ## 3. The correspondence against the corrected run -/

section Korrespondenz

variable (X : TVCtx D) (m m' : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool}
  {Λ : List (Res D)}

/-- The corrected meaning of `retry n bis body ueberlauf` in the context
    of `X` -- `execStmt`'s own arguments to `retryLauf`, given to
    `retryLaufC`. -/
def retrySemC (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueb : Block D V l Γ Λ Λ) : World D → Env D Γ → Ausgang V l Γ :=
  retryLaufC (fun σ ρ => execBlock X.O X.passes X.R body σ ρ) (travInv bis)
    (fun σ ρ => execBlock X.O X.passes X.R ueb σ ρ) n

/-- The model's meaning is `retryLauf` with the same arguments. -/
theorem execStmt_retry (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueb : Block D V l Γ Λ Λ) (σ : World D) (ρ : Env D Γ) :
    execStmt X.O X.passes X.R (Stmt.retry n bis body ueb) σ ρ =
      retryLauf (fun σ ρ => execBlock X.O X.passes X.R body σ ρ) (travInv bis)
        (fun σ ρ => execBlock X.O X.passes X.R ueb σ ρ) n σ ρ := rfl

theorem u32_holds (N : Nat) (hN : (N : Int) ≤ CIT.u32.hi) : CIT.u32.holds 0 N :=
  ⟨by decide, hN⟩

/-- The loop header `!(cb) && z < N`, from related states with `z = j`:
    it evaluates `bis` and, only if that is false, the counter. -/
theorem retry_kopf (K : CEnvLay D Γ) {cb : CX} {bis : Expr D Γ Λ .bool} (hb : ExprCorr X K cb bis)
    (z N j : Nat) (hj : j ≤ N) (hN : (N : Int) ≤ CIT.u32.hi) (σ : World D) (st : CSt)
    (ρG : Env D Γ) (ρC : CLok) (hc : corrW X.EL (travInv bis σ ρG).1 st)
    (hr : EnvRel X.EL K ρG ρC) (hz : ρC z = .int j) :
    ∃ st1, ev X.EL.lay X.orc X.fr (.land (.lnot cb) (.cmp .lt CIT.u32 (.var z) (.lit N))) st ρC =
        some (.int (b2i (!(travInv bis σ ρG).2 && decide ((j : Int) < N))), st1) ∧
      corrW X.EL (travInv bis σ ρG).1 st1 := by
  have hlo : CIT.u32.lo = 0 := rfl
  obtain ⟨st1, h1, hc1⟩ := hb.runB X K hc hr
  have hn := ev_lnot h1 (truth_b2i _)
  cases hbv : wahr? (eval (travInv bis σ ρG).1 bis (travInv bis σ ρG).1 ρG) with
  | true =>
      rw [hbv] at hn
      refine ⟨st1, ?_, hc1⟩
      rw [ev_land_F hn rfl]
      show _ = some (CVal.int (b2i (!(wahr? (eval (travInv bis σ ρG).1 bis (travInv bis σ ρG).1 ρG)) &&
        decide ((j : Int) < N))), st1)
      rw [hbv]
      rfl
  | false =>
      rw [hbv] at hn
      have hcmp : ev X.EL.lay X.orc X.fr (.cmp .lt CIT.u32 (.var z) (.lit N)) st1 ρC =
          some (.int (b2i (decide ((j : Int) < N))), st1) :=
        ev_cmp (ev_var hz) rfl (conv_id ⟨by omega, by omega⟩) (conv_id ⟨by omega, hN⟩)
      refine ⟨st1, ?_, hc1⟩
      rw [ev_land_T hn rfl hcmp (truth_b2i _)]
      show _ = some (CVal.int (b2i (!(wahr? (eval (travInv bis σ ρG).1 bis (travInv bis σ ρG).1 ρG)) &&
        decide ((j : Int) < N))), st1)
      rw [hbv]
      rfl

/-- The check after the loop, `z >= N && !(cb)`, with `z = j`. -/
theorem retry_pruef (K : CEnvLay D Γ) {cb : CX} {bis : Expr D Γ Λ .bool}
    (hb : ExprCorr X K cb bis) (z N j : Nat) (hj : j ≤ N) (hN : (N : Int) ≤ CIT.u32.hi)
    (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok) (hc : corrW X.EL (travInv bis σ ρG).1 st)
    (hr : EnvRel X.EL K ρG ρC) (hz : ρC z = .int j) :
    ∃ st1, ev X.EL.lay X.orc X.fr (.land (.cmp .ge CIT.u32 (.var z) (.lit N)) (.lnot cb)) st ρC =
        some (.int (b2i (decide ((N : Int) ≤ j) && !(travInv bis σ ρG).2)), st1) ∧
      corrW X.EL (travInv bis σ ρG).1 st1 := by
  have hlo : CIT.u32.lo = 0 := rfl
  have hcmp : ev X.EL.lay X.orc X.fr (.cmp .ge CIT.u32 (.var z) (.lit N)) st ρC =
      some (.int (b2i (decide ((N : Int) ≤ j))), st) :=
    ev_cmp (ev_var hz) rfl (conv_id ⟨by omega, by omega⟩) (conv_id ⟨by omega, hN⟩)
  cases hle : decide ((N : Int) ≤ j) with
  | false =>
      rw [hle] at hcmp
      exact ⟨st, ev_land_F hcmp rfl, hc⟩
  | true =>
      rw [hle] at hcmp
      obtain ⟨st1, h1, hc1⟩ := hb.runB X K hc hr
      have hn := ev_lnot h1 (truth_b2i _)
      exact ⟨st1, ev_land_T hcmp rfl hn (truth_b2i _), hc1⟩

/-- A run of `seq a b` is a normal run of `a` and a run of `b`, or an
    abrupt run of `a`. -/
theorem exec_seq_inv {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR} {a b : CS}
    {st : CSt} {ρ : CLok} {o : COut} (h : Exec L orc fr CR XR (.seq a b) st ρ o) :
    (∃ st1 ρ1, Exec L orc fr CR XR a st ρ (.norm st1 ρ1) ∧ Exec L orc fr CR XR b st1 ρ1 o) ∨
      (Exec L orc fr CR XR a st ρ o ∧ o.abrupt = true) := by
  cases h with
  | seqN h1 h2 => exact Or.inl ⟨_, _, h1, h2⟩
  | seqX h1 hx => exact Or.inr ⟨h1, hx⟩

/-- Put one more iteration in front of a run of `loop; check`. -/
theorem retry_vorne {L : CLayout} {orc : DevOrc} {fr : Nat} {CR XR : CCallR} {c : CX}
    {step body chk : CS} {m' : Nat} {st st1 st2 st3 : CSt} {ρ ρ2 ρ3 : CLok} {v : CVal} {o1 o : COut}
    (hc : ev L orc fr c st ρ = some (v, st1)) (ht : truth v = some true)
    (hb : Exec L orc fr CR XR body st1 ρ o1) (hw : o1.weiter m' = some (st2, ρ2))
    (hs : Exec L orc fr CR XR step st2 ρ2 (.norm st3 ρ3))
    (hr : Exec L orc fr CR XR (.seq (.forC c step body m') chk) st3 ρ3 o) :
    Exec L orc fr CR XR (.seq (.forC c step body m') chk) st ρ o := by
  rcases exec_seq_inv hr with ⟨st4, ρ4, h1, h2⟩ | ⟨h1, hx⟩
  · exact Exec.seqN (Exec.forStep hc ht hb hw hs h1) h2
  · exact Exec.seqX (Exec.forStep hc ht hb hw hs h1) hx

/-- THE LOOP, by induction on the passes left (`k`), with `z = j` and
    `j + k = N`: the C loop followed by its check corresponds to the
    corrected run. -/
theorem retryC_run (hK : K.okB = true) {z : Nat} (hf : K.freshB z = true) (N : Nat)
    (hN : (N : Int) ≤ CIT.u32.hi) {cb : CX} {bis : Expr D Γ Λ .bool} (hb : ExprCorr X K cb bis)
    (body : Block D V true Γ Λ Λ) (cbody : CS) (hbody : BlockSem X m' K body cbody)
    (hw : cbody.writesV z = false) (ueb : Block D V l Γ Λ Λ) (cexc : CS)
    (hu : BlockSem X m K ueb cexc) :
    ∀ (k j : Nat), j + k = N →
      ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
        EnvRel X.EL K ρG ρC → ρC z = .int j →
        (retrySemC X k bis body ueb σ ρG).istFehler = false →
        ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR
            (.seq (.forC (.land (.lnot cb) (.cmp .lt CIT.u32 (.var z) (.lit N)))
                (.set z CIT.u32.ty (.bin .add CIT.u32 (.var z) (.lit 1))) cbody m')
              (.ite (.land (.cmp .ge CIT.u32 (.var z) (.lit N)) (.lnot cb)) cexc .skip)) st ρC o ∧
          StOut X m K (retrySemC X k bis body ueb σ ρG) o := by
  intro k
  induction k with
  | zero =>
      intro j hjk σ st ρG ρC hc hr hz hnf
      have hjN : j = N := by omega
      subst hjN
      have hc0 : corrW X.EL (travInv bis σ ρG).1 st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨st1, h1, hc1⟩ := retry_kopf X K hb z j j (Nat.le_refl _) hN σ st ρG ρC hc0 hr hz
      have hnj : decide ((j : Int) < j) = false := decide_eq_false (by omega)
      rw [hnj, Bool.and_false] at h1
      obtain ⟨st2, h2, hc2⟩ := retry_pruef X K hb z j j (Nat.le_refl _) hN σ st1 ρG ρC hc1 hr hz
      have hjj : decide ((j : Int) ≤ j) = true := decide_eq_true (by omega)
      rw [hjj, Bool.true_and] at h2
      have hsem : retrySemC X 0 bis body ueb σ ρG =
          if (travInv bis σ ρG).2 = true then .ok (travInv bis σ ρG).1 ρG
          else execBlock X.O X.passes X.R ueb (travInv bis σ ρG).1 ρG := rfl
      rw [hsem] at hnf ⊢
      cases hbv : (travInv bis σ ρG).2 with
      | true =>
          rw [hbv] at h2
          refine ⟨.norm st2 ρC, Exec.seqN (Exec.forDone h1 rfl) (Exec.iteF h2 rfl Exec.skip), ?_⟩
          exact ⟨st2, ρC, rfl, hc2, hr⟩
      | false =>
          rw [hbv] at h2
          simp only [hbv, Bool.false_eq_true, if_false] at hnf ⊢
          obtain ⟨o, h3, hO⟩ := hu _ st2 ρG ρC hc2 hr hnf
          exact ⟨o, Exec.seqN (Exec.forDone h1 rfl) (Exec.iteT h2 rfl h3), hO⟩
  | succ k ih =>
      intro j hjk σ st ρG ρC hc hr hz hnf
      have hjN : (j : Int) < N := by omega
      have hc0 : corrW X.EL (travInv bis σ ρG).1 st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨st1, h1, hc1⟩ := retry_kopf X K hb z N j (by omega) hN σ st ρG ρC hc0 hr hz
      have hlt : decide ((j : Int) < N) = true := decide_eq_true hjN
      rw [hlt, Bool.and_true] at h1
      simp only [retrySemC] at hnf ⊢
      rw [retryLaufC.eq_2] at hnf ⊢
      cases hbv : (travInv bis σ ρG).2 with
      | true =>
          -- the condition holds before the pass: the loop ends, the check is `z >= N`, false
          rw [hbv] at h1
          simp only [if_true]
          obtain ⟨st2, h2, hc2⟩ := retry_pruef X K hb z N j (by omega) hN σ st1 ρG ρC hc1 hr hz
          have hge : decide ((N : Int) ≤ j) = false := decide_eq_false (by omega)
          rw [hge, Bool.false_and] at h2
          exact ⟨.norm st2 ρC, Exec.seqN (Exec.forDone h1 rfl) (Exec.iteF h2 rfl Exec.skip),
            st2, ρC, rfl, hc2, hr⟩
      | false =>
          rw [hbv] at h1
          simp only [hbv, Bool.false_eq_true, if_false] at hnf ⊢
          have htr : truth (.int (b2i (!false))) = some true := rfl
          cases hB : execBlock X.O X.passes X.R body (travInv bis σ ρG).1 ρG with
          | ok σ' ρ' =>
              rw [hB] at hnf
              obtain ⟨o1, hx1, hO1⟩ := hbody _ st1 ρG ρC hc1 hr (by rw [hB]; rfl)
              rw [hB] at hO1
              obtain ⟨st2, ρC2, ho1, hc2, hr2⟩ := hO1
              subst ho1
              have hz2 : ρC2 z = .int j := by rw [exec_keeps z hx1 hw ρC2 rfl, hz]
              have hinc := exec_incr X CIT.u32 N (u32_holds N hN) z j hjN st2 ρC2 hz2
              have hr3 := envRel_upd_fresh hK hf hr2 (.int ((j : Int) + 1))
              obtain ⟨o, h2, hO⟩ := ih (j + 1) (by omega) σ' st2 ρ' _ hc2 hr3
                (by simp only [lokUpd, if_pos]; rfl) hnf
              exact ⟨o, retry_vorne h1 htr hx1 rfl hinc h2, hO⟩
          | next hn σ' ρ' =>
              rw [hB] at hnf
              obtain ⟨o1, hx1, hO1⟩ := hbody _ st1 ρG ρC hc1 hr (by rw [hB]; rfl)
              rw [hB] at hO1
              obtain ⟨st2, ρC2, ho1, hc2, hr2⟩ := hO1
              subst ho1
              have hz2 : ρC2 z = .int j := by rw [exec_keeps z hx1 hw ρC2 rfl, hz]
              have hinc := exec_incr X CIT.u32 N (u32_holds N hN) z j hjN st2 ρC2 hz2
              have hr3 := envRel_upd_fresh hK hf hr2 (.int ((j : Int) + 1))
              obtain ⟨o, h2, hO⟩ := ih (j + 1) (by omega) σ' st2 ρ' _ hc2 hr3
                (by simp only [lokUpd, if_pos]; rfl) hnf
              exact ⟨o, retry_vorne h1 htr hx1 (by simp [COut.weiter]) hinc h2, hO⟩
          | leave hl σ' ρ' =>
              obtain ⟨o1, hx1, hO1⟩ := hbody _ st1 ρG ρC hc1 hr (by rw [hB]; rfl)
              rw [hB] at hO1
              obtain ⟨st2, ρC2, ho1, hc2, hr2⟩ := hO1
              subst ho1
              -- the loop consumes `goto m'_ende`; the check sees `z = j < N` and skips
              have hz2 : ρC2 z = .int j := by rw [exec_keeps z hx1 hw ρC2 rfl, hz]
              have hc2' : corrW X.EL (travInv bis σ' ρ').1 st2 := (corrW_lese _ _ _ _ _).mpr hc2
              obtain ⟨st3, h3, hc3⟩ := retry_pruef X K hb z N j (by omega) hN σ' st2 ρ' ρC2 hc2'
                hr2 hz2
              have hge : decide ((N : Int) ≤ j) = false := decide_eq_false (by omega)
              rw [hge, Bool.false_and] at h3
              exact ⟨.norm st3 ρC2, Exec.seqN (Exec.forExit h1 htr hx1 (by simp [COut.raus]))
                (Exec.iteF h3 rfl Exec.skip), st3, ρC2, rfl, (corrW_lese _ _ _ _ _).mp hc3, hr2⟩
          | zurueck σ' v =>
              obtain ⟨o1, hx1, hO1⟩ := hbody _ st1 ρG ρC hc1 hr (by rw [hB]; rfl)
              rw [hB] at hO1
              obtain ⟨st2, cv, ho1, hc2, hrc⟩ := hO1
              subst ho1
              exact ⟨_, Exec.seqX (Exec.forExit h1 htr hx1 rfl) rfl, st2, cv, rfl, hc2, hrc⟩
          | grund σ' r =>
              obtain ⟨o1, -, hO1⟩ := hbody _ st1 ρG ρC hc1 hr (by rw [hB]; rfl)
              rw [hB] at hO1
              exact hO1.elim
          | logik e => rw [hB] at hnf; exact Bool.noConfusion hnf
          | hardware e => rw [hB] at hnf; exact Bool.noConfusion hnf

/-- `retry` AGAINST THE CORRECTED RUN: the emitted loop (`retryCS`)
    corresponds to `retryLaufC` -- every form of the body's exit (`next`,
    `leave`, `return`), the early success, the success in the last check,
    and the overflow. -/
theorem scorrC_retry (hK : K.okB = true) {z : Nat} (hf : K.freshB z = true) (N : Nat)
    (hN : (N : Int) ≤ CIT.u32.hi) {cb : CX} {bis : Expr D Γ Λ .bool} (hb : ExprCorr X K cb bis)
    (body : Block D V true Γ Λ Λ) (cbody : CS) (hbody : BlockSem X m' K body cbody)
    (hw : cbody.writesV z = false) (ueb : Block D V l Γ Λ Λ) (cexc : CS)
    (hu : BlockSem X m K ueb cexc) :
    ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
      EnvRel X.EL K ρG ρC → (retrySemC X N bis body ueb σ ρG).istFehler = false →
      ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR (retryCS z N cb cbody m' cexc) st ρC o ∧
        StOut X m K (retrySemC X N bis body ueb σ ρG) o := by
  intro σ st ρG ρC hc hr hnf
  have hset : Exec X.EL.lay X.orc X.fr X.CR X.XR (.set z CIT.u32.ty (.lit 0)) st ρC
      (.norm st (lokUpd ρC z (.int 0))) :=
    Exec.set (v := .int 0) rfl rfl
  obtain ⟨o, h2, hO⟩ := retryC_run X m m' K hK hf N hN hb body cbody hbody hw ueb cexc hu N 0
    (Nat.zero_add N) σ st ρG (lokUpd ρC z (.int 0)) hc (envRel_upd_fresh hK hf hr _)
    (by simp only [lokUpd, if_pos]; rfl) hnf
  exact ⟨o, Exec.seqN hset h2, hO⟩

/-- `retry` AGAINST THE MODEL AS IT STANDS: when the overflow block always
    ends in an error (the emitter admits only a `never` exit, whose Gabbro
    meaning is the hardware assumption of the foreign call), the emitted
    loop corresponds to `execStmt`'s own `retryLauf`. Where the two
    definitions differ, the model's outcome is that error, which carries
    no obligation. -/
theorem scorr_retry (hK : K.okB = true) {z : Nat} (hf : K.freshB z = true) (N : Nat)
    (hN : (N : Int) ≤ CIT.u32.hi) {cb : CX} {bis : Expr D Γ Λ .bool} (hb : ExprCorr X K cb bis)
    (body : Block D V true Γ Λ Λ) (cbody : CS) (hbody : BlockSem X m' K body cbody)
    (hw : cbody.writesV z = false) (ueb : Block D V l Γ Λ Λ) (cexc : CS)
    (hu : BlockSem X m K ueb cexc)
    (hnie : ∀ σ ρ, (execBlock X.O X.passes X.R ueb σ ρ).istFehler = true) :
    StmtCorr X m K (Stmt.retry N bis body ueb) (retryCS z N cb cbody m' cexc) := by
  intro σ st ρG ρC hc hr hnf
  rw [execStmt_retry] at hnf ⊢
  cases he : retryErschoepft (fun σ ρ => execBlock X.O X.passes X.R body σ ρ) (travInv bis)
      N σ ρG with
  | none =>
      have hg := retryLauf_C_gleich (fun σ ρ => execBlock X.O X.passes X.R body σ ρ)
        (travInv bis) (fun σ ρ => execBlock X.O X.passes X.R ueb σ ρ) N σ ρG he
      rw [← hg] at hnf ⊢
      exact scorrC_retry X m m' K hK hf N hN hb body cbody hbody hw ueb cexc hu σ st ρG ρC hc hr hnf
  | some p =>
      obtain ⟨σ0, ρ0⟩ := p
      obtain ⟨h1, -⟩ := retryLauf_C_erschoepft (fun σ ρ => execBlock X.O X.passes X.R body σ ρ)
        (travInv bis) (fun σ ρ => execBlock X.O X.passes X.R ueb σ ρ) N σ ρG σ0 ρ0 he
      rw [h1] at hnf
      rw [hnie σ0 ρ0] at hnf
      exact Bool.noConfusion hnf

end Korrespondenz

/-
CUTS: what this file does not do, by name.
- `Semantik.lean` is not edited: `retryLauf` keeps its `0` case, and the
  model therefore reports the overflow block where the C succeeds
  (`retryLauf_C_verschieden`). The edit is stated in the header, one
  line; every theorem about `retryLauf` would have to be re-checked with
  it (`retryLauf_gut`, `retryLauf_ohneAbbruch`, … in Satz.lean,
  RufAdaequatRufG.lean, HoareRegeln.lean).
- The loop condition must have an `ExprCorr` (no observation that changes
  its value): a `retry` polling a device register -- most `retry`s of the
  corpus -- is not covered, as H9 (the register read) is a per-step lemma
  only.
- The emitted `on_exceeded` call `ausgang();` is `cexc`, whatever its own
  lemma says (`scorr_axiomCall` for a foreign exit, or vacuous where the
  Gabbro block is an error).
- The pass count `N` is a premise (`N ≤ UINT32_MAX`); that it is the
  emitter's `floor(budget / per-pass cost)` is the elaboration's matter.
-/

#print axioms retryLaufC_eq
#print axioms retryLauf_C_gleich
#print axioms retryLauf_C_erschoepft
#print axioms retryLauf_C_verschieden
#print axioms retryC_run
#print axioms scorrC_retry
#print axioms scorr_retry

end Gabbro.Grammatik
