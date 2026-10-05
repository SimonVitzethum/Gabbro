/-
  File:      Grammatik/X86/PipelineInfinite.lean
  Subject:   Finite and infinite execution soundness of the pipeline
             (`Pipeline.lean` + `PipelineImage.lean`): every finite prefix
             of the byte-level run of a lowered program is safe (it succeeds
             with the code region intact) up to the corresponding end, and
             the target stops only at a point the source budget semantics
             allows (the code end for `ok`, a refusal exit for `grund`, at
             every budget `passes`).

             Reused, not duplicated:
               - pipeline: `senkBlock_korrektC`, `senkBlock_ausgang`,
                 `senkBlock_assign`, `senkBlock_ite_inv`, `validate_sound`,
                 `Entspricht`, `CodeAt`, `WorldRep`, `LayoutSep`, `EnvRepr`,
                 `abbOf`, `encodeAll`, `laufBytes_add`, `grund_mem`;
               - image frame: `ByteRahmen`, `laufBytes_rahmen`,
                 `codeAt_lauf` (`PipelineImage.lean`);
               - machine: `byteschritt`, `laufBytes`, `ByteAusgang`;
               - source: `execBlock`, `execStmt`, `execStmt_ite`,
                 `execBlock_cons_stmtOk/Grund`, `constInt?_sound`;
               - witness data: `PipelineWitnesses` (`pwCfg`, `pwSrc`, ...).
             No second IR, no second source interpreter, no per-program rule.
-/
import Grammatik.X86.Pipeline.Kern.PipelineImage
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipelineInfinite

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineWitnesses

variable {D : Deklaration}

/-! ## 1. Budgeted byte runs: the target-side budget semantics

    `laufBudget n s` runs at most `n` byte steps: `fertig` ran the whole
    budget without a stop, `stopp` met a defined stop (`verweigert`) after
    `k` steps. There is no silent third outcome. -/

/-- The outcome of a budgeted byte run. -/
inductive BudgetAusgang where
  | fertig : Nat → Zustand → BudgetAusgang
  | stopp : Nat → Zustand → BudgetAusgang

/-- Run at most `n` byte steps from `s`. -/
def laufBudget : Nat → Zustand → BudgetAusgang
  | 0, s => .fertig 0 s
  | n + 1, s =>
    match byteschritt s with
    | .verweigert => .stopp 0 s
    | .weiter s' =>
      match laufBudget n s' with
      | .fertig k s'' => .fertig (k + 1) s''
      | .stopp k s'' => .stopp (k + 1) s''

/-! ## 2. Prefixes of byte runs (machine level, no source)

    A successful run succeeds on every prefix; a refused run stays refused
    under more fuel. Pure facts of `laufBytes`, reused by the pipeline
    theorems below. -/

/-- PREFIX SUCCESS: every prefix of a successful byte run succeeds. -/
theorem laufBytes_praefix_erfolg (n k : Nat) (s s' : Zustand)
    (h : laufBytes n s = .weiter s') (hk : k ≤ n) :
    ∃ sk, laufBytes k s = .weiter sk := by
  induction n generalizing k s with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    exact ⟨s, rfl⟩
  | succ n ih =>
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBytes, hb] at h
      cases h
    | weiter s1 =>
      simp only [laufBytes, hb] at h
      cases k with
      | zero => exact ⟨s, rfl⟩
      | succ j =>
        obtain ⟨sk, hsk⟩ := ih j s1 h (by omega)
        exact ⟨sk, by simp only [laufBytes, hb]; exact hsk⟩

/-- REFUSAL MONOTONICITY: a refused run stays refused under more fuel. -/
theorem laufBytes_verweigert_plus : ∀ (m j : Nat) (s : Zustand),
    laufBytes m s = .verweigert → laufBytes (m + j) s = .verweigert
  | 0, j, s, h => by
    simp only [laufBytes] at h
    cases h
  | m + 1, j, s, h => by
    cases hb : byteschritt s with
    | verweigert =>
      have he : m + 1 + j = (m + j) + 1 := by omega
      rw [he]
      simp only [laufBytes, hb]
    | weiter s1 =>
      have he : m + 1 + j = (m + j) + 1 := by omega
      simp only [laufBytes, hb] at h
      rw [he]
      simp only [laufBytes, hb]
      exact laufBytes_verweigert_plus m j s1 h

/-! ## 3. The budgeted runner is faithful

    `fertig` means the whole budget ran clean; `stopp` means a defined stop
    after `k` steps. Both directions are proved from the definitions. -/

/-- `fertig` ran the whole budget: `k = n` and the plain run succeeds. -/
theorem laufBudget_fertig : ∀ (n : Nat) (s : Zustand) (k : Nat) (s' : Zustand),
    laufBudget n s = .fertig k s' → k = n ∧ laufBytes n s = .weiter s'
  | 0, s, k, s', h => by
    simp only [laufBudget] at h
    cases h
    exact ⟨rfl, rfl⟩
  | n + 1, s, k, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBudget, hb] at h
      cases h
    | weiter s1 =>
      simp only [laufBudget, hb] at h
      cases hl : laufBudget n s1 with
      | fertig k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
        obtain ⟨hk1, hrun⟩ := laufBudget_fertig n s1 k1 s' hl
        refine ⟨by omega, ?_⟩
        simp only [laufBytes, hb]
        exact hrun
      | stopp k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h

/-- `stopp` met a defined stop: `k ≤ n`, the `k`-prefix succeeds, and the
    prefix state has no transition. -/
theorem laufBudget_stopp : ∀ (n : Nat) (s : Zustand) (k : Nat) (s' : Zustand),
    laufBudget n s = .stopp k s' →
      k ≤ n ∧ laufBytes k s = .weiter s' ∧ byteschritt s' = .verweigert
  | 0, s, k, s', h => by
    simp only [laufBudget] at h
    cases h
  | n + 1, s, k, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBudget, hb] at h
      cases h
      exact ⟨Nat.zero_le _, rfl, hb⟩
    | weiter s1 =>
      simp only [laufBudget, hb] at h
      cases hl : laufBudget n s1 with
      | fertig k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
      | stopp k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
        obtain ⟨hk1, hrun, hst⟩ := laufBudget_stopp n s1 k1 s' hl
        refine ⟨by omega, ?_, hst⟩
        simp only [laufBytes, hb]
        exact hrun

/-- REFUSAL STABILITY: once the budgeted runner stops, more fuel stays
    stopped at the same state. The runner refuses to step past a stop. -/
theorem laufBudget_stopp_stabil : ∀ (n j : Nat) (s : Zustand) (k : Nat) (s' : Zustand),
    laufBudget n s = .stopp k s' → laufBudget (n + j) s = .stopp k s'
  | 0, j, s, k, s', h => by
    simp only [laufBudget] at h
    cases h
  | n + 1, j, s, k, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBudget, hb] at h
      cases h
      have he : n + 1 + j = (n + j) + 1 := by omega
      rw [he]
      simp only [laufBudget, hb]
    | weiter s1 =>
      simp only [laufBudget, hb] at h
      cases hl : laufBudget n s1 with
      | fertig k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
      | stopp k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
        have he : n + 1 + j = (n + j) + 1 := by omega
        have ih := laufBudget_stopp_stabil n j s1 k1 s' hl
        rw [he]
        simp only [laufBudget, hb]
        rw [ih]

/-- CONVERSE: a clean plain run is a `fertig` budgeted run. Used by the
    positive probes below. -/
theorem laufBudget_fertig_von : ∀ (n : Nat) (s s' : Zustand),
    laufBytes n s = .weiter s' → ∃ k s'', laufBudget n s = .fertig k s'' ∧ k = n ∧ s'' = s'
  | 0, s, s', h => by
    simp only [laufBytes] at h
    cases h
    exact ⟨0, s, rfl, rfl, rfl⟩
  | n + 1, s, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBytes, hb] at h
      cases h
    | weiter s1 =>
      simp only [laufBytes, hb] at h
      obtain ⟨k, s'', hfb, hkk, hss⟩ := laufBudget_fertig_von n s1 s' h
      refine ⟨k + 1, s'', ?_, by omega, hss⟩
      simp only [laufBudget, hb]
      rw [hfb]

/-! ## 4. Prefix safety for lowered programs

    For a validated block, the fetched byte run reaches a state
    corresponding to the real `execBlock` outcome -- and EVERY finite
    prefix of that run is safe: it succeeds with the code region intact
    and the memory frame kept. Mid-run states get no source
    correspondence (a half-executed assignment chunk has no source
    meaning); the correspondence holds at the end. -/

section PipelineSaetze
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- SAFETY OF EVERY PREFIX: a validated block runs to its corresponding
    end state, and every prefix succeeds with code and frame intact. -/
theorem praefix_sicher (c : PipeCfg) (L : Layout D)
    (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c L certs src bytes = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c)) :
    ∃ n s', laufBytes n s = .weiter s' ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (0 + bytes.length))
        (execBlock O passes R (optimise certs src) σ ρ) s' ∧
      (∀ k, k ≤ n → ∃ sk, laufBytes k s = .weiter sk ∧
        CodeAt sk.speicher (natAdresse c.codeBase) bytes ∧
        ByteRahmen s.speicher sk.speicher) := by
  obtain ⟨prog, hc, hlow, hb, -, -⟩ := validate_sound c L certs src bytes hval
  obtain ⟨n, s', hrun, -, hent⟩ := senkBlock_korrektC c L hc hsep O passes R bytes
    (optimise certs src) [] [] prog hlow σ ρ s hcode (by simp [hb])
    (by rw [hrip]; exact (addrOff_null _).symm) hW hE
  rw [← hb] at hent
  refine ⟨n, s', hrun, hent, fun k hk => ?_⟩
  obtain ⟨sk, hsk⟩ := laufBytes_praefix_erfolg n k s s' hrun hk
  exact ⟨sk, hsk, codeAt_lauf k s sk hsk _ _ hcode, laufBytes_rahmen k s sk hsk⟩

/-- BUDGET-STOP ORDERING: the target stops only at or after the point the
    source allows. A stop `sk` at step `k` (a state with no transition)
    cannot come before the corresponding end `n`; at `k = n` it IS the
    corresponding end state. Before `n` the run always continues. -/
theorem erste_stop_ordnung (c : PipeCfg) (L : Layout D)
    (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c L certs src bytes = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (k : Nat) (sk : Zustand)
    (hpre : laufBytes k s = .weiter sk) (hstop : byteschritt sk = .verweigert) :
    ∃ n s', laufBytes n s = .weiter s' ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (0 + bytes.length))
        (execBlock O passes R (optimise certs src) σ ρ) s' ∧
      n ≤ k ∧ (k = n → sk = s') := by
  obtain ⟨prog, hc, hlow, hb, -, -⟩ := validate_sound c L certs src bytes hval
  obtain ⟨n, s', hrun, -, hent⟩ := senkBlock_korrektC c L hc hsep O passes R bytes
    (optimise certs src) [] [] prog hlow σ ρ s hcode (by simp [hb])
    (by rw [hrip]; exact (addrOff_null _).symm) hW hE
  rw [← hb] at hent
  have hnk : n ≤ k := by
    by_cases hle : n ≤ k
    · exact hle
    · have hlt : k < n := by omega
      have hkp1 : laufBytes (k + 1) s = .verweigert := by
        have h1' : laufBytes (k + 1) s = laufBytes (0 + 1) sk :=
          laufBytes_add k 1 s sk hpre
        rw [h1']
        simp only [laufBytes, hstop]
      have hcontra : laufBytes n s = .verweigert := by
        have hplus := laufBytes_verweigert_plus (k + 1) (n - (k + 1)) s hkp1
        rwa [show (k + 1) + (n - (k + 1)) = n by omega] at hplus
      rw [hcontra] at hrun
      cases hrun
  refine ⟨n, s', hrun, hent, hnk, fun hkk => ?_⟩
  cases hkk
  rw [hrun] at hpre
  cases hpre
  rfl

/-- SOURCE BUDGET INDEPENDENCE: a lowered block runs the same at every
    budget `passes`. The fragment has no loops and no calls, so `passes`
    is threaded but never consumed; the induction mirrors
    `senkBlock_ausgang`, using the definitional `execBlock` equations
    (which never case on `passes`) at both budgets. Together with
    `pipeline_ausgang` (only `ok`/`grund` at every budget) this is the
    source side of the budget-stop ordering: no budget stop exists for
    accepted programs, on either side. -/
theorem budget_unabhaengig (c : PipeCfg) (L : Layout D) (O : Orakel D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (pos : Nat)
    (prog : List Befehl) (h : senkBlock c L pos b = some prog) (σ : World D) (ρ : Env D Γ)
    (p1 p2 : Nat) :
    execBlock O p1 R b σ ρ = execBlock O p2 R b σ ρ := by
  generalize hb0 : b = b0 at h
  cases b0 with
  | nil => rfl
  | cons st rest =>
    cases st with
    | assignSlot t f i e hw hL =>
      rw [senkBlock_assign] at h
      cases hs : senkStmt c L (Stmt.assignSlot (V := V) t f i e hw hL) with
      | none => rw [hs] at h; cases h
      | some p =>
        rw [hs] at h
        dsimp only at h
        cases hq : senkBlock c L (pos + (encodeAll p).length) rest with
        | none => simp [hq] at h
        | some q =>
          simp only [senkStmt] at hs
          cases hk : constInt? i with
          | none => simp [hk] at hs
          | some k =>
            simp only [hk] at hs
            cases hA : L.loc t k f with
            | none => simp [hA] at hs
            | some A =>
              simp only [hA] at hs
              by_cases hok : repOk (D.typ t f) A 8 0 = true
              · rw [if_pos hok] at hs
                cases hv : senkWertT c e with
                | none => simp [hv] at hs
                | some pv =>
                  simp only [hv] at hs
                  simp only [Option.map_some, Option.some.injEq] at hs
                  subst hs
                  let σL := σ.lese Λ (i.orte ++ e.orte)
                  have hki : (eval σL i σL ρ).n = k := by
                    have hci := constInt?_sound i σL σL ρ k hk
                    simpa [intOf] using hci
                  have e1 : execBlock O p1 R (.cons (.assignSlot t f i e hw hL) rest) σ ρ =
                      execBlock O p1 R rest
                        (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
                    rw [← hki]
                    rfl
                  have e2 : execBlock O p2 R (.cons (.assignSlot t f i e hw hL) rest) σ ρ =
                      execBlock O p2 R rest
                        (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
                    rw [← hki]
                    rfl
                  rw [e1, e2]
                  exact budget_unabhaengig c L O R rest _ q hq _ ρ p1 p2
              · rw [if_neg hok] at hs; cases hs
    | ite cnd t e =>
      obtain ⟨code, j, pt, pe, q, -, ht, he, -, -, hq, -⟩ :=
        senkBlock_ite_inv c L cnd t e rest pos prog h
      have hsrc1 := execStmt_ite O p1 R cnd t e σ ρ
      have hsrc2 := execStmt_ite O p2 R cnd t e σ ρ
      by_cases hc : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = true
      · have eqt : execBlock O p1 R t (σ.lese Λ cnd.orte) ρ =
            execBlock O p2 R t (σ.lese Λ cnd.orte) ρ :=
          budget_unabhaengig c L O R t _ pt ht _ ρ p1 p2
        rcases senkBlock_ausgang c L O p1 R t _ pt ht _ ρ with ⟨σ', ρ', hx⟩ | ⟨σ', r, hx⟩
        · have hs1 : execStmt O p1 R (.ite cnd t e) σ ρ = .ok σ' ρ' := by
            rw [hsrc1, if_pos hc, hx]
          have hs2 : execStmt O p2 R (.ite cnd t e) σ ρ = .ok σ' ρ' := by
            rw [hsrc2, if_pos hc, ← eqt, hx]
          rw [execBlock_cons_stmtOk O p1 R _ rest σ ρ σ' ρ' hs1,
            execBlock_cons_stmtOk O p2 R _ rest σ ρ σ' ρ' hs2]
          exact budget_unabhaengig c L O R rest _ q hq σ' ρ' p1 p2
        · have hs1 : execStmt O p1 R (.ite cnd t e) σ ρ = .grund σ' r := by
            rw [hsrc1, if_pos hc, hx]
          have hs2 : execStmt O p2 R (.ite cnd t e) σ ρ = .grund σ' r := by
            rw [hsrc2, if_pos hc, ← eqt, hx]
          rw [execBlock_cons_stmtGrund O p1 R _ rest σ σ' ρ r hs1,
            execBlock_cons_stmtGrund O p2 R _ rest σ σ' ρ r hs2]
      · have eqe : execBlock O p1 R e (σ.lese Λ cnd.orte) ρ =
            execBlock O p2 R e (σ.lese Λ cnd.orte) ρ :=
          budget_unabhaengig c L O R e _ pe he _ ρ p1 p2
        rcases senkBlock_ausgang c L O p1 R e _ pe he _ ρ with ⟨σ', ρ', hx⟩ | ⟨σ', r, hx⟩
        · have hs1 : execStmt O p1 R (.ite cnd t e) σ ρ = .ok σ' ρ' := by
            rw [hsrc1, if_neg hc, hx]
          have hs2 : execStmt O p2 R (.ite cnd t e) σ ρ = .ok σ' ρ' := by
            rw [hsrc2, if_neg hc, ← eqe, hx]
          rw [execBlock_cons_stmtOk O p1 R _ rest σ ρ σ' ρ' hs1,
            execBlock_cons_stmtOk O p2 R _ rest σ ρ σ' ρ' hs2]
          exact budget_unabhaengig c L O R rest _ q hq σ' ρ' p1 p2
        · have hs1 : execStmt O p1 R (.ite cnd t e) σ ρ = .grund σ' r := by
            rw [hsrc1, if_neg hc, hx]
          have hs2 : execStmt O p2 R (.ite cnd t e) σ ρ = .grund σ' r := by
            rw [hsrc2, if_neg hc, ← eqe, hx]
          rw [execBlock_cons_stmtGrund O p1 R _ rest σ σ' ρ r hs1,
            execBlock_cons_stmtGrund O p2 R _ rest σ σ' ρ r hs2]
    | _ => simp [senkBlock, senkStmt] at h
  | pruefung cnd sonst rest =>
    simp only [senkBlock] at h
    cases hs : senkPruef c pos cnd sonst with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : senkBlock c L (pos + (encodeAll p).length) rest with
      | none => simp [hq] at h
      | some q =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        subst h
        cases sonst with
        | retGrund r hΛ =>
          have hsrc1 : execBlock O p1 R (.pruefung cnd (.retGrund r hΛ) rest) σ ρ =
              (if wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ)
               then execBlock O p1 R rest (σ.lese Λ cnd.orte) ρ
               else .grund (σ.lese Λ cnd.orte) r) := rfl
          have hsrc2 : execBlock O p2 R (.pruefung cnd (.retGrund r hΛ) rest) σ ρ =
              (if wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ)
               then execBlock O p2 R rest (σ.lese Λ cnd.orte) ρ
               else .grund (σ.lese Λ cnd.orte) r) := rfl
          rw [hsrc1, hsrc2]
          by_cases hc : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = true
          · rw [if_pos hc, if_pos hc]
            exact budget_unabhaengig c L O R rest _ q hq _ ρ p1 p2
          · rw [if_neg hc, if_neg hc]
        | _ => simp [senkPruef] at hs
  | _ => simp [senkBlock] at h
termination_by sizeOf b
decreasing_by
  all_goals
    subst hb0
    simp only [Block.cons.sizeOf_spec, Block.pruefung.sizeOf_spec, Stmt.ite.sizeOf_spec]
    omega

end PipelineSaetze

/-! ## 5. Joint witnesses on the non-degenerate pipeline program

    All premises jointly on `pwSrc` (two slots written, one from a
    variable, one from a folded constant; the source run changes memory
    7 -> 35 and 9 -> 6). -/

/-- JOINT WITNESS for `praefix_sicher`: every premise holds on the
    witness program whose source run changes memory; the fetched run
    ends with the slot bytes 35 and 6, and every prefix is safe. -/
theorem praefix_sicher_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧ LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse pwCfg.codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      ∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧
        (∀ k, k ≤ n → ∃ sk, laufBytes k (pwStart 30) = .weiter sk ∧
          CodeAt sk.speicher (natAdresse pwCfg.codeBase) pwBytes ∧
          ByteRahmen (pwStart 30).speicher sk.speicher) ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 35) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 6) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  obtain ⟨n, s', hrun, hent, hpre⟩ := praefix_sicher pwCfg pwL pwCerts pwSrc pwBytes
    pw_validate pw_layoutSep pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
    pw_code rfl pw_worldRep pw_envRepr30
  rw [optimise_sound pwCerts pwSrc pwO 0 pwR pwSigma pwEnv30, hsrc] at hent
  obtain ⟨-, hw, -⟩ := hent
  refine ⟨σ', ρ', pw_validate, pw_layoutSep, pw_code, rfl, pw_worldRep, pw_envRepr30,
    hsrc, rfl, h0, rfl, h1, n, s', hrun, hpre, ?_, ?_⟩
  · exact read_von_worldRep _ σ' 0 8192 hw rfl 35 h0
  · exact read_von_worldRep _ σ' 1 8200 hw rfl 6 h1

/-- The computed 12-step run ends at the code end with no transition:
    a genuine stop after a memory-changing run, not an immediate refusal.
    Stated observably (`ausgangRip`/`ausgangByte` are decidable); the
    `decide` evaluates the closed byte run. -/
theorem laufBytes12_stop : ∃ s12, laufBytes 12 (pwStart 30) = .weiter s12 ∧
    s12.rip = natAdresse 4178 ∧ byteschritt s12 = .verweigert := by
  have hw : ∃ s12, laufBytes 12 (pwStart 30) = .weiter s12 := by
    cases h12 : laufBytes 12 (pwStart 30) with
    | weiter s12 => exact ⟨s12, rfl⟩
    | verweigert =>
      have h := pw_bytes30.1
      simp [ausgangRip, h12] at h
  obtain ⟨s12, h12⟩ := hw
  have hrip : s12.rip = natAdresse 4178 := by
    have h := pw_bytes30.1
    rw [h12] at h
    simpa [ausgangRip] using h
  have hstop : ausgangRip (byteschritt s12) = none := by
    have hall : ausgangRip (laufBytes 13 (pwStart 30)) = none := by decide
    have h13 : laufBytes 13 (pwStart 30) = laufBytes 1 s12 :=
      laufBytes_add 12 1 (pwStart 30) s12 h12
    rw [h13] at hall
    cases h : byteschritt s12 with
    | verweigert => rfl
    | weiter s' =>
      have h1 : laufBytes 1 s12 = .weiter s' := by
        show laufBytes (0 + 1) s12 = .weiter s'
        simp only [laufBytes, h]
      rw [h1] at hall
      simp [ausgangRip] at hall
  have hs : byteschritt s12 = .verweigert := by
    cases h : byteschritt s12 with
    | verweigert => rfl
    | weiter s' =>
      rw [h] at hstop
      simp [ausgangRip] at hstop
  exact ⟨s12, h12, hrip, hs⟩

/-- JOINT WITNESS for `erste_stop_ordnung`: the concrete 12-step stop is
    at/after the corresponding end, and at equal length it is the end
    state; the source run changes memory 7 -> 35. -/
theorem erste_stop_ordnung_zeuge :
    ∃ (s12 : Zustand),
      validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧ LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse pwCfg.codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf pwCfg) ∧
      (∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
        (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35) ∧
      laufBytes 12 (pwStart 30) = .weiter s12 ∧ s12.rip = natAdresse 4178 ∧
      byteschritt s12 = .verweigert ∧
      ∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧ n ≤ 12 ∧ (12 = n → s12 = s') := by
  obtain ⟨σ', ρ', hsrc, h0, -⟩ := pw_quelle30
  obtain ⟨s12, h12, hrip12, hs12⟩ := laufBytes12_stop
  obtain ⟨n, s', hrun, -, hnk, hfin⟩ := erste_stop_ordnung pwCfg pwL pwCerts pwSrc pwBytes
    pw_validate pw_layoutSep pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
    pw_code rfl pw_worldRep pw_envRepr30 12 s12 h12 hs12
  exact ⟨s12, pw_validate, pw_layoutSep, pw_code, rfl, pw_worldRep, pw_envRepr30,
    ⟨σ', ρ', hsrc, rfl, h0⟩, h12, hrip12, hs12, n, s', hrun, hnk, hfin⟩

/-- JOINT WITNESS for `budget_unabhaengig`: the optimised witness block
    lowers (accepted), its source run changes memory 7 -> 35, and the
    outcome at budget 0 is the outcome at budget 7. -/
theorem budget_unabhaengig_zeuge :
    ∃ (b : Block pwD pwV false pwCtx [] []) (prog : List Befehl),
      senkBlock pwCfg pwL 0 b = some prog ∧
      (∃ σ' ρ', execBlock pwO 0 pwR b pwSigma pwEnv30 = .ok σ' ρ' ∧
        (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35) ∧
      execBlock pwO 0 pwR b pwSigma pwEnv30 = execBlock pwO 7 pwR b pwSigma pwEnv30 := by
  obtain ⟨σ', ρ', hsrc, h0, -⟩ := pw_quelle30
  have hopt : execBlock pwO 0 pwR (optimise pwCerts pwSrc) pwSigma pwEnv30 = .ok σ' ρ' := by
    rw [optimise_sound pwCerts pwSrc pwO 0 pwR pwSigma pwEnv30]
    exact hsrc
  exact ⟨optimise pwCerts pwSrc, pwProg, pw_senkBlock, ⟨σ', ρ', hopt, rfl, h0⟩,
    budget_unabhaengig pwCfg pwL pwO pwR (optimise pwCerts pwSrc) 0 pwProg pw_senkBlock
      pwSigma pwEnv30 0 7⟩

/-! ## 6. Probes: the budgeted runner on honest and tampered states

    The tampered memory (`pwMemFalsch`, one forged byte) stops the
    budgeted runner at step zero; the honest program runs its whole
    budget clean and stops only at the code end. -/

/-- TAMPERED MEMORY STOPS AT STEP ZERO: the budgeted runner reports
    `stopp`, never a silent divergence. -/
theorem gift_stopp_ist_stopp :
    laufBudget 5 { pwStart 30 with speicher := pwMemFalsch } =
      .stopp 0 { pwStart 30 with speicher := pwMemFalsch } := by
  have hb : byteschritt { pwStart 30 with speicher := pwMemFalsch } = .verweigert := by
    cases h : byteschritt { pwStart 30 with speicher := pwMemFalsch } with
    | verweigert => rfl
    | weiter s' =>
      have hgift := gift_lauf_verweigert
      simp [ausgangRip, h] at hgift
  simp only [laufBudget, hb]

/-- THE HONEST PREFIX RUNS CLEAN: five budgeted steps finish without a
    stop, on the same state the plain run reaches. -/
theorem gift_fertig_laueft : ∃ s5, laufBudget 5 (pwStart 30) = .fertig 5 s5 ∧
    laufBytes 5 (pwStart 30) = .weiter s5 := by
  obtain ⟨s1, h5, -, -⟩ := laufBytes_add_zeuge
  obtain ⟨k, s'', hfb, hkk, hss⟩ := laufBudget_fertig_von 5 (pwStart 30) s1 h5
  cases hkk
  cases hss
  exact ⟨s1, hfb, h5⟩

/-- NO STOP INSIDE HONEST CODE: the full twelve-step run finishes its
    budget and ends exactly at the code end. The runner refuses to stop
    early on an accepted program. -/
theorem gift_budget_kein_stopp_im_code : ∃ s', laufBudget 12 (pwStart 30) = .fertig 12 s' ∧
    s'.rip = natAdresse 4178 := by
  obtain ⟨s12, h12, hrip12, -⟩ := laufBytes12_stop
  obtain ⟨k, s'', hfb, hkk, hss⟩ := laufBudget_fertig_von 12 (pwStart 30) s12 h12
  cases hkk
  cases hss
  exact ⟨s12, hfb, hrip12⟩

/- CUTS (exactly what is NOT proved here):

    Safety (proved). For a validated lowered block, every finite prefix
    of the fetched byte run succeeds with the code region intact and the
    memory frame kept (`praefix_sicher`); the budgeted runner is faithful
    (`laufBudget_fertig`, `laufBudget_stopp`) and refuses to step past a
    stop (`laufBudget_stopp_stabil`); the target never stops before the
    corresponding end (`erste_stop_ordnung`); the source outcome is the
    same at every budget (`budget_unabhaengig`), so with
    `pipeline_ausgang` there is no budget stop on either side for
    accepted programs.

    Termination (not claimed here). That an accepted block's run ends at
    all is inherited from `senkBlock_korrektC` per validated program;
    this file adds no termination argument, and infinite traces past the
    corresponding end are not modelled: past the end the byte machine
    fetches whatever the memory holds there, which needs the image stop
    premise (`PipelineImage`: non-executable byte after the code, checked
    exit stubs). A stop strictly past the corresponding end (`k > n` in
    `erste_stop_ordnung`) is accordingly unclaimed at pipeline level.

    Correspondence granularity (not claimed). Mid-run states get no
    source meaning: a half-executed assignment chunk (value code run,
    store pending) corresponds to no `execBlock` prefix, and none is
    invented -- there is no source small-step and no second interpreter
    (architecture decision 594). Correspondence holds at the end
    (`Entspricht`), exactly as in `Pipeline.lean`.

    Progress/fairness (not claimed). The model is sequential single-core
    (`laufBytes`); there is no scheduler, no fairness notion, and no
    claim about concurrent or weak-memory behaviour beyond what
    `Pipeline.lean` already states.

    Fragment and machine (inherited). Everything of the CUTS of
    `Pipeline.lean` still applies: pilot ISA only, integer slots only,
    no loops, no calls, no TSO, no time, model memory. In particular
    `budget_unabhaengig` covers only lowered blocks; that `passes` is
    never consumed does NOT extend to loops or calls (`forever`/`rufAt`
    consume it), which the lowering refuses.

    Witness scope. `laufBytes12_stop` and the `gift_*` probes are
    witness-only observations over `pwMem` by computation; they prove
    nothing for other programs by themselves. -/

#print axioms laufBytes_praefix_erfolg
#print axioms laufBytes_verweigert_plus
#print axioms laufBudget_fertig
#print axioms laufBudget_stopp
#print axioms laufBudget_stopp_stabil
#print axioms laufBudget_fertig_von
#print axioms praefix_sicher
#print axioms erste_stop_ordnung
#print axioms budget_unabhaengig
#print axioms praefix_sicher_zeuge
#print axioms laufBytes12_stop
#print axioms erste_stop_ordnung_zeuge
#print axioms budget_unabhaengig_zeuge
#print axioms gift_stopp_ist_stopp
#print axioms gift_fertig_laueft
#print axioms gift_budget_kein_stopp_im_code

end Gabbro.Grammatik.X86.PipelineInfinite
