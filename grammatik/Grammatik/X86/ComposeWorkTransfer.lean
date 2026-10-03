/-
  File:      Grammatik/X86/ComposeWorkTransfer.lean
  Subject:   Work-transfer composition closing (lane 835).

  Closes the one named producer/consumer gap between declared source
  costs and actual machine work through the separate transfer:

  PRODUCER (DerivedWorkBound, lane 654): `deckung_fragment` derives the
    `Deckung` work coverage for the covered lowering fragment
    (`senkFrag` + one slot store) from the generated instruction count,
    closing the `Deckung` leg that BudgetExecution leaves OPEN.
  CONSUMER (BudgetExecution, lane 572): `budgetAusfuehrung_transfer`
    composes named per-form hardware costs (`laufKosten_schranke`,
    HardwareAssumptions lane 434) with a `Deckung` into target-time
    coverage `t <= B * k`, without re-summing the summary.
  SCHEMA (CostSummary lane 347, TimeTransfer lane 547): the admitted
    `fragmentSummary`, `expandBound`, `targetWork`, and the refusal
    halves reused below.

  Nothing is re-proved: the one `targetWork`, the one `laufKosten`
  aggregation, the one `senkFrag`/`senkAssign` lowering and the actual
  `execStmt`/`lauf`/`laufBytes` runs are reused untouched. No new
  interpreter, no second cost model, no IR, no source/checker/Spec/
  goal/emitter edit, no friend-reserved optimiser file.
-/
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.BudgetExecution
import Grammatik.X86.TimeTransfer

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## Closed interface: derived coverage into the separate transfer.

    `BudgetExecution.budgetAusfuehrung_transfer` takes `Deckung` as
    carried data (its CUTS: the lowering correspondence is OPEN there).
    `DerivedWorkBound.deckung_fragment` derives exactly that `Deckung`
    from a successful fragment lowering. The composition below plugs
    the derived producer into the transfer consumer, generically over
    arbitrary admitted inputs. Units stay separate: `src` counts source
    steps (the `Budget` ops side), `targetWork` counts retired generated
    instructions, `t` counts named target time. -/

/-- MAIN: a lowered assignment of the covered fragment whose generated
    code aggregates to named time `t` under profile `p` is covered in
    target time by the admitted fragment summary over the source budget.
    Proved by composing the derived `Deckung` producer (654) with the
    transfer consumer (572); every premise is used. -/
theorem ComposeWorkTransfer_verbindung {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (p : HardwareProfil) (src B t : Nat)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (hsrc : 1 ≤ src)
    (hCost : laufKosten p
      (decodiertZu (prog ++ [Befehl.store64 baseR dst disp])) = some t)
    (hb : ∀ d ∈ decodiertZu (prog ++ [Befehl.store64 baseR dst disp]),
      ∃ c, schrittKosten p d = some c ∧ c ≤ B) :
    ∀ k, expandBound fragmentSummary src = some k → t ≤ B * k := by
  have hDeck := deckung_fragment abb e dst tmp baseR disp src prog hsenk hsrc
  exact budgetAusfuehrung_transfer fragmentSummary p _ src B t hCost hb hDeck

/-! ## Closed declared-cost bound.

    The summary expansion over the source budget is `src * 4`
    (`fragmentSummary_expand`: uniform maximum 4, honest zero
    spill/fence), so the composed transfer closes declared source costs
    to the concrete machine-time bound `t <= B * (src * 4)`. -/

/-- CLOSED: the composed transfer at the declared expansion -- declared
    source budget `src` gives concrete target-time coverage. Every
    premise feeds the composed connection. -/
theorem ComposeWorkTransfer_geschlossen {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (p : HardwareProfil) (src B t : Nat)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (hsrc : 1 ≤ src)
    (hCost : laufKosten p
      (decodiertZu (prog ++ [Befehl.store64 baseR dst disp])) = some t)
    (hb : ∀ d ∈ decodiertZu (prog ++ [Befehl.store64 baseR dst disp]),
      ∃ c, schrittKosten p d = some c ∧ c ≤ B) :
    t ≤ B * (src * 4) := by
  have hT := ComposeWorkTransfer_verbindung abb e dst tmp baseR disp p
    src B t prog hsenk hsrc hCost hb
  exact hT _ (fragmentSummary_expand src)

/-! ## Refusals propagated through the composed step.

    Three planted cases, each reusing the accepted refusal by name: an
    underestimated work bound below the shortest generated assignment
    (2) covers nothing; an unbounded retry site behind a constant bound
    refuses summary AND transfer admission together; a prefix whose head
    form carries no named cost admits no aggregation, hence no composed
    instance runs on it. -/

/-- UNDERESTIMATED-WORK REFUSAL through the composed step: no admitted
    assignment is covered by a bound below 2. Every premise is used. -/
theorem ComposeWorkTransfer_verweigert_knapp {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (prog code : List Befehl)
    (hsenk : senkFrag abb e dst tmp = some prog)
    (hcode : senkAssign abb e dst tmp baseR disp = some code)
    (k : Nat) (hk : k < 2) :
    ¬ targetWork ((decodiertZu code).map fun d => d.befehl) ≤ k :=
  arbeit_knapp_verweigert abb e dst tmp baseR disp prog code hsenk hcode k hk

/-- UNBOUNDED-RETRY REFUSAL through the composed step: the fragment
    summary with its retry bound removed refuses admission AND transfer
    together -- a CAS retry loop never gets a free constant. -/
theorem ComposeWorkTransfer_verweigert_retry (p : HardwareProfil) :
    kostenSummeOk { fragmentSummary with retryBound := none } = false ∧
    zeitTransferZulaessig { fragmentSummary with retryBound := none } p =
      false :=
  kein_freier_versuch_fragment p

/-- UNPRICED-FORM REFUSAL through the composed step: a prefix whose head
    form the profile refuses admits no successful aggregation -- hence
    no composed time bound runs on it. -/
theorem ComposeWorkTransfer_verweigert_ohneKosten (p : HardwareProfil)
    (d : Decodiert) (rest : List Decodiert)
    (h : schrittKosten p d = none) :
    ¬ ∃ t, laufKosten p (d :: rest) = some t :=
  zeitTransfer_verweigert_ohneKosten p d rest h

/-! ## Joint witness: one table, one writing lowering, real runs.

    All witnesses share the one non-degenerate `witD628` package
    (`Paket`, lane 654): the contract writes the table, the source
    `execStmt` run moves the slot `12 -> 42`, and the fetched-byte
    target run observably changes memory. Each `_zeuge` instantiates ALL
    premises of its theorem jointly on this package and proves the
    conclusion through the composed step -- a conjunction of checks is
    never passed off as execution. -/

/-- Joint witness for the main composition, with the time bound
    `7 <= 3 * k` through the composed step. -/
theorem ComposeWorkTransfer_verbindung_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      1 ≤ 1 ∧
      laufKosten profilZeuge
        (decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)])) = some 7 ∧
      (∀ d ∈ decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)]),
        ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3) ∧
      (∀ k, expandBound fragmentSummary 1 = some k → 7 ≤ 3 * k) ∧
      Paket := by
  refine ⟨[Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 12),
      Befehl.addReg64 Register.rax Register.rcx],
    witSenk628, Nat.le_refl 1, hCost_wit, hb_wit, ?_,
    paket_nicht_degeneriert⟩
  exact ComposeWorkTransfer_verbindung witAbb628 witE628 Register.rax
    Register.rcx Register.rbx (BitVec.ofNat 32 0) profilZeuge 1 3 7 _
    witSenk628 (Nat.le_refl 1) hCost_wit hb_wit

/-- Joint witness for the closed declared-cost bound `7 <= 3 * (1 * 4)`. -/
theorem ComposeWorkTransfer_geschlossen_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      1 ≤ 1 ∧
      laufKosten profilZeuge
        (decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)])) = some 7 ∧
      (∀ d ∈ decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)]),
        ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3) ∧
      7 ≤ 3 * (1 * 4) ∧
      Paket := by
  refine ⟨[Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 12),
      Befehl.addReg64 Register.rax Register.rcx],
    witSenk628, Nat.le_refl 1, hCost_wit, hb_wit, ?_,
    paket_nicht_degeneriert⟩
  exact ComposeWorkTransfer_geschlossen witAbb628 witE628 Register.rax
    Register.rcx Register.rbx (BitVec.ofNat 32 0) profilZeuge 1 3 7 _
    witSenk628 (Nat.le_refl 1) hCost_wit hb_wit

/-- Joint witness for the underestimated-work refusal: bound 1 covers no
    composed assignment. -/
theorem ComposeWorkTransfer_verweigert_knapp_zeuge :
    ∃ (prog code : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      senkAssign witAbb628 witE628 Register.rax Register.rcx Register.rbx
        (BitVec.ofNat 32 0) = some code ∧
      1 < 2 ∧
      ¬ targetWork ((decodiertZu code).map fun d => d.befehl) ≤ 1 ∧
      Paket := by
  refine ⟨_, _, witSenk628, witSenkAssign628, by decide,
    ComposeWorkTransfer_verweigert_knapp witAbb628 witE628 Register.rax
      Register.rcx Register.rbx (BitVec.ofNat 32 0) _ _ witSenk628
      witSenkAssign628 1 (by decide),
    paket_nicht_degeneriert⟩

/- CUTS:
    - Closed here (generic): the `Deckung` leg of
      `budgetAusfuehrung_transfer` for the covered fragment, via the
      derived `deckung_fragment`; the declared-cost closed bound, the
      propagated refusals and the joint witness below.
    - OPEN (scheduling, owner: TSO/bridge lanes): which source step the
      summary's `src` counts when several lowered assignments share one
      budget (`kostenTiefF` multiplicities); concurrent interleavings
      and waiting delays are untouched.
    - OPEN (all-source, owners: lowering lanes 599/628): literals,
      variables and one bounded add/sub over atoms, then one slot
      store; everything else refuses (`none`) and carries no bound here.
    - OPEN (timing fidelity, owner: profile lane 434): `t` counts NAMED
      per-form bounds, never measured silicon latencies; `ret` refused.
-/

#print axioms ComposeWorkTransfer_verbindung
#print axioms ComposeWorkTransfer_geschlossen
#print axioms ComposeWorkTransfer_verweigert_knapp
#print axioms ComposeWorkTransfer_verweigert_retry
#print axioms ComposeWorkTransfer_verweigert_ohneKosten
#print axioms ComposeWorkTransfer_verbindung_zeuge
#print axioms ComposeWorkTransfer_geschlossen_zeuge
#print axioms ComposeWorkTransfer_verweigert_knapp_zeuge

end Gabbro.Grammatik.X86
