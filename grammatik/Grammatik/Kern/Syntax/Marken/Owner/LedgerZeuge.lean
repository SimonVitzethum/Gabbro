module

public import Grammatik.Kern.Syntax.Marken.Owner.Ledger
public import Grammatik.Kern.Syntax.Marken.Owner.Witness

@[expose] public section

namespace Gabbro.Grammatik.OwnerWitness

/-! ## Non-degenerate witness: the ghost ledger on an arbitrary run

    The base ledger `minted` is non-degenerate: its mint authority is spent
    and it holds a live grant for the declared mark and stage
    (`mint_grant_zeuge`). The ghost ledger of EVERY run — including every
    reachable one — is that ledger, since no recorded event carries an owner
    payload while `RufPasst.ownerReady` refuses nonempty flows. A witness
    tying the mint to one executed foreign call needs the C08
    software-call transition, which is still open by design. -/

/-- The ghost ledger of any machine is the valid base ledger. -/
theorem ownerLedger_zeuge_valid (M : RufMaschineG D) (threads : List Faden) :
    OwnerInvG names minted M threads := by
  unfold OwnerInvG
  rw [ownerLedger_eq_base]
  exact mint_valid_zeuge

/-- The spent authority survives every run: the mint cannot fire twice. -/
theorem ownerLedger_zeuge_spent (M : RufMaschineG D) (threads : List Faden) :
    (ownerLedgerOf names minted M threads).spent mint.mark = true := by
  rw [ownerLedger_eq_base]
  exact OwnerState.mint_spends mint_step

/-- The live grant survives every run: the minted owner stays held. -/
theorem ownerLedger_zeuge_grant (M : RufMaschineG D) (threads : List Faden) :
    (ownerLedgerOf names minted M threads).owns names root token := by
  rw [ownerLedger_eq_base]
  exact mint_grant_zeuge.2.1

/-- On every reachable run the ghost ledger is conserved. -/
theorem ownerLedger_zeuge_run (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (M : RufMaschineG D) (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (threads : List Faden) : OwnerInvG names minted M threads :=
  ownerInvG_erreichbar names minted P O passes (RufStartG P sp init) threads
    mint_valid_zeuge M hr

end Gabbro.Grammatik.OwnerWitness
