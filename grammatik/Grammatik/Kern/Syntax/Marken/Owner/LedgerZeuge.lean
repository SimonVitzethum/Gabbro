module

public import Grammatik.Kern.Syntax.Marken.Owner.Ledger
public import Grammatik.Kern.Syntax.Marken.Owner.Witness
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2

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

namespace Gabbro.Grammatik.OwnerWitness

private def stepProgram : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .cons (.ite .tru .nil .nil) (.ret .empty List.Perm.nil)

private def stepOracle : Orakel D where
  wirkt := fun _ w _ => (w, .empty)
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

private def stepStore : Speicher D :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩
private def stepInit : Faden → Σ f : D.Fn, Env D (D.params f) := fun _ => ⟨0, .nil⟩
private abbrev stepStart := RufStartG stepProgram stepStore stepInit

/-- One executed unfolding preserves the minted owner on a reachable machine. -/
theorem ownerInvG_erreichbar_zeuge : ∃ M : RufMaschineG D,
    RufSchrittG stepProgram stepOracle 0 stepStart 0 M ∧
    RufErreichbarG stepProgram stepOracle 0 stepStart M ∧
    OwnerInvG names minted M [0] := by
  obtain ⟨M, hs, _⟩ := w_endeEntf (P := stepProgram) (O := stepOracle)
    (passes := 0) (M := stepStart) (f := 0) rfl
    (.ite .tru .nil .nil) (.ret .empty List.Perm.nil) .nil rfl rfl
  exact ⟨M, hs, .schritt _ _ _ .start hs,
    ownerInvG_erreichbar names minted stepProgram stepOracle 0 stepStart [0]
      mint_valid_zeuge M (.schritt _ _ _ .start hs)⟩

end Gabbro.Grammatik.OwnerWitness
