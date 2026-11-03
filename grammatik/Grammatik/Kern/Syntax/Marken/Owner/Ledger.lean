module

public import Grammatik.Kern.Syntax.Marken.Owner.Activation
public import Grammatik.Kern.Syntax.Marken.Owner.InvocationFlow
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T2
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3
public import Grammatik.Nebenlaeufigkeit.Allgemein.Threads.FadenMaschine

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## The owner ledger as a ghost function of the run

    The lead decision (C09): no positional field is added to `RufMaschineG`
    (it would break ~170 literals). The ledger is a GHOST FUNCTION OF THE
    RUN: a fold over the recorded call-log events of the threads named by the
    caller (in practice the threads of `M.lauf`), read off `RufMaschineG`
    (`(M.faeden t).log`) and `RufEreignisF`.

    `RufPasst.ownerReady` is the checked call-boundary escrow
    (`OwnerFlow.EscrowReady`): nonempty flows are admitted with their
    inputs in hand. Recorded events still carry no owner payload, so the
    fold step stays the identity and the ghost ledger is stable along every
    `RufSchrittG` step; the per-call dynamic replay — borrow/transfer at the
    push, restore/transfer-back at the return on either channel — is
    `Owner/Escrow.lean`, proved from the `OwnerState`/`OwnerInvocation`
    lemmas below. The mint itself still needs the C08 software-call
    transition. -/

/-- One recorded call-log event contributes no owner payload to the ghost
    fold; the per-call escrow replay reads the callee flow, not the event. -/
def ownerFoldStep (s : OwnerState D) : RufEreignisF D → OwnerState D
  | .eintritt _ _ _ => s
  | .rueck _ _ _ _ _ => s
  | .why _ _ _ _ _ => s

/-- Fold one thread's recorded call log into the ghost ledger. -/
def ownerThreadStep (M : RufMaschineG D) (s : OwnerState D) (t : Faden) : OwnerState D :=
  ((M.faeden t).log).foldl ownerFoldStep s

/-- The ghost ledger of a run: the base ledger folded over the recorded
    call-log events of `threads`. Reads `RufMaschineG` and `RufEreignisF`. -/
def ownerLedgerOf (N : OwnerNamespace D) (base : OwnerState D) (M : RufMaschineG D)
    (threads : List Faden) : OwnerState D :=
  threads.foldl (ownerThreadStep M) base

/-- **The conservation invariant over G**: the ghost ledger of the run is a
    valid nominal ledger: every owner is held by exactly one place, spent
    mint authority never returns, and loans restore exactly (the two halves
    are `ownerLedger_access_unique` and `push_borrow_pop_restore` below). -/
def OwnerInvG (N : OwnerNamespace D) (base : OwnerState D) (M : RufMaschineG D)
    (threads : List Faden) : Prop :=
  (ownerLedgerOf N base M threads).Valid N

theorem foldStep_id (s : OwnerState D) (ev : RufEreignisF D) :
    ownerFoldStep s ev = s := by
  cases ev <;> rfl

theorem foldl_ledger_id (s : OwnerState D) : ∀ log : List (RufEreignisF D),
    log.foldl ownerFoldStep s = s
  | [] => rfl
  | ev :: rest => by
      have h : ownerFoldStep s ev = s := foldStep_id s ev
      rw [show (ev :: rest).foldl ownerFoldStep s =
        rest.foldl ownerFoldStep (ownerFoldStep s ev) from rfl]
      rw [h]
      exact foldl_ledger_id s rest

theorem ownerThreadStep_id (M : RufMaschineG D) (s : OwnerState D) (t : Faden) :
    ownerThreadStep M s t = s :=
  foldl_ledger_id s _

theorem ownerLedger_fold_eq (M : RufMaschineG D) (s : OwnerState D) :
    ∀ ts : List Faden, ts.foldl (ownerThreadStep M) s = s
  | [] => rfl
  | t :: rest => by
      have h : ownerThreadStep M s t = s := ownerThreadStep_id M s t
      rw [show (t :: rest).foldl (ownerThreadStep M) s =
        rest.foldl (ownerThreadStep M) (ownerThreadStep M s t) from rfl]
      rw [h]
      exact ownerLedger_fold_eq M s rest

/-- The ghost ledger is the base ledger: no recorded event carries an owner
    payload while nonempty flows are refused. -/
theorem ownerLedger_eq_base (N : OwnerNamespace D) (base : OwnerState D)
    (M : RufMaschineG D) (threads : List Faden) :
    ownerLedgerOf N base M threads = base :=
  ownerLedger_fold_eq M base threads

/-- Generic preservation: two machines with the same ghost ledger satisfy
    `OwnerInvG` together. Every step below closes through this lemma; most
    steps leave the recorded logs unchanged, and a push or pop appends one
    event whose fold step is the identity. -/
theorem ownerLedger_of_ledger_eq (N : OwnerNamespace D) (base : OwnerState D)
    (M M' : RufMaschineG D) (threads : List Faden)
    (h : ownerLedgerOf N base M' threads = ownerLedgerOf N base M threads)
    (hI : OwnerInvG N base M threads) : OwnerInvG N base M' threads := by
  unfold OwnerInvG at hI ⊢
  rw [h]
  exact hI

/-- Initial lemma: the start machine carries the base ledger. -/
theorem ownerInvG_start (N : OwnerNamespace D) (base : OwnerState D)
    (P : Programm D) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (threads : List Faden) (hv : base.Valid N) :
    OwnerInvG N base (RufStartG P sp init) threads := by
  unfold OwnerInvG
  rw [ownerLedger_eq_base]
  exact hv

/-- Preservation by EVERY `RufSchrittG` step, one goal per constructor of
    `RufSchrittG1` … `RufSchrittG6` (the union is `RufSchrittG`, T2.lean).
    Pushes (`ruf`, `rufDann`, `dannCallInd`, `rufCallInd`, `dannBindCall`,
    `dannBindCallInd`, `dannBindCallElse`) append one `eintritt` event; pops
    (`rueck`, `rueckBind`, `dannRet`, `rueckCons`, `dannRetBind`,
    `rueckConsBind`, `rueckGrund`, `rueckConsGrund`, `dannRetGrund`) append
    one `rueck`/`why` event; every other rule leaves the acting thread's log
    — and every other thread's state (`rufSchrittG_passt_anders`) — alone.
    All close generically through `ownerLedger_eq_base`, since the appended
    event carries no owner payload while `RufPasst.ownerReady` holds. -/
theorem ownerInvG_schritt {N : OwnerNamespace D} {base : OwnerState D}
    {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {f : Faden} {M' : RufMaschineG D}
    {threads : List Faden} (hI : OwnerInvG N base M threads)
    (hs : RufSchrittG P O passes M f M') : OwnerInvG N base M' threads := by
  have hbase : base.Valid N := by
    unfold OwnerInvG at hI
    rw [ownerLedger_eq_base] at hI
    exact hI
  have close : ∀ {M'' : RufMaschineG D}, OwnerInvG N base M'' threads := by
    intro M''
    unfold OwnerInvG
    rw [ownerLedger_eq_base]
    exact hbase
  rcases hs with (h | h | h | h | h | h | h) <;> cases h <;> exact close

/-- Reachability induction: every machine G reaches from `M0` keeps the ghost
    ledger valid. -/
theorem ownerInvG_erreichbar (N : OwnerNamespace D) (base : OwnerState D)
    (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D)
    (threads : List Faden) (hv : base.Valid N) (M : RufMaschineG D)
    (hr : RufErreichbarG P O passes M0 M) : OwnerInvG N base M threads := by
  induction hr with
  | start => exact ownerInvG_start N base P _ _ threads hv
  | schritt _ _ _ _ hs ih => exact ownerInvG_schritt ih hs

/-! ## Edge compatibility: transfer, borrow, restore

    The ghost ledger is stable because no edge carries a payload yet. When a
    canonical push/pop pair IS authorized, the ledger moves exactly through
    the existing `OwnerState` operations, using the `OwnerInvocation`
    evidence for each edge kind. -/

/-- A canonical move hands over a fresh grant for the same owner and retires
    every saved use of the old grant. -/
theorem push_transfer_valid {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} {N : OwnerNamespace D}
    {s s' : OwnerState D} {t t' : OwnerToken D}
    (push : c.Push P O passes M M') (hv : s.ledger.valid)
    (h : push.transfer N s t = some (s', t')) :
    s'.ledger.valid ∧ s'.owns N c.frame t' ∧ t'.mark = t.mark ∧ t'.stage = t.stage ∧
      (∀ frame, ¬ s'.access N frame t) ∧ s'.spent = s.spent :=
  OwnerState.transfer_grant hv h

/-- A canonical borrow admits one accessor and disables the lender. -/
theorem push_borrow_valid {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} {N : OwnerNamespace D}
    {s s' : OwnerState D} {t : OwnerToken D}
    (push : c.Push P O passes M M') (hv : s.ledger.valid)
    (h : push.borrow N s t = some s') :
    s'.ledger.valid ∧ s'.access N c.frame t ∧ ¬ s'.access N c.caller t ∧
      ¬ s'.owns N c.frame t ∧ s'.spent = s.spent ∧ s'.stage = s.stage :=
  OwnerState.borrow_grant hv h

/-- A canonical return restores precisely the saved identity and stage. -/
theorem pop_restore_valid {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} {N : OwnerNamespace D}
    {s s' : OwnerState D} {t : OwnerToken D}
    (pop : c.Return P O passes M M') (hv : s.ledger.valid)
    (h : pop.restore N s t = some s') :
    s'.ledger.valid ∧ s'.access N c.caller t ∧ s'.spent = s.spent ∧ s'.stage = s.stage :=
  OwnerState.returnBorrow_grant hv h

/-- Loans restore exactly: a checked borrow has an exact inverse at its
    matching return, innermost borrow outward for nested loans. -/
theorem push_borrow_pop_restore {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M0 M1 M2 M3 : RufMaschineG D} {N : OwnerNamespace D}
    {s loaned : OwnerState D} {t : OwnerToken D}
    (push : c.Push P O passes M0 M1) (pop : c.Return P O passes M2 M3)
    (hv : s.ledger.valid) (hb : push.borrow N s t = some loaned) :
    pop.restore N loaned t = some s :=
  OwnerInvocation.borrow_restore push pop hv hb

/-- Every owner is held by exactly one place in the ghost ledger. -/
theorem ownerLedger_access_unique {N : OwnerNamespace D} {base : OwnerState D}
    {M : RufMaschineG D} {threads : List Faden} {f g : Faden} {t : OwnerToken D}
    (hf : (ownerLedgerOf N base M threads).access N f t)
    (hg : (ownerLedgerOf N base M threads).access N g t) : f = g := by
  have e := ownerLedger_eq_base N base M threads
  rw [e] at hf hg
  exact OwnerState.access_unique hf hg

/-- Uniqueness is nominal: a copied handle cannot supply a second accessor. -/
theorem ownerLedger_access_owner_unique {N : OwnerNamespace D} {base : OwnerState D}
    {M : RufMaschineG D} {threads : List Faden} {f g : Faden} {t u : OwnerToken D}
    (hf : (ownerLedgerOf N base M threads).access N f t)
    (hu : (ownerLedgerOf N base M threads).access N g u) (hm : t.mark = u.mark) :
    f = g ∧ t.stage = u.stage := by
  have e := ownerLedger_eq_base N base M threads
  rw [e] at hf hu
  exact OwnerState.access_owner_unique hf hu hm

/-! ## Spawn: the thread machine over G -/

/-- Preservation over one thread-machine step: `lauf` is a G step, `start`
    and `kind` spawn dormant slots and `join` ends the wait, all three
    leaving the G state — hence the ghost ledger — alone. -/
theorem ownerInvF_schritt_G {N : OwnerNamespace D} {base : OwnerState D}
    {P : Programm D} {O : Orakel D} {passes : Nat}
    {K K' : FadenMaschine D} {threads : List Faden}
    (hI : OwnerInvG N base K.m threads) (hs : FadenSchritt P O passes K K') :
    OwnerInvG N base K'.m threads := by
  cases hs with
  | lauf K f M' hf hw hs' => exact ownerInvG_schritt hI hs'
  | start K p cs hp hw hfrei hcs => exact hI
  | kind K p c hp hw hc => exact hI
  | join K p hp hw hf => exact hI

end Gabbro.Grammatik
