module

public import Grammatik.Kern.Syntax.Marken.Owner.Ledger
public import Grammatik.Speichermodell.Atomar.AtomarLauf
public import Grammatik.Speichermodell.Maschine.GXMaschine

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## The owner ledger over GX

    The ghost ledger reads only recorded call logs, never presented memory,
    so a GX step — G on a memory agreeing outside the shared atomics `Tg` —
    threads it through unchanged, the way the lock legs (`sperrWechsel_ausX`,
    `sperrSicht_ausX`) thread memory facts through. `Tg` is carried for the
    shape of those transports; the ledger proof never case-splits on it. -/

/-- **The conservation invariant over GX**: the same ghost ledger, on runs
    whose shared-atomics reads the weak memory answers. -/
def OwnerInvGX (N : OwnerNamespace D) (base : OwnerState D)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M : RufMaschineG D)
    (threads : List Faden) : Prop :=
  (ownerLedgerOf N base M threads).Valid N

/-- A G invariant is a GX invariant: the ledger is identical on both. -/
theorem ownerInvGX_of_G {N : OwnerNamespace D} {base : OwnerState D}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M : RufMaschineG D} {threads : List Faden}
    (hI : OwnerInvG N base M threads) : OwnerInvGX N base Tg M threads :=
  hI

/-- Preservation by every GX step: the inner G step keeps the ghost ledger,
    and the presented-memory change touches no recorded log. -/
theorem ownerInvGX_schritt {N : OwnerNamespace D} {base : OwnerState D}
    {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {M : RufMaschineG D} {u : Faden} {M' : RufMaschineG D} {threads : List Faden}
    (hI : OwnerInvGX N base Tg M threads)
    (hs : RufSchrittGX P O passes Tg M u M') : OwnerInvGX N base Tg M' threads := by
  have hbase : base.Valid N := by
    unfold OwnerInvGX at hI
    rw [ownerLedger_eq_base] at hI
    exact hI
  unfold OwnerInvGX
  rw [ownerLedger_eq_base]
  exact hbase

/-- Reachability induction over GX runs. -/
theorem ownerInvGX_erreichbar (N : OwnerNamespace D) (base : OwnerState D)
    (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M0 : RufMaschineG D) (threads : List Faden) (hv : base.Valid N)
    (M : RufMaschineG D) (hr : RufErreichbarGX P O passes Tg M0 M) :
    OwnerInvGX N base Tg M threads := by
  induction hr with
  | start =>
      unfold OwnerInvGX
      rw [ownerLedger_eq_base]
      exact hv
  | schritt _ _ _ _ hs ih => exact ownerInvGX_schritt ih hs

/-- Preservation over one thread-machine step over GX: `lauf` is a GX step;
    spawn, kind and join leave the G state alone. -/
theorem ownerInvF_schritt_X {N : OwnerNamespace D} {base : OwnerState D}
    {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {K K' : FadenMaschine D} {threads : List Faden}
    (hI : OwnerInvGX N base Tg K.m threads) (hs : FadenSchrittX P O passes Tg K K') :
    OwnerInvGX N base Tg K'.m threads := by
  cases hs with
  | lauf f M' hf hw hs' => exact ownerInvGX_schritt hI hs'
  | start p cs hp hw hfrei hcs => exact hI
  | kind p c hp hw hc => exact hI
  | join p hp hw hf => exact hI

/-- A spawn, kind or join step leaves the G state alone; only `lauf` moves
    it. Used by admission: a dormant start cannot restart the mint. -/
theorem fadenSpawn_m_X {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} {K K' : FadenMaschine D}
    (hs : FadenSchrittX P O passes Tg K K') :
    K'.m = K.m ∨
      ∃ (f : Faden) (M' : RufMaschineG D), RufSchrittGX P O passes Tg K.m f M' := by
  cases hs with
  | lauf f M' hf hw hs' => exact Or.inr ⟨f, M', hs'⟩
  | start p cs hp hw hfrei hcs => exact Or.inl rfl
  | kind p c hp hw hc => exact Or.inl rfl
  | join p hp hw hf => exact Or.inl rfl

end Gabbro.Grammatik
