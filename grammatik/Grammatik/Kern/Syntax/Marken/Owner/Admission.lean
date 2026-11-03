module

public import Grammatik.Kern.Syntax.Marken.Owner.LedgerGX
public import Grammatik.Zielsatz.Kern.Spec.Teil1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## Root and spawn admission for the one-shot mint

    Design (C09): exactly one syntactic mint site outside all loops, a root
    with no caller and no address-taking, one declared occurrence across
    `E.starts ++ E.gestartet`, and no repeated or spawned execution of that
    occurrence. `EinzelnPool` is not sufficient: pool-safe roots still cannot
    mint twice.

    This file decides the checkable part (`ownerB`) and proves its soundness
    (`OwnerAdmission`), the at-most-once execution along the runtime
    (`owner_root_once`, from `Laufzeit.einmal`), and that spawns cannot
    restart the mint (`owner_step_mint_refused_*`: a spawn leaves the G state
    alone, spent authority stays spent).

    NOT wired into `Akzeptiert`/`AkzeptiertSpec(X)` yet: mint admission stays
    closed until the C08 software-call transition connects the canonical mint
    rule. (Call-boundary escrow for owner flows is `RufPasst.ownerReady`.) -/

/-- **Owner admission**: the root carrying the distinguished mint is
    declared once, has no caller in the checked graph, starts clean, and is
    the unit's only mint origin. -/
structure OwnerAdmission [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn)
    (d : OwnerMintDecl D) (ws : List D.Fn) : Prop where
  root_declared : d.root ∈ ws
  root_single : ((ws.filter (fun v => decide (v = d.root)))).length = 1
  root_no_caller : ∀ f ∈ fs, ruftB P f d.root = false
  root_clean : D.haelt d.root = [] ∧ D.gruende d.root = 0

/-- The admission, decided over the member list `fs`. -/
def ownerB [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn)
    (d : OwnerMintDecl D) (ws : List D.Fn) : Bool :=
  decide (d.root ∈ ws) &&
    decide (((ws.filter (fun v => decide (v = d.root)))).length = 1) &&
    fs.all (fun f => decide (ruftB P f d.root = false)) &&
    decide (D.haelt d.root = []) && decide (D.gruende d.root = 0)

theorem ownerB_iff [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn)
    (d : OwnerMintDecl D) (ws : List D.Fn) :
    ownerB P fs d ws = true ↔ d.root ∈ ws ∧
      ((ws.filter (fun v => decide (v = d.root)))).length = 1 ∧
      (∀ f ∈ fs, ruftB P f d.root = false) ∧
      D.haelt d.root = [] ∧ D.gruende d.root = 0 := by
  simp only [ownerB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

theorem ownerAdmission_of_ownerB [DecidableEq D.Fn] (P : Programm D)
    (fs : List D.Fn) (d : OwnerMintDecl D) (ws : List D.Fn)
    (h : ownerB P fs d ws = true) : OwnerAdmission P fs d ws := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (ownerB_iff P fs d ws).mp h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- One declared occurrence is not two: a singly listed root is not
    `Mehrfach`, so `Laufzeit.einmal` cannot place it on two threads. -/
theorem owner_single_not_twice [DecidableEq D.Fn] (d : OwnerMintDecl D)
    (ws : List D.Fn)
    (hsingle : ((ws.filter (fun v => decide (v = d.root)))).length = 1) :
    ¬ Zielsatz.Mehrfach ws d.root := by
  intro hM
  have hlt : 1 < ((ws.filter (fun v => decide (v = d.root)))).length :=
    mehrfach_filter.mp hM
  omega

/-- The admitted root runs on at most one thread: two threads starting at
    the root contradict `Laufzeit.einmal` with the single occurrence. -/
theorem owner_root_once [DecidableEq D.Fn] (E : Zielsatz.Einheit D)
    (d : OwnerMintDecl D) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit E sp init)
    (hsingle : (((Zielsatz.Einheit.ws E).filter
      (fun v => decide (v = d.root)))).length = 1)
    {t u : Faden} (hne : t ≠ u) (ht : (init t).1 = some d.root)
    (hu : (init u).1 = some d.root) : False := by
  have hM := hL.einmal t u hne (by rw [ht, hu])
  rcases hM with hnone | ⟨w, hw, hMw⟩
  · rw [ht] at hnone
    cases hnone
  · rw [ht] at hw
    have hwroot : w = d.root := by simpa using hw.symm
    subst hwroot
    exact owner_single_not_twice d _ hsingle hMw

/-- A spawn, kind or join step over G leaves the G state alone; only `lauf`
    moves it. -/
theorem fadenSpawn_m_G {P : Programm D} {O : Orakel D} {passes : Nat}
    {K K' : FadenMaschine D} (hs : FadenSchritt P O passes K K') :
    K'.m = K.m ∨
      ∃ (f : Faden) (M' : RufMaschineG D), RufSchrittG P O passes K.m f M' := by
  cases hs with
  | lauf f M' hf hw hs' => exact Or.inr ⟨f, M', hs'⟩
  | start p cs hp hw hfrei hcs => exact Or.inl rfl
  | kind p c hp hw hc => exact Or.inl rfl
  | join p hp hw hf => exact Or.inl rfl

/-- No thread-machine step over G restarts the mint: the ghost ledger is the
    base ledger on both sides, so spent authority stays spent. In particular
    a dormant start spawned at run time cannot mint again. -/
theorem owner_step_mint_refused_G {P : Programm D} {O : Orakel D} {passes : Nat}
    {N : OwnerNamespace D} {base : OwnerState D} {d : OwnerMintDecl D}
    {K K' : FadenMaschine D} {threads : List Faden} {f : ArenaOwnership.Frame}
    (hs : FadenSchritt P O passes K K')
    (hspent : (ownerLedgerOf N base K.m threads).spent d.mark = true) :
    OwnerState.recordMint N d (ownerLedgerOf N base K'.m threads) f = none := by
  have heq : ownerLedgerOf N base K'.m threads = base :=
    ownerLedger_eq_base N base K'.m threads
  have heq2 : ownerLedgerOf N base K.m threads = base :=
    ownerLedger_eq_base N base K.m threads
  rw [heq]
  have hspent' : base.spent d.mark = true := by
    rw [← heq2]
    exact hspent
  exact OwnerState.mint_spent_refused N d base f hspent'

/-- No thread-machine step over GX restarts the mint, for the same reason:
    the ledger is log-derived and spawns move no log. -/
theorem owner_step_mint_refused_X {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} {N : OwnerNamespace D} {base : OwnerState D}
    {d : OwnerMintDecl D} {K K' : FadenMaschine D} {threads : List Faden}
    {f : ArenaOwnership.Frame} (hs : FadenSchrittX P O passes Tg K K')
    (hspent : (ownerLedgerOf N base K.m threads).spent d.mark = true) :
    OwnerState.recordMint N d (ownerLedgerOf N base K'.m threads) f = none := by
  have heq : ownerLedgerOf N base K'.m threads = base :=
    ownerLedger_eq_base N base K'.m threads
  have heq2 : ownerLedgerOf N base K.m threads = base :=
    ownerLedger_eq_base N base K.m threads
  rw [heq]
  have hspent' : base.spent d.mark = true := by
    rw [← heq2]
    exact hspent
  exact OwnerState.mint_spent_refused N d base f hspent'

end Gabbro.Grammatik
