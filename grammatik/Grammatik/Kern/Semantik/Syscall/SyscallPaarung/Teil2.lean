module

public import Grammatik.Kern.Semantik.Syscall.Syscall
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Syscall.SyscallPaarung.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- The narrow user side: identical contract, but declares NO table
    written -- the kernel's offset bump is outside `Eu`. -/
def swUleer : UserSyscall swD (swD.aparams ()) IoFehler where
  nummer := 1
  abi := schreibAbi
  tab := schreibFehler
  lo := 0
  hi := 8192
  Pu := fun σ ρ => (σ.slots () (swFd ρ) ()).n ≠ 0
  Qu := fun _ _ ans ρ => match ans with
    | .ok v => v ≤ swLen ρ
    | .why _ => True
    | .unerwartet _ => False
  Eu := fun _ => false
  EuG := fun g => nomatch g

/-- Counterexample arguments: `fd = 3`, `len = 8`. -/
def swRho8 : Env swD swParams :=
  .cons (⟨3, by decide, by decide⟩ : Wert swD (.int 0 7))
    (.cons (⟨8, by decide, by decide⟩ : Wert swD (.int 0 8192)) .nil)

/-- Counterexample entry world: every offset slot reads `5` (so `Pk`
    holds: the descriptor is open), empty trace. -/
def swWelt5 : World swD :=
  { slots := fun _ _ _ => ⟨5, by decide, by decide⟩
    globs := fun g => nomatch g
    spur := [] }

/-- Rejection: the kernel writes a table the user side does not declare,
    so some kernel behaviour satisfying `Pk`/`Qk`/`Ek` violates the user
    frame. Concretely: `fd = 3` is open (slot `5`), the kernel answers
    count `5 ≤ len = 8` and bumps the slot to `1` -- inside `Ek`, outside
    the empty `Eu`. -/
theorem syscall_paarung_abgelehnt :
    ∃ (σ σ' : World swD) (ρ : Env swD (swD.aparams ())) (roh : Int),
      swK.Pk σ ρ ∧ swK.Qk σ σ' roh ρ ∧ Rahmen swK.Ek swK.EkG σ σ' ∧
      ¬ Rahmen swUleer.Eu swUleer.EuG σ σ' := by
  have hPk : swK.Pk swWelt5 swRho8 := by
    show (swWelt5.slots () (swFd swRho8) ()).n ≠ 0
    decide
  refine ⟨swWelt5, swWelt5.storeSlot () (swFd swRho8) ()
    (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)), swRho8, 5,
    hPk, .inl ⟨by decide, by decide, rfl⟩, ?_, ?_⟩
  · exact rahmen_storeSlot swK.Ek swK.EkG swWelt5 () (swFd swRho8) ()
      (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)) rfl
  · intro h
    have hn1 : (((swWelt5.storeSlot () (swFd swRho8) ()
        (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192))).slots ()
        (swFd swRho8) ()).n) = 1 := rfl
    have hn5 : ((swWelt5.slots () (swFd swRho8) ()).n) = 5 := rfl
    have heq := h.1 () rfl (swFd swRho8) ()
    have hn := congrArg Zahl.n heq
    rw [hn1, hn5] at hn
    omega

/-! ## 7. From per-axiom pairing to the global oracle bound -/

/-- If every axiom of a declaration is a syscall paired with a kernel entry
    (a per-axiom family of the pairing premises), then `GutO` holds for the
    oracle built from the kernel behaviours: the goal theorem's hardware
    premise `hO` is discharged for a Gabbro-kernel system. Only the
    frame/recording legs of the pairing travel here -- the contract legs
    (`Pu -> Pk`, `Qk -> Qu`) give `PaarGut`'s second conjunct and are not
    needed for the oracle bound, so they are not premises. Every premise is
    load-bearing: `hnum`/`habi` transport each kernel behaviour to its user
    dispatch identity, `hsub`/`hsubG` with `hEu`/`hEuG` widen each kernel
    frame to its declared axiom frame, `hKeff` supplies frame, locks, and
    recording per axiom, `hO` ties the oracle to `K` per axiom. -/
theorem paarung_gibt_gutO (D : Deklaration) (O : Orakel D)
    {A : Type} {Grund : Type} [DecidableEq Grund]
    (k : ∀ a : D.Ax, KernelEintragG A D (D.aparams a))
    (u : ∀ a : D.Ax, UserSyscallG A D (D.aparams a) Grund)
    (K : ∀ a : D.Ax, Nat → A → World D → Env D (D.aparams a) →
      World D → Int → Prop)
    (hnum : ∀ a, (k a).nummer = (u a).nummer)
    (habi : ∀ a, (k a).abi = (u a).abi)
    (hsub : ∀ a t, (k a).Ek t = true → (u a).Eu t = true)
    (hsubG : ∀ a g, (k a).EkG g = true → (u a).EuG g = true)
    (hEu : ∀ a t, (u a).Eu t = D.aschreibt a t)
    (hEuG : ∀ a g, (u a).EuG g = D.agschreibt a g)
    (hKeff : ∀ a σ ρ σ' roh, K a (k a).nummer (k a).abi σ ρ σ' roh →
      Rahmen (k a).Ek (k a).EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
      ((∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt) →
       (∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt) →
       ∃ tabs : List D.Tab, ∃ globs : List D.Glob, ∃ Λe : List (Res D),
         (∀ t, D.aschreibt a t = true → t ∈ tabs) ∧
         (∀ g, D.agschreibt a g = true → g ∈ globs) ∧
         (∀ t, D.aschreibt a t = true → darf D t Λe) ∧
         (∀ g, D.agschreibt a g = true → gdarf D g Λe) ∧
         (∀ m st, Res.marke m st ∉ Λe) ∧
         HeldIn Λe σ.haelt ∧
         σ'.spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur))
    (hO : ∀ a σ ρ, ∃ σ' roh, K a (u a).nummer (u a).abi σ ρ σ' roh ∧
      O.wirkt a σ ρ = (σ', roh)) :
    GutO O := by
  intro a σ ρ
  have hW : ∀ t, (k a).Ek t = true → D.aschreibt a t = true := by
    intro t ht
    rw [← hEu a t]
    exact hsub a t ht
  have hG : ∀ g, (k a).EkG g = true → D.agschreibt a g = true := by
    intro g hg
    rw [← hEuG a g]
    exact hsubG a g hg
  obtain ⟨σ', roh, hKbeh, hOeq⟩ := hO a σ ρ
  rw [← hnum a, ← habi a] at hKbeh
  obtain ⟨hfr, hha, hcond⟩ := hKeff a σ ρ σ' roh hKbeh
  have hfst : (O.wirkt a σ ρ).1 = σ' := by rw [hOeq]
  refine ⟨hfst ▸ hfr.weiter hW hG, ?_, ?_⟩
  · rw [hfst]; exact hha
  · intro hgt hgg
    obtain ⟨tabs, globs, Λe, hct, hcg, hdt, hdg, hmf, hhi, hspur⟩ :=
      hcond hgt hgg
    refine ⟨tabs, globs, Λe, hct, hcg, hdt, hdg, hmf, hhi, ?_⟩
    rw [hfst]; exact hspur

/-- ZEUGE: all eight `paarung_gibt_gutO` premises hold jointly on the toy
    `write` declaration `swD`, whose only axiom is that syscall (number 1,
    `schreibAbi`, `schreibFehler`); the program is non-degenerate: function
    `()` writes table `()`, and a `storeSlot` step moves memory
    (`0 -> 1` at slot `0`). -/
theorem paarung_gibt_gutO_zeuge :
    GutO swO ∧ swD.schreibt () () = true ∧
    ∃ (σ σ' : World swD), σ'.slots () 0 () ≠ σ.slots () 0 () := by
  refine ⟨paarung_gibt_gutO swD swO (fun _ => swK) (fun _ => swU)
    (fun _ => swKbeh) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl, ?_⟩
  · intro a
    cases a
    exact swNum
  · intro a
    cases a
    exact swAbi
  · intro a
    cases a
    exact swSub
  · intro a
    cases a
    exact swSubG
  · intro a
    cases a
    exact swEu
  · intro a
    cases a
    exact swEuG
  · intro a
    cases a
    exact swEff
  · intro a
    cases a
    exact swO_trifft
  · refine ⟨swWelt0, swWelt0.storeSlot () 0 ()
      (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)), ?_⟩
    have hn1 : ((swWelt0.storeSlot () 0 ()
        (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192))).slots () 0 ()).n
        = 1 := rfl
    have hn0 : (swWelt0.slots () 0 ()).n = 0 := rfl
    intro hcon
    have hn := congrArg Zahl.n hcon
    rw [hn1, hn0] at hn
    omega

/- CUTS: what is not proved.
   - The kernel implementation `K` is a hypothesis (`hKeff`/`hKcon`),
     not a verification: discharging it for a real Gabbro kernel means
     proving the dispatch entry's contract over its runs, including the
     recorded `axiomSpur` events.
   - `syscall_paarung` covers the contract/frame/recording pairing only. The
     emitter side (stub template, register binding, clobbers) and the
     ghost-carrier erasure live in lanes S6/S3, not here.
   - `syscall_paarung_abgelehnt` exhibits one counterexample shape (an
     undeclared table write); it does not classify all mismatches
     (wrong number, wrong map, weak `Qk`).
   - `paarung_gibt_gutO` discharges the oracle bound only for the
     frame/recording legs; the decoded-contract leg of `PaarGut` is not
     needed for `GutO` and is not a premise. The single `Grund` type for
     all axioms covers the one-axiom witness; a multi-syscall declaration
     with per-axiom reason types would generalise `u` to a per-axiom
     family of types.
-/

#print axioms Gabbro.Grammatik.syscall_paarung
#print axioms Gabbro.Grammatik.syscall_paarung_zeuge
#print axioms Gabbro.Grammatik.syscall_paarung_abgelehnt
#print axioms Gabbro.Grammatik.PaarGut
#print axioms Gabbro.Grammatik.swEns
#print axioms Gabbro.Grammatik.swO_trifft
#print axioms Gabbro.Grammatik.paarung_gibt_gutO
#print axioms Gabbro.Grammatik.paarung_gibt_gutO_zeuge

end Gabbro.Grammatik
