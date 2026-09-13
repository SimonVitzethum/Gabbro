/-
  File:      Grammatik/FremdSperre.lean
  Subject:   MODEL REPAIR -- A FOREIGN WRITE MUST HOLD THE GUARD (lane 74).

  `Stmt.axiomCall` carries guard proofs `hd`/`hgd` for every table/global
  the axiom declares written. This file proves the payoff: an axiom call
  step that changes a slot of `t` holds every lock guarding `t`
  (`axiomCall_haelt_waechter`), and a call writing a guarded carrier is
  not derivable with an empty trace (`axiomCall_ohne_sperre_nicht_ableitbar`).
-/
import Grammatik.Satz

namespace Gabbro.Grammatik

/-- One guarded table holding one boolean; one lock; one writing axiom. -/
def DF : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => true
  ggeteilt := fun g => nomatch g
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => [Sum.inl ()]
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun g => nomatch g
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => nomatch g
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by
    show [Sum.inl ()] ≠ []
    simp
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The calling contract: writes the table, holds nothing. -/
def VF : Vertrag DF :=
  Vertrag.mk (fun _ => true) (fun g => nomatch g) none 0 [] [] none

/-- The static trace: the one guard in hand. -/
def ΛF : List (Res DF) := [Res.held ()]

/-- A world with the slot `false` and the guard taken. -/
def σF : World DF :=
  { slots := fun _ _ _ => false
    globs := fun g => nomatch g
    spur := [@Ereignis.nimmt DF () []] }

/-- The oracle: flips every slot to `true`, keeps globals and locks, and
    records the axiom's write event (as the recording `GutO` demands). -/
def OF : Orakel DF :=
  { wirkt := fun _ σ _ =>
      ({ slots := fun _ _ _ => true
         globs := fun g => nomatch g
         spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0)
    regLies := fun r _ => nomatch r
    regSchreib := fun r _ => nomatch r
    sichtbar := fun g _ => nomatch g }

/-- The axiom writes only the guarded table, whose guard is in hand. -/
theorem hdF : ∀ t, DF.aschreibt () t = true → darf DF t ΛF := by
  intro t _ w hw
  cases t
  cases w with
  | inl L =>
      cases L
      show Res.held PUnit.unit ∈ ΛF
      decide
  | inr m =>
      exact nomatch m.1

/-- No globals exist, so the global guard holds vacuously. -/
theorem hgdF : ∀ g, DF.agschreibt () g = true → gdarf DF g ΛF :=
  fun g => nomatch g

/-- The table write is within the contract. -/
theorem hwF : ∀ t, DF.aschreibt () t = true → VF.schreibt t = true :=
  fun _ _ => rfl

/-- No globals exist, so the global frame holds vacuously. -/
theorem hgF : ∀ g, DF.agschreibt () g = true → VF.gschreibt g = true :=
  fun g => nomatch g

/-- The oracle satisfies the conditional bound: frame (only the declared
    table moves) and held locks in every world; in worlds where the guard is
    held, the write event over the complete domains with the guard trace.
    In worlds where the guard is not held the trace clause discharges
    vacuously -- and no typed `axiomCall` fires there (`hd` needs the guard).
    Every premise is used: `hgt` gives the held lock for `HeldIn`. -/
theorem hOF : GutO OF := by
  intro a σ ρ
  cases a with
  | unit =>
      have hW : OF.wirkt () σ ρ =
          ({ slots := fun _ _ _ => true
             globs := fun g => nomatch g
             spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0) := rfl
      refine ⟨?_, by rw [hW]; rfl, ?_⟩
      · constructor
        · intro t ht
          cases t
          contradiction
        · intro g
          exact nomatch g
      · intro hgt hgg
        refine ⟨[()], [], [Res.held ()], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro t _
          cases t
          exact List.Mem.head _
        · intro g
          exact nomatch g
        · intro t hwr
          exact hdF t hwr
        · intro g
          exact nomatch g
        · intro m st hm
          simp at hm
        · intro L hL
          have eL : L = () := by
            have heq : Res.held (D := DF) L = Res.held (D := DF) () :=
              List.mem_singleton.mp hL
            cases heq
            rfl
          rw [eL]
          exact hgt () rfl () (List.Mem.head _)
        · rw [hW]

/-- The static trace names exactly the held lock. -/
theorem hhF : HeldGenau ΛF σF.haelt := by
  intro L
  cases L
  simp only [ΛF, σF, World.haelt, offen]
  exact iff_of_true (List.Mem.head _) (List.Mem.head _)

/-- **A foreign write holds the guard.** In any `axiomCall` step whose oracle
    world differs from the entry world on a slot of `t`, every lock guarding
    `t` is held (open in the thread trace): the difference forces
    `D.aschreibt a t = true` through the oracle frame (`hO`), the new guard
    premise `hd` turns that into `darf`, and `HeldGenau` (`hh`) makes it
    dynamic. The two further conjuncts use the remaining new premises: every
    global the axiom may write has its guards held (`hgd`), and the step
    stays inside the contract frame (`hw`, `hg`). -/
theorem axiomCall_haelt_waechter
    {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hO : GutO O)
    (σ : World D) (ρ : Env D Γ)
    (hh : HeldGenau Λ σ.haelt)
    (σ' : World D)
    (hexec : (execStmt O passes R
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab)
    (hdiff : ∃ k : Int, ∃ f : D.Feld t, σ'.slots t k f ≠ σ.slots t k f)
    (L : D.Lock)
    (hL : Sum.inl L ∈ D.braucht t) :
    L ∈ σ.haelt ∧
      (∀ g : D.Glob, ∀ L' : D.Lock, D.agschreibt a g = true →
        Sum.inl L' ∈ D.gbraucht g → L' ∈ σ.haelt) ∧
      Rahmen V.schreibt V.gschreibt σ σ' := by
  simp only [execStmt] at hexec
  split at hexec
  · rename_i σ1 v ha
    simp only [Ausgang.welt, Option.some.injEq] at hexec
    subst hexec
    have hfst : (O.wirkt a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args
          (σ.lese Λ args.orte) ρ)).1 = σ1 := by
      have h1 := congrArg Prod.fst ha
      simp only [axiomAntwort] at h1
      exact h1
    clear ha v
    obtain ⟨k, f, hne⟩ := hdiff
    have hlese_slots : (σ.lese Λ args.orte).slots = σ.slots := rfl
    have hframe := (hO a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1
    have haschreibt : D.aschreibt a t = true := by
      cases heq : D.aschreibt a t with
      | true => rfl
      | false =>
          have heq' : σ1.slots t k f = σ.slots t k f := by
            rw [← hfst, hframe.1 t heq k f, hlese_slots]
          exact absurd heq' hne
    have hguard : L ∈ σ.haelt := by
      have hmem : Res.held L ∈ Λ := by
        have hdarf := hd t haschreibt
        have hmem' := hdarf _ hL
        simpa [Res.von] using hmem'
      exact (hh L).mp hmem
    have hguardG : ∀ g : D.Glob, ∀ L' : D.Lock, D.agschreibt a g = true →
        Sum.inl L' ∈ D.gbraucht g → L' ∈ σ.haelt := by
      intro g L' hag hmemG
      have hmem' : Res.held L' ∈ Λ := by
        have hgdarf := hgd g hag
        have hmem'' := hgdarf _ hmemG
        simpa [Res.von] using hmem''
      exact (hh L').mp hmem'
    have hrahmen : Rahmen V.schreibt V.gschreibt σ σ1 := by
      have hlese_frame : Rahmen V.schreibt V.gschreibt σ (σ.lese Λ args.orte) :=
        rahmen_gleich rfl rfl
      have horacle_frame : Rahmen V.schreibt V.gschreibt (σ.lese Λ args.orte) σ1 :=
        Rahmen.weiter hw hg (hfst ▸ hframe)
      exact hlese_frame.trans horacle_frame
    exact ⟨hguard, hguardG, hrahmen⟩
  · rename_i hx
    have h2 := congrArg Prod.snd hx
    simp only [axiomAntwort] at h2
    rw [h] at h2
    simp only [einpassenErg] at h2
    simp at h2

/-- **No guard, no derivation.** The table of `DF` is guarded, so `darf`
    at the empty trace is uninhabitable: a foreign call writing it is not
    derivable with `Λ = []`. This is the lane-54 counterexample as a
    theorem -- the old `axiomCall` admitted exactly this shape. -/
theorem axiomCall_ohne_sperre_nicht_ableitbar : darf DF () [] → False := by
  intro hder
  have hmem' := hder _ (List.Mem.head _)
  simp [Res.von] at hmem'

/-- Empty call arguments for the parameter-free axiom. -/
def argsF : Args DF [] ΛF (DF.aparams ()) := .nil

/-- Empty environment for the parameter-free call. -/
def ρF : Env DF [] := .nil

/-- The read world at the call site (no argument reads). -/
def σrF : World DF := σF.lese ΛF argsF.orte

/-- The argument environment at the call site. -/
def ρrF : Env DF (DF.aparams ()) := evalArgs σrF argsF σrF ρF

/-- The oracle world after the flip. -/
def σF' : World DF := (OF.wirkt () σrF ρrF).1

/-- The call handler is never consulted by an axiom call. -/
def RF : ∀ f : DF.Fn, World DF → Env DF (DF.params f) → RufAusgang f :=
  fun f _ _ => .logik (.abstieg f)

/-- The axiom call reaches the flipped world. -/
theorem hexecF : (execStmt OF 0 RF
    (Stmt.axiomCall () argsF rfl hwF hgF hdF hgdF :
      Stmt DF VF false [] ΛF ΛF) σF ρF).welt = some σF' := rfl

/-- The reached world differs on the slot: the step changes memory. -/
theorem hdiffF :
    ∃ k : Int, ∃ f : DF.Feld (), σF'.slots () k f ≠ σF.slots () k f :=
  ⟨0, (), by show (true : Bool) ≠ false; decide⟩

/-- The guard membership for the witness table. -/
theorem hLmem : Sum.inl () ∈ DF.braucht () := List.Mem.head _

/-- Non-degeneracy: the declaration has a function writing the table. -/
theorem zeuge_schreibt : DF.schreibt () () = true := rfl

/- RESTORED (reviewer revision): `axiomCall_haelt_waechter_zeuge` holds again
    -- under the conditional `GutO`, the guarded-write oracle `OF` satisfies
    the bound (`hOF`), so the joint premises can be instantiated. -/
/-- **Inhabitation.** All premises of `axiomCall_haelt_waechter` hold jointly
    on the guarded one-table declaration: the guard proof, the oracle bound,
    the held-exactly fact, a reached run step (`hexecF`) that changes memory
    (`hdiffF`), and the guard membership -- plus the non-degeneracy facts (a
    function writes the table, the reached step flips its slot). -/
theorem axiomCall_haelt_waechter_zeuge :
    () ∈ σF.haelt ∧
      Rahmen VF.schreibt VF.gschreibt σF σF' ∧
      DF.schreibt () () = true ∧
      (∃ k : Int, ∃ f : DF.Feld (), σF'.slots () k f ≠ σF.slots () k f) := by
  have hmain := axiomCall_haelt_waechter () argsF rfl hwF hgF hdF hgdF
    OF 0 RF hOF σF ρF hhF σF' hexecF () hdiffF () hLmem
  exact ⟨hmain.1, hmain.2.2, zeuge_schreibt, hdiffF⟩

/-- **Guarded-oracle inhabitation (rule 13).** An oracle whose axiom writes a
    lock-guarded table satisfies the conditional `GutO`: `OF` with `hOF`,
    jointly with the guard proof (`hdF`), the held-exactly fact (`hhF`), a
    memory-changing oracle step (`hdiffF` at the answer world), and the
    non-degeneracy fact (a function writes the table). Every component is
    used: the package is the joint instantiation. -/
theorem gutO_bewacht_zeuge :
    ∃ (O : Orakel DF),
      GutO O ∧
      (∀ t, DF.aschreibt () t = true → darf DF t ΛF) ∧
      HeldGenau ΛF σF.haelt ∧
      (∃ k : Int, ∃ f : DF.Feld (),
        (O.wirkt () σrF ρrF).1.slots () k f ≠ σF.slots () k f) ∧
      DF.schreibt () () = true := by
  obtain ⟨k, f, hne⟩ := hdiffF
  refine ⟨OF, hOF, hdF, hhF, ?_, zeuge_schreibt⟩
  exact ⟨k, f, hne⟩

/-! ## CUTS

  (F1) `axiomCall_haelt_waechter` covers table guards dynamically (the oracle
    world differs on a slot) and global guards statically (everything the
    axiom may write). A dynamic global-guard leg (oracle differs on a global)
    is not stated.
  (F2) (reviewer revision) The oracle bound `GutO` RECORDS a write access
    event per declared table/global write (`axiomSpur`, `Satz.lean`) -- but
    only CONDITIONALLY on the axiom's lock guards being held in the calling
    world; elsewhere the trace is unconstrained. The unconditional version
    was a vacuity trap (no guarded-table writer satisfied it). `OF` emits
    its write event and satisfies the bound (`hOF`: frame and locks
    everywhere, events where the guard is held); `gutO_bewacht_zeuge`
    packages the joint inhabitation and `axiomCall_haelt_waechter_zeuge` is
    restored. Guarded-table writers exist (`hOF` below).
  (F3) (reviewer revision) `Block.bindAxiom` now carries the guard premises
    `hd`/`hgd` like `Stmt.axiomCall` (constructor change in `Syntax.lean`);
    the lane-74 repair is complete for both axiom forms.
-/

#print axioms Gabbro.Grammatik.axiomCall_haelt_waechter
#print axioms Gabbro.Grammatik.axiomCall_haelt_waechter_zeuge
#print axioms Gabbro.Grammatik.gutO_bewacht_zeuge
#print axioms Gabbro.Grammatik.axiomCall_ohne_sperre_nicht_ableitbar

end Gabbro.Grammatik
