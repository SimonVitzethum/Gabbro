/-
  File:      Grammatik/AxiomVertrag.lean
  Subject:   AXIOM-CALLING BODIES WITH A RESULT-DEPENDENT CONTRACT -- the
             finding about `KoerperGutV`, and the strengthening that closes
             it: per-axiom declared ensures.

  `KoerperGutV P passes f` asks for the body triple of `f` against EVERY
  oracle that respects the declared axiom frames (`RahmenO`). A frame says
  WHICH carriers an axiom may write, not WHAT it writes nor what it answers.
  Here, on the smallest body that calls an axiom and returns its answer --

      axiom inc() -> 0 .. 3  writes tab            (frame: `tab`)
      fn zaehle() -> 0 .. 3  requires Held(L)  writes tab
        { if true { let r = inc(); return r }; return 0 }

  -- the finding (`koerperGutV_nur_rahmen`): whatever `ensures E` the user
  writes, `KoerperGutV` holds only if `E` holds for EVERY result `v` and
  EVERY written value `w` of the slot (the post world `σ[tab[0] := w]`). So
  `E` cannot relate the result to the written slot: `result == tab[0]`
  ("inc returns the new value") fails (`inc_ensures_nicht_V`), for the
  frame-respecting oracle that writes `1` and answers `2`.

  The strengthening (`KoerperGutA`): an axiom DECLARES an ensures `Q` over
  its result and its post world (as a syscall declares `Qu`), the machine's
  oracle meets it (`AxVertragO Q O`, a hardware premise like `GutO`), and the
  user obligation quantifies over the frame-respecting oracles that meet
  the declared ensures. With `Q inc σ' v := (v == σ'.tab[0])`, the contract
  `result == tab[0]` is provable (`inc_koerperGutA`). The goal theorem over
  the strengthened obligation is `ziel_ort_voll_ax` (`ZielOrtAx.lean`); it
  needs `Q` to read only the axiom's declared carriers of the post world
  (`AxEnsLokal`), the class the replay can transfer.
-/
import Grammatik.ZielOrtVollBeweis
import Grammatik.ZielOrtVollZeuge

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Declared axiom ensures, and the strengthened obligation -/

/-- A per-axiom declared ensures: a decision over the axiom's answer world
    and its (range-checked) result. -/
abbrev AxEns (D : Deklaration) := ∀ a : D.Ax, World D → ErgVal D (D.aerg a) → Bool

/-- The oracle meets the declared ensures: whenever an axiom's raw answer
    fits its declared result type, the declared ensures holds of the
    answer world and the result (the hardware premise of the declaration,
    as `GutO` is the one of the frame). -/
def AxVertragO (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    einpassenErg (D.aerg a) (O.wirkt a σ ρ).2 = some v → Q a (O.wirkt a σ ρ).1 v = true

/-- The declared ensures reads only the axiom's declared write carriers of
    the answer world (and the result). -/
def AxEnsLokal (Q : AxEns D) : Prop :=
  ∀ (a : D.Ax) (σ σ' : World D) (v : ErgVal D (D.aerg a)),
    (∀ t, D.aschreibt a t = true → σ.slots t = σ'.slots t) →
    (∀ g, D.agschreibt a g = true → σ.globs g = σ'.globs g) → Q a σ v = Q a σ' v

/-- **The strengthened user obligation.** The body triple and the caller
    duty of `KoerperGut`, for every oracle that respects the declared axiom
    frames AND meets the declared axiom ensures. -/
def KoerperGutA (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → AxVertragO Q O' → KoerperGut P O' passes f

/-- The strengthened obligation is weaker than `KoerperGutV`: fewer oracles. -/
theorem koerperGutA_of_V {P : Programm D} {passes : Nat} (Q : AxEns D) {f : D.Fn}
    (h : KoerperGutV P passes f) : KoerperGutA P passes Q f :=
  fun O' hr _ => h O' hr

/-- Every recorded axiom answer meets the declared ensures. -/
def VertragA (Q : AxEns D) (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA →
      ∀ v : ErgVal D (D.aerg a), einpassenErg (D.aerg a) x.2 = some v → Q a x.1 v = true

theorem vertragA_nil (Q : AxEns D) : VertragA Q ([] : List (AxEintrag D)) :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

/-- The oracle of a record meets the declared ensures when the machine's
    oracle does and every recorded answer does. -/
theorem orakelAus_vertrag {Q : AxEns D} {O : Orakel D} (hQ : AxVertragO Q O)
    {HA : List (AxEintrag D)} (hv : VertragA Q HA) : AxVertragO Q (orakelAus O HA) := by
  intro a σ ρ v
  simp only [orakelAus]
  split
  · rename_i hex
    exact hv a σ ρ _ (Classical.choose_spec hex) v
  · exact hQ a σ ρ v

/-- The recorded answer world agrees with the machine's answer world on the
    axiom's declared carriers, so a local declared ensures transfers. -/
theorem axWelt_vertrag {Q : AxEns D} (hlok : AxEnsLokal Q) (e0 : Ereignis D) (a : D.Ax)
    (κ σ₂ : World D) (v : ErgVal D (D.aerg a)) (h : Q a σ₂ v = true) :
    Q a (axWelt e0 a κ σ₂) v = true := by
  rw [hlok a (axWelt e0 a κ σ₂) σ₂ v (fun t ht => by
      show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
      rw [if_pos ht])
    (fun g hg => by
      show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
      rw [if_pos hg])]
  exact h

/-! ## 2. The example: `inc` and `zaehle` -/

inductive AxFn where
  | haupt
  | zaehle
  | ruhe
  deriving DecidableEq

def axSigHaupt : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def axSigZaehle : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 3)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def axSigRuhe : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One table `tab` (one slot, `0 .. 3`) guarded by the lock `L`; one axiom
    `inc() -> 0 .. 3` whose frame is `tab`; three functions. -/
def axD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 3
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := AxFn
  sig := fun | .haupt => 0 | .zaehle => 1 | .ruhe => 2
  sigNr := fun n => match n with | 0 => axSigHaupt | 1 => axSigZaehle | _ => axSigRuhe
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some (.int 0 3)
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def axHaupt : axD.Fn := AxFn.haupt
def axZaehle : axD.Fn := AxFn.zaehle
def axRuhe : axD.Fn := AxFn.ruhe
def axInc : axD.Ax := ()

abbrev axL : List (Res axD) := [Res.held (D := axD) ()]

theorem axDarf : darf axD () axL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

def axIdx {Γ : Ctx} {Λ : List (Res axD)} : Expr axD Γ Λ (.index (axD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

def axNullE {Γ : Ctx} {Λ : List (Res axD)} : Expr axD Γ Λ (.int 0 3) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- `let r = inc(); return r` -/
def axIncBlock : Block axD (vertragVon axD axZaehle) false [] axL axL :=
  .bindAxiom axInc .nil rfl (fun _ _ => rfl) (fun e => nomatch e) (fun _ _ => axDarf)
    (fun e => nomatch e) (.cons (.ret (.wert (.var .hier)) (List.Perm.refl _)) .nil)

def axIte : Stmt axD (vertragVon axD axZaehle) false [] axL axL := .ite .wahr axIncBlock .nil

def axRetNull : Endblock axD (vertragVon axD axZaehle) false [] axL :=
  .ret (.wert axNullE) (List.Perm.refl _)

/-- `zaehle`: `if true { let r = inc(); return r }; return 0`. -/
def axRumpfZaehle : Endblock axD (vertragVon axD axZaehle) false [] axL := .cons axIte axRetNull

/-- `haupt` calls `zaehle`: same lock, same writes. -/
theorem axHpZaehle : RufPasst axD (vertragVon axD axHaupt) (axD.signatur axZaehle) axL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩

def axRufZaehle : Stmt axD (vertragVon axD axHaupt) false [] axL (nach axD axZaehle axL) :=
  .call axZaehle .nil axHpZaehle rfl

def axRetH : Endblock axD (vertragVon axD axHaupt) false [] axL := .ret .keine (List.Perm.refl _)

/-- `haupt`: `zaehle(); return`. -/
def axRumpfHaupt : Endblock axD (vertragVon axD axHaupt) false [] axL := .cons axRufZaehle axRetH

def axRumpfRuhe : Endblock axD (vertragVon axD axRuhe) false [] [] := .ret .keine List.Perm.nil

/-- An `ensures` for `zaehle`: over its result (bound first) and the slot. -/
abbrev AxEnsZ := Expr axD (ErgCtx (axD.params axZaehle) (axD.erg axZaehle))
  (vertragVon axD axZaehle).ende .bool

/-- `result == tab[0]`: `inc` returns the new value of the slot it writes. -/
def axEnsInc : AxEnsZ := .eq (.var .hier) (.slot () () axIdx axDarf)

/-- The program with `zaehle`'s `ensures` given by `E`. -/
def axPE (E : AxEnsZ) : Programm axD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .haupt => .wahr
    | .zaehle => E
    | .ruhe => .wahr
  rumpf
    | .haupt => axRumpfHaupt
    | .zaehle => axRumpfZaehle
    | .ruhe => axRumpfRuhe

/-- The program with `ensures result == tab[0]`. -/
def axP : Programm axD := axPE axEnsInc

/-! ## 3. The finding: `KoerperGutV` validates only frame-valid contracts -/

/-- The oracle that writes `w` into the slot and answers `v` -- inside the
    frame of `inc` for every `v`, `w`. -/
def axOrakel (v w : Wert axD (.int 0 3)) : Orakel axD where
  wirkt := fun _ σ _ => (σ.storeSlot () 0 () w, v.n)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem axOrakel_rahmen (v w : Wert axD (.int 0 3)) : RahmenO (axOrakel v w) := by
  intro a σ ρ
  refine ⟨fun t ht => ?_, fun g => nomatch g⟩
  cases ht

/-- A handler that is never asked (the bodies of `axPE` call nothing that
    returns): it respects every contract vacuously and blames nobody. -/
theorem keinRuf_respektiert (P : Programm axD) : RespektiertVertraege P keinRuf := by
  intro f σ ρ _ σ' v h
  cases h

theorem keinRuf_ohne : OhneVorbedingung (D := axD) keinRuf := by
  intro g σ ρ e h g' he
  cases h
  cases he

/-- The outcome of `zaehle`'s body after the axiom answered `x` in `σ₂`. -/
def axZaehleAus (σ₂ : World axD) :
    Option (ErgVal axD (axD.aerg axInc)) → EndAusgang (vertragVon axD axZaehle) false []
  | some v => .zurueck (σ₂.lese axL []) v
  | none => .hardware (.annahme axInc)

/-- `zaehle`'s body under any oracle: it returns the axiom's answer (at a
    world whose memory is the oracle's answer world's), or the axiom's
    answer did not fit its type. -/
theorem axZaehle_lauf (E : AxEnsZ) (O' : Orakel axD) (passes : Nat)
    (R : ∀ f : axD.Fn, World axD → Env axD (axD.params f) → RufAusgang f) (σ : World axD)
    (σ₂ : World axD) (x : Option (ErgVal axD (axD.aerg axInc)))
    (hax : axiomAntwort O' axInc ((σ.lese axL []).lese axL []) .nil = (σ₂, x)) :
    execEnd O' passes R ((axPE E).rumpf axZaehle) σ .nil = axZaehleAus σ₂ x := by
  show execEnd O' passes R axRumpfZaehle σ .nil = _
  cases x with
  | none =>
      simp only [axRumpfZaehle, axIte, axIncBlock, execEnd, execStmt, execBlock, eval, wahr?,
        if_true, Expr.orte, Args.orte, evalArgs, hax]
      try rfl
  | some v =>
      simp only [axRumpfZaehle, axIte, axIncBlock, execEnd, execStmt, execBlock, eval, wahr?,
        if_true, Expr.orte, Args.orte, evalArgs, hax]
      rfl

/-- **The finding (`koerperGutV_nur_rahmen`).** If `zaehle` with `ensures E`
    meets `KoerperGutV`, then `E` holds at EVERY result `v` and EVERY post
    value `w` of the slot the axiom writes: `KoerperGutV` validates only
    contracts that are true over the whole frame, so no contract can relate
    the result to the written slot. Proof: the frame-respecting oracle that
    writes `w` and answers `v`. -/
theorem koerperGutV_nur_rahmen (E : AxEnsZ) (h : KoerperGutV (axPE E) 0 axZaehle)
    (σ : World axD) (v w : Wert axD (.int 0 3)) :
    wahr? (eval σ E (σ.storeSlot () 0 () w) (.cons v .nil)) = true := by
  have hK := (h (axOrakel v w) (axOrakel_rahmen v w) keinRuf (keinRuf_respektiert _)
    keinRuf_ohne σ .nil rfl).1
  have hein : einpassenErg (D := axD) (axD.aerg axInc) v.n = some v := by
    show einpassen (.int 0 3) v.n = some v
    simp only [einpassen, dif_pos (show 0 ≤ v.n ∧ v.n ≤ 3 from ⟨v.lo_le, v.le_hi⟩)]
    rfl
  have hax : axiomAntwort (axOrakel v w) axInc ((σ.lese axL []).lese axL []) .nil =
      (((σ.lese axL []).lese axL []).storeSlot () 0 () w, some v) := by
    show (_, einpassenErg (D := axD) (axD.aerg axInc) v.n) = _
    rw [hein]
    rfl
  have hrun := axZaehle_lauf E (axOrakel v w) 0 keinRuf σ _ _ hax
  have hens := hK _ _ hrun
  exact ens_transfer (P := axPE E) (f := axZaehle) hens (GleichAuf.refl _ _)
    ⟨fun t _ => rfl, fun g => nomatch g⟩

/-- **The refutation.** `result == tab[0]` is not a `KoerperGutV` contract:
    the frame-respecting oracle that writes `1` and answers `2` breaks it. -/
theorem inc_ensures_nicht_V : ¬ KoerperGutV axP 0 axZaehle := by
  intro h
  have := koerperGutV_nur_rahmen axEnsInc h
    ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => (nomatch g), []⟩
    ⟨2, by decide, by decide⟩ ⟨1, by decide, by decide⟩
  exact absurd this (by decide)

/-! ## 4. The strengthening: the declared ensures of `inc` -/

/-- `inc`'s declared ensures: it returns the new value of its slot. -/
def axQ : AxEns axD := fun _ σ' v => decide ((v : Zahl 0 3).n = (σ'.slots () 0 ()).n)

theorem axQ_lokal : AxEnsLokal axQ := by
  intro a σ σ' v ht _
  show decide ((v : Zahl 0 3).n = (σ.slots () 0 ()).n) = decide (v.n = (σ'.slots () 0 ()).n)
  rw [ht () rfl]

/-- **The contract is satisfiable under the strengthened obligation**:
    `zaehle` with `ensures result == tab[0]` meets `KoerperGutA` for `inc`'s
    declared ensures -- the contract talks about the result and the written
    slot, and holds for every frame-respecting oracle that meets the
    declaration. -/
theorem inc_koerperGutA : KoerperGutA axP 0 axQ axZaehle := by
  intro O' _ hQ R _ _ σ ρ _
  have hρ : ρ = .nil := by cases ρ; rfl
  subst hρ
  have hax : axiomAntwort O' axInc ((σ.lese axL []).lese axL []) .nil =
      ((O'.wirkt axInc ((σ.lese axL []).lese axL []) .nil).1,
        einpassenErg (axD.aerg axInc) (O'.wirkt axInc ((σ.lese axL []).lese axL []) .nil).2) :=
    rfl
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have e := hrun.symm.trans (axZaehle_lauf axEnsInc O' 0 R σ _ _ hax)
    revert e
    cases hw : einpassenErg (axD.aerg axInc)
        (O'.wirkt axInc ((σ.lese axL []).lese axL []) .nil).2 with
    | none => intro e; cases e
    | some u =>
        intro e
        cases e
        exact hQ axInc _ .nil _ hw
  · have e := hrun.symm.trans (axZaehle_lauf axEnsInc O' 0 (torRuf axP R) σ _ _ hax)
    revert e
    cases einpassenErg (axD.aerg axInc) (O'.wirkt axInc ((σ.lese axL []).lese axL []) .nil).2 with
    | none => intro e; cases e
    | some u => intro e; cases e

/-- The strengthened obligation holds for `haupt` and `ruhe` too (they make
    no axiom call; `haupt`'s call meets `zaehle`'s `requires true`). -/
theorem axP_koerperA : ∀ f, KoerperGutA axP 0 axQ f := by
  intro f
  cases f
  · intro O' _ _ R _ hOV σ ρ _
    refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
    have hr : axP.rumpf AxFn.haupt = axRumpfHaupt := rfl
    have ht : ∀ σ1 ρ1, torRuf axP R axZaehle σ1 ρ1 = R axZaehle σ1 ρ1 := fun _ _ => if_pos rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp only [axRufZaehle, execStmt, ht] at h1
      split at h1
      · cases h1
      · rename_i r _
        exact (Fin.cast rfl r).elim0
      · rename_i e hR
        cases h1
        exact hOV _ _ _ _ hR g rfl
      · cases h1
    · simp only [axRetH, execEnd] at h1
      cases h1
  · exact inc_koerperGutA
  · intro O' _ _ R _ _ σ ρ _
    refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
    have hr : axP.rumpf AxFn.ruhe = axRumpfRuhe := rfl
    rw [hr] at hrun
    simp only [axRumpfRuhe, execEnd] at hrun
    cases hrun

/-! ## CUTS:

  What is proved: the finding -- on the axiom-calling body `zaehle`, every
  `ensures E` that `KoerperGutV` accepts holds at every result and every
  post value of the written slot (`koerperGutV_nur_rahmen`), so the
  result-dependent contract `result == tab[0]` is refuted
  (`inc_ensures_nicht_V`); the strengthening -- declared axiom ensures
  (`AxEns`, `AxVertragO`, `AxEnsLokal`), the obligation `KoerperGutA`
  (weaker than `KoerperGutV`, `koerperGutA_of_V`), the record facts the
  replay needs (`VertragA`, `orakelAus_vertrag`, `axWelt_vertrag`); the
  contract under the strengthened obligation (`inc_koerperGutA`,
  `axP_koerperA`).

  What the finding does NOT say: `KoerperGutV` is not vacuous for axiom
  bodies -- contracts that hold over the whole frame (typing bounds, the
  unchanged carriers outside the frame) are accepted. It says precisely
  that a contract cannot depend on what the axiom answers or writes inside
  its frame, which is why the declared ensures is needed.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.koerperGutV_nur_rahmen
#print axioms Gabbro.Grammatik.inc_ensures_nicht_V
#print axioms Gabbro.Grammatik.inc_koerperGutA
#print axioms Gabbro.Grammatik.axP_koerperA
