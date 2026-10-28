import Grammatik.Bausteine.Arena.Ownership.Body.Program
import Grammatik.Bausteine.Arena.Struktur.ArenaDynZeuge

/-! Witness for the general body judgment over the four-slot arena fixture.
`make` (`true`) allocates from the counter and returns the owning index, or
its reason on a full arena; `user` (`false`) calls `make` with an `else`,
releases the returned allocation and returns. Both bodies derive in the
judgment, so `checked_calls` applies to the actual `rufAt`; the actual run
of `user` executes the allocation, the owning handoff and the release. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body.Witness

open InvDynZeuge Source

def makeSig : Signatur FD.Tab FD.Glob FD.Lock FD.Marke :=
  { params := []
    erg := some (Ty.index 4)
    gruende := 1
    haelt := []
    schreibt := fun _ => true
    gschreibt := fun _ => true
    konsumiert := []
    produziert := [] }

def userSig : Signatur FD.Tab FD.Glob FD.Lock FD.Marke :=
  { makeSig with erg := none }

def sigOf : Bool → Nat
  | true => 0
  | false => 1

def sigTable : Nat → Signatur FD.Tab FD.Glob FD.Lock FD.Marke
  | 0 => makeSig
  | _ => userSig

@[reducible] def D : Deklaration :=
  { FD with
    Fn := Bool
    sig := sigOf
    passt := fun f n => decide (sigOf f = n)
    rzusage := fun e => nomatch e
    sigNr := sigTable
    passt_ok := by
      intro f n h
      have hn : sigOf f = n := of_decide_eq_true h
      subst hn
      exact SigPasst.refl _ _
    eigner_nie_erzeugt := fun _ _ _ _ h => by cases h
    invarianten_gehalten := fun _ i => nomatch i }

def A : FreiForm D where
  tab := ()
  feld := 0
  zaehl := 0
  hz := rfl
  hpos := by decide
  komm := 1
  hk := rfl
  hzwei := by decide
  kopf := 2
  hkopf := rfl
  nxt := 1
  hnxt := rfl
  hk1 := by decide
  hk2 := by decide
  hf := by decide

theorem tab_right : darf D A.tab [] := fun _ h => by cases h
theorem glob_right (g : D.Glob) : gdarf D g [] := fun _ h => by cases h

def seven {Γ : Ctx} : Expr D Γ [] (D.typ A.tab A.feld) := .widen (by decide) (by decide) (.lit 7)

def reason (f : D.Fn) : Fin (D.gruende f) := ⟨0, by cases f <;> decide⟩

theorem hpUser : RufPasst D (vertragVon D false) (D.signatur true) [] where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], List.Sublist.refl []⟩
  hh := fun _ h => by cases h

/-! ## The bodies -/

def makeReturn : Block D (vertragVon D true) false [Ty.index 4] [] [] :=
  .cons (.ret (valueResult (τ := Ty.index 4) rfl (.var .here)) (List.Perm.refl [])) .nil

def makeAlloc : Block D (vertragVon D true) false [] [] [] :=
  Block.arenaAlloc A.toArenaForm seven rfl tab_right rfl (glob_right _)
    (.retWhy (reason true) (List.Perm.refl [])) makeReturn

def makeBody : Endblock D (vertragVon D true) false [] [] :=
  .cons (.ite .tru makeAlloc makeAlloc) (.retWhy (reason true) (List.Perm.refl []))

def release : Block D (vertragVon D false) false [Ty.index 4] [] [] :=
  Block.freiVar A .here rfl tab_right rfl (glob_right _) .nil

def userBody : Endblock D (vertragVon D false) false [] [] :=
  .bindCallElse true .nil rfl hpUser (by decide)
    (.retWhy (reason false) (List.Perm.refl []))
    (.cons (.ite .tru release release) (.ret .empty (List.Perm.refl [])))

def P : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun | true => makeBody | false => userBody

/-- `make` returns an owning index, `user` returns nothing; neither takes a parameter. -/
def I : Interfaces A
  | true => ⟨.nil, rfl, .owner⟩
  | false => ⟨.nil, rfl, .plain⟩

/-! ## The derivations -/

def entry : Context := Flow.parameterContext (Modes.nil : Modes [])

theorem make_derives : OE A I (V := vertragVon D true) (I true).output noLoop entry makeBody := by
  have hblk : OB A I (I true).output noLoop entry makeAlloc ((entry.bind none).drop) := by
    unfold makeAlloc Block.arenaAlloc Block.arenaRumpf
    refine OB.allocCounter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?he ?hhi ?hn ?hg ?he2 ?hi ?hev ?hs ?hvoll ?hrest
    case he => rfl
    case hhi => decide
    case hn => decide
    case hg => rfl
    case he2 => rfl
    case hi => rfl
    case hev => rfl
    case hs => rfl
    case hvoll => exact OE.retWhy _ _ (by rfl)
    case hrest => exact OB.cons _ _ (OS.ret (c' := entry.bind none) _ _ (by rfl)) OB.nil
  exact OE.cons _ _ (OS.ite _ _ _ (by rfl) hblk hblk) (OE.retWhy _ _ (by rfl))

theorem user_derives : OE A I (V := vertragVon D false) (I false).output noLoop entry userBody := by
  have hrel : OB A I (I false).output noLoop ((entry.afterCall [] []).bindFresh) release
      (((entry.afterCall [] []).bindFresh).kill 0) := by
    unfold release Block.freiVar
    refine OB.release (o := 0) (p := 0) _ _ _ _ _ _ _ _ _ _ _ rfl ?hf ?hip ?he ?hg ?he2 ?hc OB.nil
    case hf => rfl
    case hip => rfl
    case he => rfl
    case hg => rfl
    case he2 => rfl
    case hc => rfl
  unfold userBody
  apply OE.bindCallElse
  · rfl
  · rfl
  · exact OE.retWhy _ _ (by rfl)
  · exact OE.cons _ _ (OS.ite _ _ _ (by rfl) hrel hrel) (OE.ret _ _ (by rfl))

/-- **Both bodies derive.** -/
theorem checked : Checked P A I := by
  intro f
  cases f
  · exact user_derives
  · exact make_derives

theorem good_oracle (O : Orakel D) : GutO O := fun a => nomatch a

/-- The checked program's interfaces hold at every actual call. -/
theorem calls (O : Orakel D) (passes : Nat) : ∀ n, Respects A I.contracts (rufAt P O passes n) :=
  checked_calls checked (good_oracle O) passes

/-! ## The actual run -/

def world : World D where
  slots := fun _ _ f => by
    change Wert D (if f = 0 then .int 0 255 else .int 0 4)
    split
    · exact ⟨7, by decide, by decide⟩
    · exact ⟨4, by decide, by decide⟩
  globs := fun g => if g = 0 then ⟨0, by decide, by decide⟩ else ⟨4, by decide, by decide⟩
  spur := []

theorem free_ok : A.FreiOk world :=
  ⟨[], FreiForm.Kette.nil, List.nodup_nil, fun _ h => by cases h⟩

theorem agrees : State.empty.agrees A world := by
  refine ⟨State.empty_valid, fun i => ?_⟩
  change A.Lebt world i ↔ ∃ c, none = some c
  constructor
  · intro h
    have h0 := h.1
    have hlt := h.2.1
    change i < 0 at hlt
    omega
  · rintro ⟨c, h⟩; cases h

/-- `user` runs: `make` allocates slot `0`, hands it over, and `user` releases it. -/
theorem actual_run (O : Orakel D) (passes : Nat) :
    ∃ σ', rufAt P O passes 2 false world .nil = .ok σ' () ∧ A.stand σ' = 1 ∧ A.kopfSt σ' = 0 := by
  exact ⟨_, rfl, rfl, rfl⟩

/-- **The interface of `user` at the actual run:** the activation ends owning
nothing, so the allocation `make` returned is not leaked. -/
theorem actual_run_closed (O : Orakel D) (passes : Nat) (frame : Frame) :
    ∃ (σ' : World D) (s' : State), rufAt P O passes 2 false world .nil = .ok σ' () ∧ s'.agrees A σ' ∧ s'.closed frame := by
  obtain ⟨σ', hrun, _, _⟩ := actual_run O passes
  have hpre : (I.contracts false).requires frame State.empty .nil := by
    refine ⟨fun _ => none, ⟨rfl, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro τ x; cases x
    · intro i m h; simp only [I, Flow.parameterContext, Context.empty, List.length_nil, List.replicate_zero, reduceCtorEq] at h
    · intro i j p q h; simp only [I, Flow.parameterContext, Context.empty, List.length_nil, List.replicate_zero, reduceCtorEq] at h
    · intro _ _ h; cases h
  obtain ⟨s', ha', _, _, _, hclosed⟩ :=
    (calls O passes 2 false frame State.empty world .nil agrees free_ok hpre).1 σ' () hrun
  exact ⟨σ', s', hrun, ha', hclosed⟩

#print axioms checked
#print axioms actual_run_closed

end Gabbro.Grammatik.ArenaOwnership.Body.Witness
