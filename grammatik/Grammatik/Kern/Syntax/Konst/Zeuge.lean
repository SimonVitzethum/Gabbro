module

public import Grammatik.Kern.Syntax.Konst.Rang
public import Grammatik.Kern.Syntax.Konst.ReinBBeweis

public section
namespace Gabbro.Grammatik.ConstWitness

@[expose, reducible] def witnessD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun t => t.elim
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Fin 2
  sig := fun _ => 0
  sigNr := fun _ => ⟨[], some (.int 3 3), 0, [], fun t => t.elim, fun g => g.elim, [], [], none, {}⟩
  eigner_nie_erzeugt := fun _ t => t.elim
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

/-- Calls preserve the empty resource context. -/
theorem callFits (f g : witnessD.Fn) :
    RufPasst witnessD (vertragVon witnessD f) (witnessD.signatur g) [] where
  hw := fun t => t.elim
  hg := fun g => g.elim
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun l => l.elim
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _ (OwnerFlow.empty_of_empty _)

/-- Two functions: the first calls the selected callee, the second adds literals. -/
@[expose] def witnessP (callee : Fin 2) : Programm witnessD where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun f => if f.val = 0 then
    .cons (.call callee .nil (callFits f callee) rfl)
      (.ret (.val (.add (.lit 1) (.lit 2))) (List.Perm.refl _))
    else .ret (.val (.add (.lit 1) (.lit 2))) (List.Perm.refl _)

/-- Closed metadata shared by the acyclic and recursive fixtures. -/
@[expose, reducible] def fixture (callee : Fin 2) : ConstProgram where
  D := witnessD
  P := witnessP callee
  functions := [(0 : Fin 2), (1 : Fin 2)]
  functions_complete := by decide
  sourceId := fun f => f.val
  sourceId_injective := fun _ _ h => Fin.ext h
  noGlobals := fun g => g.elim
  noOracles := fun a => a.elim
  noRegisters := fun r => r.elim
  noLocks := fun l => l.elim
  noMarks := fun m => m.elim
  noInvariants := fun i => i.elim
  domains := []
  domains_complete := fun t => t.elim
  noFields := fun t => t.elim
  count_nonnegative := fun t => t.elim
  domains_closed := fun t => t.elim
  noReasons := fun _ => rfl
  emptyEntry := fun _ => rfl
  emptyExit := fun _ => rfl

/-- Fixture A has the edge f → g. -/
@[expose, reducible] def fixtureA : ConstProgram := fixture 1

/-- The leaf has rank zero and its caller rank one. -/
@[expose] def rankA (f : fixtureA.D.Fn) : Nat := if f.val = 0 then 1 else 0

set_option maxRecDepth 100000 in
/-- The structural whitelist accepts an actual call and arithmetic return. -/
theorem constAdmissibleB_zeuge : constAdmissibleB fixtureA = true := by decide

set_option maxRecDepth 100000 in
/-- The finite rank certificate accepts the acyclic edge. -/
theorem constTerminationB_zeuge : constTerminationB fixtureA 1 rankA = true := by decide

/-- Boolean admissibility yields the canonical structural judgment. -/
theorem constAdmissible_zeuge : ConstAdmissible fixtureA :=
  (constAdmissibleB_iff fixtureA).mp constAdmissibleB_zeuge

/-- Boolean termination yields the canonical existential certificate. -/
theorem constTermination_zeuge : ConstTermination fixtureA 1 :=
  constTerminationB_sound fixtureA 1 rankA constTerminationB_zeuge

/-- Fixture C has the self edge f → f. -/
@[expose, reducible] def fixtureC : ConstProgram := fixture 0

set_option maxRecDepth 100000 in
/-- A self edge is refused by the same concrete rank assignment. -/
theorem constRecursion_zeuge :
    constTerminationB fixtureC 1 (fun f => if f.val = 0 then 1 else 0) = false := by decide

/-- The requested global-write or foreign-call fixture B cannot inhabit ConstProgram:
    closed metadata already excludes both kinds of target, before scanning a body. -/
theorem constForbiddenTargets_zeuge (c : ConstProgram) :
    (¬ Nonempty c.D.Glob) ∧ (¬ Nonempty c.D.Ax) :=
  ⟨fun ⟨g⟩ => c.noGlobals g, fun ⟨a⟩ => c.noOracles a⟩

end Gabbro.Grammatik.ConstWitness
