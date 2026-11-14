module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.ScopedZeuge

@[expose] public section

namespace Gabbro.Stage0.ScopedOutcomeWitness

open Gabbro.Grammatik

/-!
Unexecuted typed companions to `proben-ir/c11-scoped-*`. These are canonical
syntax, G7 steps, and answer-delivery witnesses, not an image acceptance claim.
The source probes additionally demand real runner lock-word releases by
reacquiring the same locks. Only the lead checks this module on integration.
-/

def signature : Signatur Empty Unit Bool Empty where
  params := [.int 0 100, .bool]
  erg := some (.int 0 100)
  gruende := 2
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun _ => true
  konsumiert := []
  produziert := []

/-- Two distinct lexical locks, an original integer/Bool argument pair,
    two reasons, and a mutable global for the entry-world postcondition. -/
def D : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => nomatch t
  Feld := fun t => nomatch t
  decFeld := fun t => nomatch t
  typ := fun t => nomatch t
  erlaubt := fun t => nomatch t
  tabNr := fun _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 100
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => nomatch t
  ggeteilt := fun _ => false
  Lock := Bool
  decLock := inferInstance
  rang := fun L => if L then 1 else 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun t => nomatch t
  gbraucht := fun _ => []
  eigner := fun t => nomatch t
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => signature
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by cases h

abbrev V : Vertrag D := vertragVon D ()
abbrev Params : Ctx := D.params ()
abbrev Answer := ErgVal D V.erg ⊕ Fin V.gruende

def arguments : Env D Params := .cons ⟨23, by decide, by decide⟩ (.cons true .nil)

def initial : Speicher D :=
  ⟨fun t => nomatch t, fun _ => ⟨7, by decide, by decide⟩⟩

def entry : World D := initial.welt []
def holdings : List (Res D) := [.held true, .held false]
def cleanup : RueckRessourcen D V holdings := ⟨[true, false], .refl _⟩
def value : ErgVal D V.erg := ⟨23, by decide, by decide⟩
def reason : Fin V.gruende := ⟨1, by decide⟩

/-- The store is a canonical world operation, recorded while both locks are held. -/
def beforeReturn : World D :=
  ((entry.nimmt false).nimmt true).schreibGlob () holdings ⟨19, by decide, by decide⟩

def resultExpr : ErgExpr D Params holdings V.erg := .val (.var .here)

def returnStmt (why : Bool) : Stmt D V false Params holdings holdings :=
  if why then .retWhyScoped reason cleanup else .retScoped resultExpr cleanup

/-- Both if branches have the same resource-aware exit after the real store. -/
def innerBody (why : Bool) : Block D V false Params holdings holdings :=
  .cons (.assignGlob () (.widen (by decide) (by decide) (.lit 19)) rfl
    (fun _ h => absurd h List.not_mem_nil))
    (.cons (.ite (.var (.there .here))
      (.cons (returnStmt why) .nil) (.cons (returnStmt why) .nil)) .nil)

def outerBody (why : Bool) : Block D V false Params [.held false] [.held false] :=
  .cons (.locks true (by
    intro L h
    cases L <;> simp_all [D]) (innerBody why)) .nil

def body (why : Bool) : Endblock D V false Params [] :=
  .cons (.locks false (fun _ h => absurd h List.not_mem_nil) (outerBody why))
    (.ret (.val (.var .here)) (.refl []))

def post (delta : Int) : Expr D (ErgCtx Params V.erg) [] .bool :=
  .and (.eq (.var .here) (.var (.there .here)))
    (.eq (.glob () (fun _ h => absurd h List.not_mem_nil))
      (.add (.oldG () (fun _ h => absurd h List.not_mem_nil)) (.lit delta)))

def program (why : Bool) : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => post 12
  rumpf := fun _ => body why

def oracle : Orakel D where
  wirktL := fun a => nomatch a
  regLiesL := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbarL := fun _ _ => true

def answer (why : Bool) : Answer := if why then .inr reason else .inl value

def sourceRest (why : Bool) : GRest D V false Params holdings :=
  .dann (.cons (returnStmt why) .nil) .leer

/-- A fixed expected thread record; all execution facts below use G7 itself. -/
def thread {Λ : List (Res D)} (r : GRest D V false Params Λ) (σ : World D)
    (stack : List (RufRahmenG D) := []) : RufFadenG D :=
  ⟨stack, ⟨(), arguments, entry, ⟨false, Params, Λ, arguments, r⟩⟩, σ.spur, []⟩

def source (why : Bool) : RufMaschineG D :=
  ⟨beforeReturn.speicher, fun _ => thread (sourceRest why) beforeReturn, [], entry⟩

/-- Expected successor records use the same update operation as the G rules. -/
def successor (M : RufMaschineG D) (z : RufFadenG D) (events : Lauf D) : RufMaschineG D :=
  ⟨M.speicher, rufUpdateG M.faeden 0 z, M.lauf ++ events, M.start⟩

def captured (why : Bool) : RufMaschineG D :=
  successor (source why)
    (thread (.aufraeumen ⟨answer why, beforeReturn⟩ [true, false]) beforeReturn) []

def innerReleased (why : Bool) : RufMaschineG D :=
  successor (captured why)
    (thread (.aufraeumen ⟨answer why, beforeReturn⟩ [false]) (beforeReturn.gibt true))
    [⟨0, .gibt true⟩]

def finishedThread (why : Bool) : RufFadenG D :=
  thread (.zurueckgekehrt ⟨answer why, beforeReturn⟩)
    ((beforeReturn.gibt true).gibt false)

def finished (why : Bool) : RufMaschineG D :=
  successor (innerReleased why) (finishedThread why) [⟨0, .gibt false⟩]

/-- Reuse the existing accepted-premise actor fixture without modifying it. -/
theorem existing_actor_zeuge :
    RufSchrittG7 scopedZP adO 0 scopedZM 0 scopedZM' := akteur_gruppe7_zeuge.1

theorem lexical_scope_zeuge (why : Bool) : ScopesOkProg (program why) := by
  intro f
  cases f
  cases why <;> rfl

/-- The already existing canonical frame semantics computes both expected
    source-head outcomes; no fixture-specific evaluator supplies them. -/
theorem source_head_semantics_zeuge :
    semK oracle 0 keinRuf (sourceRest false) beforeReturn arguments =
      .zurueck ((beforeReturn.gibt true).gibt false) value ∧
    semK oracle 0 keinRuf (sourceRest true) beforeReturn arguments =
      .why ((beforeReturn.gibt true).gibt false) reason := ⟨rfl, rfl⟩

/-- Both channels evaluate/save at the actual source head, before either release. -/
theorem capture_zeuge (why : Bool) :
    RufSchrittG7 (program why) oracle 0 (source why) 0 (captured why) := by
  cases why with
  | false =>
    exact .rueckScopedWert (source false) 0 arguments (sourceRest false) resultExpr cleanup
      rfl rfl (by decide) (by decide) beforeReturn rfl [] rfl (by decide)
  | true =>
    exact .rueckScopedGrund (source true) 0 arguments (sourceRest true) reason cleanup
      rfl rfl (by decide) (by decide) (by decide)

/-- The two real G7 releases have the required chronological order. -/
theorem release_zeuge (why : Bool) :
    RufSchrittG7 (program why) oracle 0 (captured why) 0 (innerReleased why) ∧
    RufSchrittG7 (program why) oracle 0 (innerReleased why) 0 (finished why) := by
  refine ⟨?_, ?_⟩
  · exact .rueckFreigabe (captured why) 0 arguments ⟨answer why, beforeReturn⟩
      true [false] rfl (by decide)
  · exact .rueckFreigabeLetzte (innerReleased why) 0 arguments
      ⟨answer why, beforeReturn⟩ false rfl (finishedThread why) rfl

/-- Completion retains the original parameters, entry snapshot, saved answer,
    and the stored global value 19, and releases each lock exactly once. -/
theorem root_outcome_zeuge (why : Bool) :
    (finished why).lauf = [⟨0, .gibt true⟩, ⟨0, .gibt false⟩] ∧
    offen ((finished why).faeden 0).spur = [] ∧
    ((finished why).speicher.globs ()).n = 19 ∧
    ((finished why).faeden 0).kopf.rho = arguments ∧
    ((finished why).faeden 0).kopf.s0 = entry ∧
    ((finished why).faeden 0).kopf.rest =
      ⟨false, Params, [], arguments, .zurueckgekehrt ⟨answer why, beforeReturn⟩⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The source-level `old(g) + 12` and original-argument postcondition are true;
    using the post-world for `old`, or the wrong argument, makes them false. -/
theorem ensures_old_parameters_zeuge :
    wahr? (eval entry (post 12) ((beforeReturn.gibt true).gibt false)
      (ergEnv V.erg value arguments)) = true ∧
    wahr? (eval beforeReturn (post 12) ((beforeReturn.gibt true).gibt false)
      (ergEnv V.erg value arguments)) = false ∧
    wahr? (eval entry (post 12) ((beforeReturn.gibt true).gibt false)
      (ergEnv V.erg value (.cons ⟨24, by decide, by decide⟩ (.cons true .nil)))) = false :=
  ⟨rfl, rfl, rfl⟩

/-- Running the canonical typed body includes the if, global store, normal
    callee contract, and the original entry environment. Only the expected
    outcome is asserted here; this is not the retired source runtime. -/
theorem canonical_call_zeuge :
    ∃ σ : World D,
      rufAt (program false) oracle 0 1 () entry arguments = .ok σ value ∧
      (σ.globs ()).n = 19 ∧ σ.haelt = [] := ⟨_, rfl, rfl, rfl⟩

def badProgram (why : Bool) : Programm D :=
  { program why with ensures := fun _ => post 11 }

/-- The false-old negative twin remains a contract failure on normal return. -/
theorem canonical_contract_failure_zeuge :
    rufAt (badProgram false) oracle 0 1 () entry arguments =
      .logik (.nachbedingung ()) := rfl

/-- A reason bypasses that same false normal-return contract while preserving
    the global store; it is not converted into success or a contract failure. -/
theorem canonical_reason_bypass_zeuge :
    ∃ σ : World D,
      rufAt (badProgram true) oracle 0 1 () entry arguments = .why σ reason ∧
      (σ.globs ()).n = 19 ∧ σ.haelt = [] := ⟨_, rfl, rfl, rfl⟩

def singleCleanup : RueckRessourcen D V [.held false] := ⟨[false], .refl _⟩
def singleWorld : World D := entry.nimmt false
def singleSource : RufMaschineG D :=
  ⟨initial, fun _ => thread (.ende (.retWhyScoped reason singleCleanup)) singleWorld, [], entry⟩
def singleCaptured : RufMaschineG D :=
  successor singleSource (thread (.aufraeumen ⟨.inr reason, singleWorld⟩ [false]) singleWorld) []
def singleFinishedThread : RufFadenG D :=
  thread (.zurueckgekehrt ⟨.inr reason, singleWorld⟩) (singleWorld.gibt false)
def singleFinished : RufMaschineG D :=
  successor singleCaptured singleFinishedThread [⟨0, .gibt false⟩]

/-- A reason in an ending source position uses the same last-release delivery. -/
theorem single_reason_zeuge :
    RufSchrittG7 (program true) oracle 0 singleSource 0 singleCaptured ∧
    RufSchrittG7 (program true) oracle 0 singleCaptured 0 singleFinished ∧
    singleFinished.lauf = [⟨0, .gibt false⟩] ∧
    offen (singleFinished.faeden 0).spur = [] := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact .rueckScopedGrund singleSource 0 arguments _ reason singleCleanup
      rfl rfl (by decide) (by decide) (by decide)
  · exact .rueckFreigabeLetzte singleCaptured 0 arguments
      ⟨.inr reason, singleWorld⟩ false rfl singleFinishedThread rfl

def emptyCleanup : RueckRessourcen D V [] := ⟨[], .refl _⟩
def directRest (why : Bool) : GRest D V false Params [] :=
  .ende (if why then .retWhyScoped reason emptyCleanup
    else .retScoped (.val (.var .here)) emptyCleanup)
def directSource (why : Bool) : RufMaschineG D :=
  ⟨initial, fun _ => thread (directRest why) entry, [], entry⟩
def directFinishedThread (why : Bool) : RufFadenG D :=
  thread (.zurueckgekehrt ⟨answer why, entry⟩) entry
def directFinished (why : Bool) : RufMaschineG D :=
  successor (directSource why) (directFinishedThread why) []

/-- G7's explicit empty-cleanup cases deliver both channels without a release.
    Source outside lexical scopes retains its existing exact-return constructors. -/
theorem empty_delivery_zeuge (why : Bool) :
    RufSchrittG7 (program why) oracle 0 (directSource why) 0 (directFinished why) ∧
    (directFinished why).lauf = [] ∧
    ((directFinished why).faeden 0).kopf.rho = arguments := by
  refine ⟨?_, rfl, rfl⟩
  cases why with
  | false =>
    exact .rueckScopedWertDirekt (directSource false) 0 arguments (directRest false)
      (.val (.var .here)) emptyCleanup rfl rfl (by decide) (by decide)
      entry rfl [] rfl rfl (directFinishedThread false) rfl
  | true =>
    exact .rueckScopedGrundDirekt (directSource true) 0 arguments (directRest true)
      reason emptyCleanup rfl rfl (by decide) (by decide) rfl (directFinishedThread true) rfl

def handler : Endblock D V false (.why 2 :: Params) [] :=
  .ret (.val (.widen (by decide) (by decide) (.lit 0))) (.refl [])
def continuation : GRest D V false Params [] :=
  .ende (.ret (.val (.var .here)) (.refl []))
def caller : RufRahmenG D :=
  ⟨(), arguments, entry, ⟨false, Params, [], arguments,
    .wartetSonst (τ := .int 0 100) 2 handler .nil continuation⟩⟩

def resumedValue : RufFadenG D :=
  ⟨[], ⟨(), arguments, entry,
    ⟨false, .int 0 100 :: Params, [], .cons value arguments,
      .dann .nil (.schrumpf continuation)⟩⟩,
    ((beforeReturn.gibt true).gibt false).spur,
    [.rueck () arguments value entry ((beforeReturn.gibt true).gibt false)]⟩
def resumedReason : RufFadenG D :=
  ⟨[], ⟨(), arguments, entry,
    ⟨false, .why 2 :: Params, [], .cons reason arguments,
      .dann handler.alsBlock.2 (.abbruch (.schrumpf continuation))⟩⟩,
    ((beforeReturn.gibt true).gibt false).spur,
    [.why () arguments reason entry ((beforeReturn.gibt true).gibt false)]⟩

/-- A suspended fallible caller receives the exact value/reason and keeps its
    entry record. The log records the callee's original arguments and s0. -/
theorem callee_delivery_zeuge :
    rufAntwortG
      (thread (.aufraeumen ⟨.inl value, beforeReturn⟩ [false])
        (beforeReturn.gibt true) [caller])
      beforeReturn ((beforeReturn.gibt true).gibt false) (.inl value) = some resumedValue ∧
    rufAntwortG
      (thread (.aufraeumen ⟨.inr reason, beforeReturn⟩ [false])
        (beforeReturn.gibt true) [caller])
      beforeReturn ((beforeReturn.gibt true).gibt false) (.inr reason) = some resumedReason :=
  ⟨rfl, rfl⟩

/-- The saved pre-release world survives later unrelated shared-world writes;
    a completed root never re-reads its saved answer or entry snapshot. -/
theorem saved_world_zeuge :
    let changed := { finished false with
      speicher := (((finished false).speicher.welt []).storeGlob ()
        ⟨99, by decide, by decide⟩).speicher }
    (changed.speicher.globs ()).n = 99 ∧
    (changed.faeden 0).kopf.rest =
      ⟨false, Params, [], arguments, .zurueckgekehrt ⟨.inl value, beforeReturn⟩⟩ ∧
    (beforeReturn.globs ()).n = 19 ∧ (entry.globs ()).n = 7 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Gabbro.Stage0.ScopedOutcomeWitness
