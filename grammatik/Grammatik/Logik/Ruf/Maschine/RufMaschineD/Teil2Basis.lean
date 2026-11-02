module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
public import Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- `ensures`: the result equals the parameter plus one.
    Context `[.int 0 5, .int 0 5]`: result at `.here`, parameter at `.there .here`. -/
def rufEnsLitD : Expr rufD [.int 0 6, .int 0 5] [] .bool :=
  .eq (.var .here)
    (.add (.widen (by decide) (by decide) (.var (.there .here)) :
          Expr rufD [.int 0 6, .int 0 5] [] (.int 0 5))
        (.widen (by decide) (by decide) (.lit 1) :
          Expr rufD [.int 0 6, .int 0 5] [] (.int 0 1)))

/-- The ensures context computes to result-before-parameters. -/
theorem rufEnsCtxD : ErgCtx (rufD.params rufIncD)
      (rufD.erg rufIncD)
    = [.int 0 6, .int 0 5] := by
  rw [rufD_params rufIncD, rufD_erg rufIncD]
  rfl

/-- The program: `requires` and `ensures` as above; each body returns its
    parameter plus one. -/
def rufPD : Programm rufD where
  invariante := fun i => nomatch i
  requires := fun _ => rufReqD
  ensures := fun _ => rufEnsCtxD ▸ rufEnsLitD
  rumpf
    | true => .ret (.val
        (.add (.var .here)
          (.widen (by decide) (by decide) (.lit 1) :
            Expr rufD (rufD.params rufIncD) (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))) :
        ErgExpr rufD (rufD.params rufIncD)
          (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD))
        (by decide)
    | false => .ret (.val
        (.add (.var .here)
          (.widen (by decide) (by decide) (.lit 1) :
            Expr rufD (rufD.params rufIncD) (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))) :
        ErgExpr rufD (rufD.params rufIncD)
          (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD))
        (by decide)


/-- The empty world over the witness declaration. -/
def rufWeltD : World rufD :=
  ⟨fun _ _ _ => true, fun g => Empty.elim g, []⟩

/-- Entry check holds at the place: param 2 satisfies `requires`. -/
theorem ruf_req_am_ortD :
    ReqAmEintritt rufPD rufIncD rufWeltD rufRhoD := by
  rfl

/-- Return check holds at the place: result 3 = param 2 + 1. -/
theorem ruf_ens_am_ortD :
    EnsAmRueck rufPD rufIncD
      rufWeltD rufWeltD rufRhoD rufVD := by
  rfl

/-- One thread calling the increment function: start state, one `ruf` step,
    one `rueck` step. The start state threads thread 0 at the entry frame of
    `rufIncD` with `rufRhoD`; thread 0's residue is a `call` to test the
    `ruf` rule... -- instead the start state already logs the entry, so the
    witness run is: start, then a `rueck`-shaped return needs a pushed frame.
    We build the run directly: start machine `M0`, one `ruf` step from a
    caller frame, one `rueck` step popping it. -/
def rufInitD : Faden → Σ f : rufD.Fn, Env rufD (rufD.params f) :=
  fun _ => ⟨rufIncD, rufRhoD⟩

def rufM0D : RufMaschineD rufD :=
  RufStartD rufPD ⟨fun _ _ _ => true, fun g => Empty.elim g⟩ rufInitD


/-! ## 9. The witness run: one call and its return (TARGET B, part 2) -/

/-- The callee signature writes nothing: `hw` side of `RufPasst`. -/
theorem rufSigSchreibtFalse (t : rufD.Tab) :
    (rufD.signatur rufIncD).schreibt t = false := by rfl

/-- The call fits: callee writes nothing, consumes nothing, holds nothing. -/
theorem rufHpD : RufPasst rufD (vertragVon rufD rufIncD)
    (rufD.signatur rufIncD) ([] : List (Res rufD)) where
  hw := fun t ht => by rw [rufSigSchreibtFalse t] at ht; cases ht
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The call arguments: the single variable. -/
def rufArgsD : Args rufD [Ty.int 0 5] [] (rufD.params rufIncD) :=
  (rufD_params rufIncD).symm ▸ Args.cons (.var .here) Args.nil

/-- Held-exactly at the empty trace: no locks exist. -/
theorem rufHeldLeerD (spur : List (Ereignis rufD)) :
    HeldGenau ([] : List (Res rufD)) (offen spur) := by
  intro L
  exact nomatch L

/-- The caller residue: a single `call` to the increment function, returning
    to the empty end. -/
def rufCallerResD :
    Endblock rufD (vertragVon rufD rufIncD) false [Ty.int 0 5] [] :=
  .cons (.call rufIncD rufArgsD rufHpD rfl)
    (.ret (.val (.widen (by decide) (by decide) (.var .here))) (by decide))


/-- The caller frame: running `rufIncD` with `rufRhoD`, entry world the empty
    world, residue the caller block above. -/
def rufCallerD : RufRahmenD rufD :=
  ⟨rufIncD, rufRhoD, rufWeltD,
   ⟨false, [Ty.int 0 5], [], rufCallerResD⟩⟩

/-- The caller machine: thread 0 at the caller frame with empty trace and
    empty log; memory empty. -/
def rufCallerMD : RufMaschineD rufD :=
  ⟨⟨fun _ _ _ => true, fun g => Empty.elim g⟩,
   fun _ => ⟨[], rufCallerD, [], []⟩,
   [], rufWeltD⟩

/-- The entry world of step 1 is the thread world itself: the argument
    reads nothing (`var.hier` has no Orte). -/
theorem rufArgsOrteLeerD : rufArgsD.orte = [] := by rfl

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def rufOD : Orakel rufD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- Step 1 fires the `ruf` rule: head matches, locks vacuous, entry world
    is the thread world (no arg reads), evaluated args are `rufRhoD`, no new
    trace events. Every premise is used: `hhead`/`hΛ`/`hs0`/`hrho`/`hneu`
    feed the `RufSchrittD.ruf` constructor. -/
theorem rufSchritt1D :
    RufSchrittD rufPD rufOD 0 rufCallerMD 0
      ⟨(rufCallerMD.speicher),
       rufUpdateD rufCallerMD.faeden 0
         ⟨[rufCallerD],
          ⟨rufIncD, rufRhoD, rufCallerMD.weltVon 0,
           ⟨false, rufD.params rufIncD,
            Signatur.anfang rufD (rufD.signatur rufIncD),
            rufPD.rumpf rufIncD⟩⟩,
          (rufCallerMD.weltVon 0).spur,
          [RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)]⟩,
       rufCallerMD.lauf ++ rufEigenD 0 [],
       rufCallerMD.start⟩ := by
  have hhead : (rufCallerMD.faeden 0).kopf.rest =
      ⟨false, [Ty.int 0 5], [],
        .cons (.call rufIncD rufArgsD rufHpD rfl) _⟩ := rfl
  have hΛ : HeldGenau ([] : List (Res rufD)) (offen (rufCallerMD.faeden 0).spur) :=
    rufHeldLeerD _
  have hs0 : rufCallerMD.weltVon 0 =
      (rufCallerMD.weltVon 0).lese [] (Args.orte rufArgsD) := by
    rw [rufArgsOrteLeerD]
    rfl
  have hrho : rufRhoD = evalArgs (rufCallerMD.weltVon 0) rufArgsD
      (rufCallerMD.weltVon 0) rufRhoD := by
    have : rufCallerMD.weltVon 0 = rufWeltD := rfl
    rw [this]
    rfl
  have hneu : (rufCallerMD.weltVon 0).spur = [] ++ (rufCallerMD.faeden 0).spur := rfl
  exact RufSchrittD.ruf rufCallerMD 0 false [Ty.int 0 5] [] rufIncD rufArgsD
    rufHpD rfl _ rufRhoD hhead hΛ _ hs0 _ hrho _ hneu


/-- The return expression of the callee body: param + 1. -/
def rufRetED : ErgExpr rufD (rufD.params rufIncD)
    (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD) :=
  .val (.add (.var .here)
    ((.widen (by decide) (by decide) (.lit 1) :
      Expr rufD (rufD.params rufIncD)
        (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))))

/-- The callee residue is `ret` of param + 1, definitionally. -/
theorem rufRumpfRetD : rufPD.rumpf rufIncD =
    Endblock.ret rufRetED
      (by decide : (Signatur.anfang rufD (rufD.signatur rufIncD)).Perm
        (vertragVon rufD rufIncD).ende) := by rfl

/-- The return reads nothing. -/
theorem rufRetOrteLeerD : ErgExpr.orte rufRetED = [] := by rfl

/-- The return evaluates to 3 = 2 + 1. -/
theorem rufRetWertD : evalErg rufWeltD rufRetED rufWeltD rufRhoD = rufVD := by rfl

/-- The machine after step 1: name it for step 2. -/
def rufM1D : RufMaschineD rufD :=
  ⟨(rufCallerMD.speicher),
   rufUpdateD rufCallerMD.faeden 0
     ⟨[rufCallerD],
      ⟨rufIncD, rufRhoD, rufCallerMD.weltVon 0,
       ⟨false, rufD.params rufIncD,
        Signatur.anfang rufD (rufD.signatur rufIncD),
        rufPD.rumpf rufIncD⟩⟩,
      (rufCallerMD.weltVon 0).spur,
      [RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)]⟩,
   rufCallerMD.lauf ++ rufEigenD 0 [],
   rufCallerMD.start⟩


end Gabbro.Grammatik
