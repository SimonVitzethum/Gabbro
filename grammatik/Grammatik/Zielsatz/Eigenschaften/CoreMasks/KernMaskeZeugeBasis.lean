/-
  File:      Grammatik/Zielsatz/Eigenschaften/KernMaskeZeuge.lean
  Subject:   The witnesses of the per-core mask state (`KernMaske.lean`): ONE program, two
             declarations that differ in nothing but whether its lock is declared `masks irqs`.

  The fixture is the smallest one that has the shape of `beispiele/gift/460`: one lock `()`,
  two functions with the same body `locks () { }; return`, `h` an interrupt handler
  (`Programm.unterbricht`) and `t` an ordinary function. The declaration `wD m` has
  `maskiert := fun _ => m`; the start has thread 0 running `h` and thread 1 running `t`, both on
  core 0 (`wk`).

  * `ohne_maske_verklemmt` (`m = false`): thread 1 takes the lock, the entry guard admits the
    handler (the core is unmasked), the handler stands at a lock its core's thread holds and
    waits for it (`WartetG`), every other thread is held back by run to completion, and
    `KernHaltM` is FALSE at the machine reached. The checker side agrees: `w_masken_falsch`.
  * `mit_maske_verweigert` (`m = true`): the same two steps of thread 1 set the core's mask
    (`maske_nichtleer_iff`), and the model REFUSES the handler's entry step. PLANTED DEFECT: the
    step the guard refuses is a step of plain machine G (`RufSchrittG`) and ends with the
    handler standing at the held lock, so the safety below rests on the guard and on nothing else.
  * `mit_maske_nach_freigabe`: after thread 1 leaves its section and releases the lock the mask
    is empty and the handler's entry is a guarded step: the guard delays, it does not block.
  * `mit_maske_sicher` (`m = true`): `KernHaltM` holds on EVERY guarded run -- `kernHaltM_aus`
    from the closure (`w_abg_wahr`) and the discipline (`w_masken_wahr`), the schedule derived
    from the guards, not assumed.
-/
module
public import Grammatik.Zielsatz.Eigenschaften.CoreMasks.KernMaske
public import Grammatik.Zielsatz.Eigenschaften.CoreMasks.KernMaskeGleich
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.KernMaskeFix
open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

inductive WFn where
  | h
  | t
  deriving DecidableEq

def wSig : Signatur Empty Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def wD (m : Bool) : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => nomatch t
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun t _ => nomatch t
  erlaubt := fun t _ _ _ => nomatch t
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun t => nomatch t
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => m
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun t => nomatch t
  gbraucht := fun e => nomatch e
  eigner := fun t => nomatch t
  Fn := WFn
  sig := fun _ => 0
  sigNr := fun _ => wSig
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

instance (m : Bool) : DecidableEq (wD m).Fn := inferInstanceAs (DecidableEq WFn)

def wRumpf (m : Bool) (f : WFn) : Endblock (wD m) (vertragVon (wD m) f) false [] [] :=
  .cons (.locks () (fun _ h => nomatch h) .nil) (.ret .empty List.Perm.nil)

def wP (m : Bool) : Programm (wD m) where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun f => wRumpf m f
  unterbricht
    | .h => true
    | .t => false

def wFs (m : Bool) : List (wD m).Fn := [WFn.h, WFn.t]

theorem wFs_voll (m : Bool) : ∀ g : (wD m).Fn, g ∈ wFs m := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem w_masken_wahr : maskenB (wP true) (wFs true) = true := by decide
theorem w_masken_falsch : maskenB (wP false) (wFs false) = false := by decide
theorem w_abg_wahr : abgAlleB (wP true) (wFs true) = true := by decide


def wLocksS (m : Bool) (f : WFn) : Stmt (wD m) (vertragVon (wD m) f) false [] [] [] :=
  .locks () (fun _ h => nomatch h) .nil

def wRet (m : Bool) (f : WFn) : Endblock (wD m) (vertragVon (wD m) f) false [] [] :=
  .ret .empty List.Perm.nil

def wO (m : Bool) : Orakel (wD m) where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

def wInit (m : Bool) : Faden → Σ f : (wD m).Fn, Env (wD m) ((wD m).params f)
  | 0 => ⟨WFn.h, .nil⟩
  | _ + 1 => ⟨WFn.t, .nil⟩

def wSp (m : Bool) : Speicher (wD m) := ⟨fun t _ _ => (nomatch t), fun g => nomatch g⟩

abbrev wM0 (m : Bool) : RufMaschineG (wD m) := RufStartG (wP m) (wSp m) (wInit m)

theorem wM0_offen (m : Bool) (f : Faden) : offen ((wM0 m).faeden f).spur = [] := by
  match f with
  | 0 => rfl
  | _ + 1 => rfl

theorem wH0 (m : Bool) : HandlerVon (wP m) (wM0 m) 0 := by rfl

theorem w_handler (m : Bool) (t : Faden) (h : HandlerVon (wP m) (wM0 m) t) : t = 0 := by
  match t, h with
  | 0, _ => rfl
  | _ + 1, h => exact Bool.noConfusion h

def wZ0 (m : Bool) : KernZ (wD m) := ⟨wM0 m, fun _ => [], fun _ => False⟩

theorem wStart (m : Bool) : KernStart (fun _ => 0) (wM0 m) (wZ0 m) :=
  ⟨rfl, fun c f L => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, _, hL⟩ => by
    rw [wM0_offen] at hL
    exact absurd hL List.not_mem_nil⟩, fun _ h => h⟩


abbrev wk : Faden → Nat := fun _ => 0

/-- **The runs of the fixture, common prefix**: thread 1 (`t`) unfolds its body, takes the lock,
    leaves the empty section (`dannLeer`) and releases it (`freiGib`); no other thread moves. -/
theorem w_prefix (m : Bool) : ∃ M1 M2 M3 M4 : RufMaschineG (wD m),
    RufSchrittG (wP m) (wO m) 0 (wM0 m) 1 M1 ∧ RufSchrittG (wP m) (wO m) 0 M1 1 M2 ∧
    RufSchrittG (wP m) (wO m) 0 M2 1 M3 ∧ RufSchrittG (wP m) (wO m) 0 M3 1 M4 ∧
    () ∈ offen (M2.faeden 1).spur ∧ offen (M4.faeden 1).spur = [] ∧
    (∀ f, f ≠ 1 → M2.faeden f = (wM0 m).faeden f) ∧
    (∀ f, f ≠ 1 → M4.faeden f = (wM0 m).faeden f) := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := wP m) (O := wO m) (passes := 0) (M := wM0 m)
    (f := 1) rfl (wLocksS m WFn.t) (wRet m WFn.t) .nil rfl rfl
  have e1 : offen (M1.faeden 1).spur = [] := by
    rw [hZ1.1]
    exact wM0_offen m 1
  have hfrei : RufFreiG M1 1 () := by
    intro g hg
    rw [rufSchrittG_fremd s1 g hg, wM0_offen]
    exact List.not_mem_nil
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := wP m) (O := wO m) (passes := 0) (M := M1) (f := 1)
    hZ1.1 () (fun _ h => absurd h List.not_mem_nil) .nil .nil (.ende (wRet m WFn.t)) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res (wD m))) ↔ L ∈ offen ((wM0 m).faeden 1).spur
      rw [wM0_offen]
      simp only [List.not_mem_nil]) hfrei
  obtain ⟨M3, s3, hZ3⟩ := w_dannLeer (P := wP m) (O := wO m) (passes := 0) (M := M2) (f := 1)
    hZ2.1 (.frei () (.dann .nil (.ende (wRet m WFn.t)))) .nil rfl
  obtain ⟨M4, s4, hZ4⟩ := w_freiGib (P := wP m) (O := wO m) (passes := 0) (M := M3) (f := 1)
    hZ3.1 () (.dann .nil (.ende (wRet m WFn.t))) .nil rfl
  have hn2 : (M2.faeden 1).spur = Ereignis.nimmt () (offen (M1.weltVon 1).spur) ::
      (M1.weltVon 1).spur := by
    rw [hZ2.1]
    rfl
  have hn3 : (M3.faeden 1).spur = (M2.faeden 1).spur := by
    rw [hZ3.1]
    rfl
  have hn4 : (M4.faeden 1).spur = Ereignis.gibt () :: (M3.faeden 1).spur := by
    rw [hZ4.1]
    rfl
  refine ⟨M1, M2, M3, M4, s1, s2, s3, s4, ?_, ?_, ?_, ?_⟩
  · rw [hn2]
    exact List.mem_cons_self
  · rw [hn4, hn3, hn2]
    have e1' : offen (M1.weltVon 1).spur = [] := e1
    simp only [offen, e1']
    first | rfl | decide
  · intro f hf
    rw [rufSchrittG_fremd s2 f hf, rufSchrittG_fremd s1 f hf]
  · intro f hf
    rw [rufSchrittG_fremd s4 f hf, rufSchrittG_fremd s3 f hf, rufSchrittG_fremd s2 f hf,
      rufSchrittG_fremd s1 f hf]



end Gabbro.Grammatik.Zielsatz.KernMaskeFix
