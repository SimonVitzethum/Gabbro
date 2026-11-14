/- C08 R3b: THE FIXTURE OF THE CALL-SITE GOAL WITNESS (`CallSiteGoalZeuge`).

   The smallest unit with a software foreign item that the checker accepts and the runtime
   starts: the one-function, memory-free declaration of `CallSiteZeuge`, now with a VALUE
   answer. The item `g(x : 0..1) -> 0..1` is declared software with the contract
   `requires x != 0`, `ensures result == 1`, and the declared summary `Q` "the answer is 1".
   The body calls `g(1)` and returns the answer under `ensures result == 1`: its post is
   provable only from `g`'s summary, which the class of the body duties grants only where `g`'s
   pre held. The binding `echo` answers its argument: it meets the post exactly where the pre
   holds, and breaks the summary at `x = 0`, so it is no oracle of the full premise of
   `GabbroZielVoll`.

   Proved here: (a) the checker Bool, component by component (each kernel computation over the
   one body); `PostDeckt`, `ForeignVertrag` for `echo`, `HardwareAnnahmenHw`; the pre is
   satisfiable and falsifiable; `echo` breaks the full summary. -/
module

public import Grammatik.Zielsatz.Kern.Spec.Fremd
public import Grammatik.Zielsatz.Atomar.AtomarZiel
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteGoal

open Gabbro.Grammatik

/-- The signature of the one function: no parameter, a `0..1` result. -/
def sig : Signatur Empty Empty Empty Empty where
  params := []
  erg := some (.int 0 1)
  gruende := 0
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One function, one SOFTWARE foreign item `g(x : 0..1) -> 0..1`; no memory, locks or
    providers. -/
def wD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun e => nomatch e
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun e => nomatch e
  eigner := fun e => nomatch e
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => sig
  eigner_nie_erzeugt := fun _ e => nomatch e
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => [.int 0 1]
  aerg := fun _ => some (.int 0 1)
  aschreibt := fun _ e => nomatch e
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ e => nomatch e
  ggeteilt_bewacht := fun e => nomatch e
  axHerkunft := fun _ => some .software
  axBeleg := fun _ => none

instance instDecEqWFn : DecidableEq wD.Fn := inferInstanceAs (DecidableEq Unit)
instance instDecEqWAx : DecidableEq wD.Ax := inferInstanceAs (DecidableEq Unit)

/-- A `0..1` number read off an answer or a result. -/
def zahl (v : Zahl 0 1) : Int := v.n

/-- `g`'s contract: `requires x != 0`, `ensures result == 1`. -/
def contract : CallContract wD (wD.asignatur ()) where
  pre := .not (.eq (.var .here) (.lit 0))
  post := .eq (.var .here) (.lit 1)

/-- The argument `1`. -/
def args : Args wD [] [] (wD.aparams ()) :=
  .cons (.widen (by decide) (by decide) (.lit 1)) .nil

/-- `let r = g(1); return r`. -/
def body : Endblock wD (vertragVon wD ()) false [] [] :=
  .bindAxiom (τ := .int 0 1) () args rfl (fun e => nomatch e) (fun e => nomatch e)
    (fun e => nomatch e) (fun e => nomatch e) (.ret (.val (.var .here)) List.Perm.nil)

/-- The program: `ensures result == 1` on the function, `g`'s contract on the item. -/
def wP : Programm wD where
  invariante := fun e => nomatch e
  requires := fun _ => .tru
  ensures := fun _ => .eq (.var .here) (.lit 1)
  rumpf := fun _ => body
  axVertrag := fun _ => contract

/-- The declared summary of `g`: the answer is `1`. -/
def wQ : AxEns wD := fun _ _ v => decide (zahl v = 1)

def memory : Speicher wD where
  slots := fun e => nomatch e
  globs := fun e => nomatch e

def world : World wD := memory.welt []

/-- The unit: the function declared once as a start. -/
def wE : Einheit wD where
  P := wP
  S := SperrInv.leer wD
  Q := wQ
  starts := [⟨(), .nil⟩]
  sp0 := memory

/-- The answer of an argument list: its one number. -/
def kopfN : Env wD [.int 0 1] → Int
  | .cons v _ => zahl v

/-- **The binding**: `g` answers its argument and changes no memory. -/
def echo : Orakel wD where
  wirktL := fun _ σ ρ => ({ σ with spur := [] }, kopfN ρ)
  regLiesL := fun e => nomatch e
  regSchreib := fun e => nomatch e
  sichtbarL := fun e => nomatch e

/-- The arguments `1` (`true`) and `0` (`false`). -/
def rhoW (b : Bool) : Env wD (wD.aparams ()) :=
  .cons (if b then ⟨1, by decide, by decide⟩ else ⟨0, by decide, by decide⟩) .nil

theorem env1 (ρ : Env wD [.int 0 1]) : ∃ (x : Zahl 0 1) (r : Env wD []), ρ = .cons x r := by
  cases ρ with
  | cons x r => exact ⟨x, r, rfl⟩

/-! ## The pre, the post, the summary -/

/-- The pre holds exactly at the argument `1`. -/
theorem pre_n {σ : World wD} {x : Zahl 0 1} {r : Env wD []}
    (h : AxVor wP.axVertrag () σ (.cons x r)) : x.n = 1 := by
  have h1 : (!decide (x.n = 0)) = true := h
  have h2 : x.n ≠ 0 := by
    intro h0
    rw [h0] at h1
    exact absurd h1 (by decide)
  have h3 := x.lo_le
  have h4 := x.le_hi
  omega

theorem pre_true (σ : World wD) : AxVor wP.axVertrag () σ (rhoW true) := rfl

theorem pre_false (σ : World wD) : ¬ AxVor wP.axVertrag () σ (rhoW false) := by
  intro h
  change false = true at h
  cases h

/-- The post covers the declared summary: both say "the answer is 1". -/
theorem post_cover : PostDeckt wE := by
  intro a _ σ0 ρ σ1 v h
  cases a
  exact h

/-- **The binding's proof**: under the pre `echo` answers `1`, so the post holds; every answer
    decodes (it is the argument, inside `0..1`). -/
theorem binding : ForeignVertrag wE echo := by
  refine ⟨?_, ?_⟩
  · intro a _ σ0 ρ hpre v hv
    cases a
    obtain ⟨x, r, rfl⟩ := env1 ρ
    have hx : x.n = 1 := pre_n hpre
    have h2 : einpassen echo.zeiger (.int 0 1) x.n = some v := hv
    rw [hx] at h2
    have h3 : (some ⟨1, by decide, by decide⟩ : Option (Zahl 0 1)) = some v := h2
    obtain rfl := Option.some.inj h3
    rfl
  · intro a _ σ ρ
    cases a
    obtain ⟨x, r, rfl⟩ := env1 ρ
    have h0 := x.lo_le
    have h1 := x.le_hi
    show sonstPasst echo.zeiger (some (.int 0 1)) 0 x.n ≠ none
    rcases (show x.n = 0 ∨ x.n = 1 by omega) with hx | hx <;> rw [hx] <;> intro h <;> cases h

theorem echo_gut : GutO echo := by
  intro a σ ρ
  refine ⟨rahmen_gleich rfl rfl, rfl, ?_⟩
  intro hgt hgg
  refine ⟨[], [], [], ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro t
    exact nomatch t
  · intro g
    exact nomatch g
  · intro t
    exact nomatch t
  · intro g
    exact nomatch g
  · intro m
    exact nomatch m
  · intro L
    exact nomatch L

/-- (c): the frame and register locality of `echo`; `g` is software, so no summary is assumed. -/
theorem hardware [RootNativeFloat.Hardware] : HardwareAnnahmenHw echo wE.Q := by
  refine ⟨echo_gut, ?_, fun _ hsw => absurd rfl hsw, inferInstance⟩
  constructor
  · intro r
    exact nomatch r
  · intro g
    exact nomatch g

/-- **NON-DEGENERATE**: `echo` breaks the summary at the argument `0`; it is no oracle of the
    full summary premise (c) of `GabbroZielVoll`. -/
theorem echo_not_summary : ¬ AxVertragO wE.Q echo := by
  intro h
  have h0 := h () world (rhoW false) ⟨0, by decide, by decide⟩ rfl
  exact absurd h0 (by decide)

/-! ## (a) the checker, component by component -/

theorem fs_voll : ∀ g : wD.Fn, g ∈ [()] := fun g => by
  cases g
  exact List.mem_singleton_self _

/-- **(a)**: `akzeptiertX_pruefer` accepts the unit. The Bool is split into its components,
    each decided over the one body (no kernel computation over the whole unit at once). -/
theorem checker : akzeptiertX_pruefer.akzeptiert wE [()] [] [] = true := by
  simp only [akzeptiertX_pruefer, AkzeptiertX, Bool.and_eq_true]
  and_intros
  all_goals first
    | exact (schnittstellenB_iff fs_voll).mpr (schnittstellen_standard _ _)
    | decide

end Gabbro.Grammatik.Zielsatz.CallSiteGoal
