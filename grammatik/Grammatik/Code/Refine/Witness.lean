import Grammatik.Code.Refine.Closure

/-
  File:      Grammatik/Code/Refine/Witness.lean
  Subject:   TRACK L, PHASE L1 -- A NON-DEGENERATE WITNESS of the refinement chain.

  One concrete program, built by hand in machine G, every new lowering form of Track L in it:

      table konto count 4 { v : 0 .. 100 }           -- one table, four slots
      fn get(i : index 4) -> 0 .. 100  { return konto[i].v; }                  -- slot read
      fn put(i : index 4)              { konto[i].v = 7; return; }             -- slot write
      fn wipe()  { traverse konto { konto[k].v = 0; } return; }                 -- the LOOP
      fn main()  { if true { let x = get(2); narrow x to 0 .. 50 else return; }   -- let-call, narrow
                   retry 2 until false { } on_exceeded { }                     -- the bounded retry loop
                   put(1); wipe();                                              -- calls
                   return; }

  What is proved (all at the 64-bit little-endian target, and again at 32-bit big-endian):
    * the layout satisfies `LayoutOk` (the hypothesis of every refinement theorem is inhabited);
    * `lowerFn` succeeds on all four functions (the lowering covers `call`, `bindCall`, `traverse`,
      `narrow` and the slot forms) and produces the expected number of IR blocks;
    * the module of the four lowered functions satisfies `FnOk`, and `lowerFn_callref` is
      INSTANTIATED: for every recursion depth the lowered functions refine the source meaning of a
      call;
    * the source meaning of a call is `ok` somewhere (`rufAt` of `get` on a concrete world), so the
      hypothesis `R f σ ρ = ok σ' v` of `CallRef` is not vacuous.
-/

namespace Gabbro.Code.Lower.Wit

open Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive WFn where
  | get
  | put
  | wipe
  | main
  deriving DecidableEq

def sigGet : Signatur Unit Empty Unit Empty where
  params := [.int 0 3]
  erg := some (.int 0 100)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def sigPut : Signatur Unit Empty Unit Empty where
  params := [.int 0 3]
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def sigNoArg : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def wD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := WFn
  sig := fun | .get => 0 | .put => 1 | _ => 2
  sigNr := fun | 0 => sigGet | 1 => sigPut | _ => sigNoArg
  eigner_nie_erzeugt := fun n _ _ _ h => by
    rcases n with _ | _ | n <;> simp [sigGet, sigPut, sigNoArg] at h
  Inv := Empty
  traeger := fun e => nomatch e
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
  geteilt_bewacht := fun t h => absurd h (by decide)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-! ## 2. The bodies -/

theorem wDarf (Λ : List (Res wD)) : darf wD () Λ := fun w hw => nomatch hw

/-- `get(i)`: `return konto[i].v`. -/
def rGet : Endblock wD (vertragVon wD WFn.get) false [.int 0 3]
    (Signatur.anfang wD (wD.signatur WFn.get)) :=
  .ret (.val (.slot () () (.var .here) (wDarf _))) (List.Perm.refl _)

/-- `put(i)`: `konto[i].v = 7; return`. -/
def rPut : Endblock wD (vertragVon wD WFn.put) false [.int 0 3]
    (Signatur.anfang wD (wD.signatur WFn.put)) :=
  .cons (.assignSlot () () (.var .here)
    (.widen (lo := 7) (hi := 7) (by decide) (by decide) (.lit 7)) rfl (wDarf _))
    (.ret .empty (List.Perm.refl _))

/-- `wipe()`: `traverse konto { konto[k].v = 0 }; return`. -/
def rWipe : Endblock wD (vertragVon wD WFn.wipe) false []
    (Signatur.anfang wD (wD.signatur WFn.wipe)) :=
  .cons (.traverse () .tru (.cons (.assignSlot () () (.var .here)
    (.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0)) rfl (wDarf _)) .nil))
    (.ret .empty (List.Perm.refl _))

theorem wHpGet : RufPasst wD (vertragVon wD WFn.main) (wD.signatur WFn.get) [] where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun _ h => nomatch h

theorem wHpPut : RufPasst wD (vertragVon wD WFn.main) (wD.signatur WFn.put) [] where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun _ h => nomatch h

theorem wHpWipe : RufPasst wD (vertragVon wD WFn.main) (wD.signatur WFn.wipe) [] where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun _ h => nomatch h

/-- The argument `k` (a literal in `0 .. 3`). -/
def argK (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 3) {Γ : Ctx} {Λ : List (Res wD)} :
    Args wD Γ Λ [.int 0 3] :=
  .cons (.widen (lo := k) (hi := k) h0 h1 (.lit k)) .nil

/-- `main()`: under `if true`, a call that binds its result and a `narrow`; a `retry`; then two calls. -/
def rMain : Endblock wD (vertragVon wD WFn.main) false []
    (Signatur.anfang wD (wD.signatur WFn.main)) :=
  .cons (.ite .tru
      (Block.bindCall (τ := .int 0 100) WFn.get (argK 2 (by decide) (by decide)) rfl wHpGet rfl
        (Block.narrow (.var .here) 0 50 (.ret .empty (List.Perm.refl _)) .nil))
      .nil)
    (.cons (.retry 2 .fls .nil .nil)
    (.cons (.call WFn.put (argK 1 (by decide) (by decide)) wHpPut rfl)
      (.cons (.call WFn.wipe .nil wHpWipe rfl)
        (.ret .empty (List.Perm.refl _)))))

/-- The program. -/
def wP : Programm wD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .get => rGet
    | .put => rPut
    | .wipe => rWipe
    | .main => rMain

/-! ## 3. The layout, the module, the oracle -/

def wName : WFn → String
  | .get => "get"
  | .put => "put"
  | .wipe => "wipe"
  | .main => "main"

/-- `konto` is global block 0, an array of four records of one byte-sized field; the four functions are
    the IR functions 0 .. 3. -/
def wLay : Layout wD where
  gblk := fun _ => 0
  tty := fun _ => .arr 4 (.fld (.int 8) .unit)
  rty := fun _ => .fld (.int 8) .unit
  fidx := fun _ _ => 0
  ggblk := fun e => nomatch e
  fno := fun | .get => 0 | .put => 1 | .wipe => 2 | .main => 3

def wO : Orakel wD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- A world: every slot holds `0`. -/
def w0 : World wD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, (fun e => nomatch e), []⟩

/-- The argument environment of `get`/`put`: the index `k` (in `0 .. 3`). -/
def argEnv (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 3) : Env wD (wD.params WFn.get) :=
  .cons (⟨k, h0, h1⟩ : Zahl 0 3) .nil

/-- Is an answer an `ok`? -/
def isOk {f : wD.Fn} : RufAusgang f → Bool
  | .ok _ _ => true
  | _ => false

section Gen

variable [Conf]

/-- **The layout assumptions hold** for the layout above, at every target. -/
theorem wLayOk : LayoutOk wLay where
  tab := fun _ => rfl
  fld := fun _ _ _ => ⟨0, by
    show Ty.fieldOff (.fld (.int 8) .unit) 0 0 = some (0, .int (Ar.wid 0 100))
    have h8 : Ar.wid 0 100 = 8 := by decide
    have hp := Conf.wb_pos
    have hal : Ty.align (.int 8) = 1 := by
      simp [Ty.align, Ty.intAlign]
      omega
    simp [Ty.fieldOff, hal, Ty.roundUp, h8]⟩
  inj := fun _ _ _ _ _ _ => rfl
  tinj := fun _ _ _ => rfl
  gdis := fun _ g => nomatch g
  ginj := fun g => nomatch g
  fsm := fun _ _ => Nat.two_pow_pos _

/-- The IR functions of the four functions, in order (a function whose lowering fails is left out). -/
def wFuncs : List Func :=
  [WFn.get, WFn.put, WFn.wipe, WFn.main].filterMap fun f => lowerFn wLay wP f (wName f)

/-- The module of the lowered functions. -/
def wMod : Modl := ⟨[], wFuncs⟩

end Gen

/-! ## 4. At the 64-bit little-endian target -/

section C64

local instance conf64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- The lowering covers the whole program: all four functions lower. -/
theorem wit64_lowers : ∀ f, ∃ func, lowerFn wLay wP f (wName f) = some func ∧ wMod.funs[wLay.fno f]? = some func := by
  intro f
  cases f
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- **The closing theorem, instantiated**: for every recursion depth, the lowered functions refine the
    source meaning of a call. -/
theorem wit64_callref (S : Sees) (passes : Nat) :
    ∀ n, CallRef wLay wMod S (rufAt wP wO passes n) :=
  lowerFn_callref wLay wLayOk wP wO passes wMod S wName wit64_lowers

/-- The loop is a loop: `wipe` lowers to eight blocks (entry, the four blocks of the counter loop, the
    two blocks of its body, the return). -/
theorem wit64_wipe_blocks : (lowerFn wLay wP WFn.wipe "wipe").map (·.blks.length) = some 8 := rfl

/-- The calling function has the calls, the `narrow` and the `retry`: seventeen blocks. -/
theorem wit64_main_blocks : (lowerFn wLay wP WFn.main "main").map (·.blks.length) = some 17 := rfl

/-- The premise of `CallRef` is not vacuous: the source meaning of `get(1)` is an `ok`. -/
theorem wit64_get_ok : ∃ σ' v, rufAt wP wO 0 1 WFn.get w0 (argEnv 1 (by decide) (by decide)) =
    RufAusgang.ok σ' v := ⟨_, _, rfl⟩

/-- ... and so is that of `main`, which calls the other three (depth 3 suffices). -/
theorem wit64_main_ok : isOk (rufAt wP wO 0 3 WFn.main w0 .nil) = true := by decide +kernel

end C64

/-! ## 5. At the 32-bit big-endian target -/

section C32

local instance conf32 : Conf := ⟨32, true, Or.inl rfl⟩

/-- The lowering covers the whole program: all four functions lower. -/
theorem wit32_lowers : ∀ f, ∃ func, lowerFn wLay wP f (wName f) = some func ∧ wMod.funs[wLay.fno f]? = some func := by
  intro f
  cases f
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- **The closing theorem, instantiated**: for every recursion depth, the lowered functions refine the
    source meaning of a call. -/
theorem wit32_callref (S : Sees) (passes : Nat) :
    ∀ n, CallRef wLay wMod S (rufAt wP wO passes n) :=
  lowerFn_callref wLay wLayOk wP wO passes wMod S wName wit32_lowers

/-- The loop is a loop: `wipe` lowers to eight blocks (entry, the four blocks of the counter loop, the
    two blocks of its body, the return). -/
theorem wit32_wipe_blocks : (lowerFn wLay wP WFn.wipe "wipe").map (·.blks.length) = some 8 := rfl

/-- The calling function has the calls, the `narrow` and the `retry`: seventeen blocks. -/
theorem wit32_main_blocks : (lowerFn wLay wP WFn.main "main").map (·.blks.length) = some 17 := rfl

/-- The premise of `CallRef` is not vacuous: the source meaning of `get(1)` is an `ok`. -/
theorem wit32_get_ok : ∃ σ' v, rufAt wP wO 0 1 WFn.get w0 (argEnv 1 (by decide) (by decide)) =
    RufAusgang.ok σ' v := ⟨_, _, rfl⟩

end C32

end Gabbro.Code.Lower.Wit
