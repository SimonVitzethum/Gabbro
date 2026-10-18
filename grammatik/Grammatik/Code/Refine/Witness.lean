import Grammatik.Code.Refine.Calls.Closure

/-
  File:      Grammatik/Code/Refine/Witness.lean
  Subject:   TRACK L, PHASE L1 -- A NON-DEGENERATE WITNESS of the refinement chain.

  One concrete program, built by hand in machine G, every new lowering form of Track L in it:

      table konto count 4 { v : 0 .. 100 }           -- one table, four slots
      fn get(i : index 4) -> 0 .. 100  { return konto[i % 4].v; }              -- slot read, remainder
      fn put(i : index 4)              { konto[i].v = 7 / 2; return; }         -- slot write, division
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
  | mt
  | bits
  | fail
  | callf
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

/-- A function with a failure channel: one argument, an answer in `0 .. 100`, two reasons. -/
def sigFail : Signatur Unit Empty Unit Empty where
  params := [.int 0 3]
  erg := some (.int 0 100)
  gruende := 2
  haelt := []
  schreibt := fun _ => false
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
  sig := fun | .get => 0 | .put => 1 | .fail => 3 | _ => 2
  sigNr := fun | 0 => sigGet | 1 => sigPut | 3 => sigFail | _ => sigNoArg
  eigner_nie_erzeugt := fun n _ _ _ h => by
    rcases n with _ | _ | _ | _ | n <;> simp [sigGet, sigPut, sigNoArg, sigFail] at h
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

/-- `get(i)`: `return konto[i % 4].v` (a remainder: the divisor is a fact of the range). -/
def rGet : Endblock wD (vertragVon wD WFn.get) false [.int 0 3]
    (Signatur.anfang wD (wD.signatur WFn.get)) :=
  .ret (.val (.slot () () (.rem (by decide) (by decide) (.var .here) (.lit 4)) (wDarf _))) (List.Perm.refl _)

/-- `put(i)`: `konto[i].v = 7 / 2; return` (a division by a number `>= 1`). -/
def rPut : Endblock wD (vertragVon wD WFn.put) false [.int 0 3]
    (Signatur.anfang wD (wD.signatur WFn.put)) :=
  .cons (.assignSlot () () (.var .here)
    (.widen (lo := 0) (hi := 7) (by decide) (by decide) (.div (by decide) (by decide) (.lit 7) (.lit 2)))
    rfl (wDarf _))
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

/-- `mt()`: the three matches. `match some(2)` (an option: the present arm binds the index), `match` on
    the reason number 1 of 3 (a switch), `match` on the tagged value of case 1 with payload 5 (the case
    expression builds the word, the match takes it apart again). -/
def rMt : Endblock wD (vertragVon wD WFn.mt) false []
    (Signatur.anfang wD (wD.signatur WFn.mt)) :=
  .cons (.onOption (n := 4)
      (.some (.widen (lo := 2) (hi := 2) (by decide) (by decide) (.lit 2)))
      (.cons (.assignSlot () () (.var .here)
        (.widen (lo := 1) (hi := 1) (by decide) (by decide) (.lit 1)) rfl (wDarf _)) .nil)
      .nil)
  (.cons (.onWhy (n := 3) (.why 3 ⟨1, by decide⟩)
      (.cons .nil (.cons (.cons (.assignSlot () ()
          (.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0))
          (.widen (lo := 2) (hi := 2) (by decide) (by decide) (.lit 2)) rfl (wDarf _)) .nil)
        (.cons .nil .nil))))
  (.cons (.onTag (cs := [none, some (0, 9)])
      (.case [none, some (0, 9)] ⟨1, by decide⟩
        (.num (.widen (lo := 5) (hi := 5) (by decide) (by decide) (.lit 5))))
      (.cons .nil (.cons (c := some (0, 9))
        (.cons (.assignSlot () ()
          (.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0))
          (.widen (lo := 0) (hi := 9) (by decide) (by decide) (.var .here)) rfl (wDarf _)) .nil)
        .nil)))
  (.ret .empty (List.Perm.refl _))))

/-- `bits()`: the signed and bitwise forms, each on literals: signed division and remainder, `&`, `|`, `^`,
    `<<`, `>>` (every one's precondition is a fact of the ranges, `Refine/Bits/Forms.lean`). -/
def rBits : Endblock wD (vertragVon wD WFn.bits) false []
    (Signatur.anfang wD (wD.signatur WFn.bits)) :=
  .bind (.sdiv (by decide) (.lit 100) (.lit 3))
  (.bind (.srem (by decide) (.lit 7) (.lit 3))
  (.bind (.band (by decide) (by decide) (.lit 12) (.lit 10))
  (.bind (.bor 8 (by decide) (by decide) (by decide) (by decide) (.lit 5) (.lit 6))
  (.bind (.bxor 8 (by decide) (by decide) (by decide) (by decide) (.lit 5) (.lit 6))
  (.bind (.shl 8 (by decide) (by decide) (by decide) (by decide) (.lit 3) (.lit 2))
  (.bind (.shr 8 (by decide) (by decide) (by decide) (by decide) (.lit 200) (.lit 3))
  (.ret .empty (List.Perm.refl _))))))))

/-- `fail(i)`: `return why 1` below 2, else `return konto[i].v` (an answer word, or a reason). -/
def rFail : Endblock wD (vertragVon wD WFn.fail) false [.int 0 3]
    (Signatur.anfang wD (wD.signatur WFn.fail)) :=
  .cons (.ite (.lt (.var .here) (.lit 2))
      (.cons (.retWhy ⟨1, by decide⟩ (List.Perm.refl _)) .nil) .nil)
    (.ret (.val (.slot () () (.var .here) (wDarf _))) (List.Perm.refl _))

theorem wHpFail : RufPasst wD (vertragVon wD WFn.callf) (wD.signatur WFn.fail) [] where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun _ h => nomatch h

/-- `callf()`: two calls that may fail, `let x = fail(3) else (r) { .. }` (answers a value: the `else` arm
    is not taken) and `let y = fail(1) else (r) { return }` (answers the reason `1`: the `else` arm returns). -/
def rCallf : Endblock wD (vertragVon wD WFn.callf) false []
    (Signatur.anfang wD (wD.signatur WFn.callf)) :=
  .cons (.ite .tru
      (Block.bindCallElse (τ := .int 0 100) WFn.fail (argK 3 (by decide) (by decide)) rfl wHpFail (by decide)
        (.ret .empty (List.Perm.refl _)) .nil) .nil)
  (.cons (.ite .tru
      (Block.bindCallElse (τ := .int 0 100) WFn.fail (argK 1 (by decide) (by decide)) rfl wHpFail (by decide)
        (.ret .empty (List.Perm.refl _)) .nil) .nil)
  (.ret .empty (List.Perm.refl _)))

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
    | .mt => rMt
    | .bits => rBits
    | .fail => rFail
    | .callf => rCallf

/-! ## 3. The layout, the module, the oracle -/

def wName : WFn → String
  | .get => "get"
  | .put => "put"
  | .wipe => "wipe"
  | .main => "main"
  | .mt => "mt"
  | .bits => "bits"
  | .fail => "fail"
  | .callf => "callf"

/-- `konto` is global block 0, an array of four records of one byte-sized field; the four functions are
    the IR functions 0 .. 3. -/
def wLay : Layout wD where
  gblk := fun _ => 0
  tty := fun _ => .arr 4 (.fld (.int 8) .unit)
  rty := fun _ => .fld (.int 8) .unit
  fidx := fun _ _ => 0
  ggblk := fun e => nomatch e
  lblk := fun _ => 100
  lsrv := fun _ => 101
  shared := fun e => nomatch e
  fno := fun | .get => 0 | .put => 1 | .wipe => 2 | .main => 3 | .mt => 4 | .bits => 5 | .fail => 6 | .callf => 7

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

/-- Does the lowered function contain a binary instruction with this operator? -/
def usesOp (op : BinOp) (f : Func) : Bool :=
  f.blks.any fun b => b.body.any fun i => match i with
    | .bin _ o _ _ _ => decide (o = op)
    | _ => false

/-- Does the lowered function contain a block whose terminator satisfies this test? -/
def usesTerm (p : Term → Bool) (f : Func) : Bool := f.blks.any fun b => p b.term

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
  lkT := fun _ _ => ⟨by show (100 : Nat) ≠ 0; decide, by show (101 : Nat) ≠ 0; decide⟩
  lkG := fun _ g => nomatch g
  lkX := fun _ _ => by show (100 : Nat) ≠ 101; decide
  lkN := fun _ _ _ => rfl
  lkS := fun _ _ _ => rfl
  shAtomic := fun g => nomatch g
  fsm := fun _ _ => Nat.two_pow_pos _

/-- The IR functions of the four functions, in order (a function whose lowering fails is left out). -/
def wFuncs : List Func :=
  [WFn.get, WFn.put, WFn.wipe, WFn.main, WFn.mt, WFn.bits, WFn.fail, WFn.callf].filterMap fun f => lowerFn wLay wP f (wName f)

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

/-- `put` lowers its division to an unsigned division, `get` its remainder to an unsigned remainder. -/
theorem wit64_put_udiv : (lowerFn wLay wP WFn.put "put").map (usesOp .udiv) = some true := by decide +kernel

theorem wit64_get_urem : (lowerFn wLay wP WFn.get "get").map (usesOp .urem) = some true := by decide +kernel

/-- The three matches lower: `mt` has a `switch` (the reason and the tagged value), a signed branch (the
    option), the case number and the payload are an unsigned remainder and division. -/
theorem wit64_mt_forms : (lowerFn wLay wP WFn.mt "mt").map (fun f =>
    usesTerm (fun | .sw .. => true | _ => false) f && usesTerm (fun | .brc .slt .. => true | _ => false) f &&
    usesOp .urem f && usesOp .udiv f) = some true := by decide +kernel

/-- The failure channel: `fail` answers its word by a multiplication (`ret`) and subtraction-free reason words;
    `callf` takes the word apart with an unsigned remainder and division and branches. -/
theorem wit64_fail_forms : (lowerFn wLay wP WFn.fail "fail").map (fun f => usesOp .mul f) = some true ∧
    (lowerFn wLay wP WFn.callf "callf").map (fun f => usesOp .urem f && usesOp .udiv f && usesOp .sub f) =
      some true := by
  constructor <;> decide +kernel

/-- ... and the source meaning of `callf` is an `ok`: it takes the value arm once and the reason arm once. -/
theorem wit64_callf_ok : isOk (rufAt wP wO 0 3 WFn.callf w0 .nil) = true := by decide +kernel

/-- The signed and bitwise forms lower to their instructions: signed division and remainder, and, or, xor,
    shift left, logical shift right. -/
theorem wit64_bits_forms : (lowerFn wLay wP WFn.bits "bits").map (fun f =>
    usesOp .sdiv f && usesOp .srem f && usesOp .and f && usesOp .or f && usesOp .xor f && usesOp .shl f &&
    usesOp .lshr f) = some true := by decide +kernel

theorem wit64_bits_ok : isOk (rufAt wP wO 0 1 WFn.bits w0 .nil) = true := by decide +kernel

/-- ... and the source meaning of `mt` is an `ok`: the premise of the refinement is not vacuous. -/
theorem wit64_mt_ok : isOk (rufAt wP wO 0 1 WFn.mt w0 .nil) = true := by decide +kernel

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

/-- The three matches lower, at the other target too. -/
theorem wit32_mt_forms : (lowerFn wLay wP WFn.mt "mt").map (fun f =>
    usesTerm (fun | .sw .. => true | _ => false) f && usesTerm (fun | .brc .slt .. => true | _ => false) f &&
    usesOp .urem f && usesOp .udiv f) = some true := by decide +kernel

/-- The failure channel lowers at the other target too. -/
theorem wit32_fail_forms : (lowerFn wLay wP WFn.fail "fail").map (fun f => usesOp .mul f) = some true ∧
    (lowerFn wLay wP WFn.callf "callf").map (fun f => usesOp .urem f && usesOp .udiv f && usesOp .sub f) =
      some true := by
  constructor <;> decide +kernel

/-- The signed and bitwise forms lower at the other target too. -/
theorem wit32_bits_forms : (lowerFn wLay wP WFn.bits "bits").map (fun f =>
    usesOp .sdiv f && usesOp .srem f && usesOp .and f && usesOp .or f && usesOp .xor f && usesOp .shl f &&
    usesOp .lshr f) = some true := by decide +kernel

/-- The premise of `CallRef` is not vacuous: the source meaning of `get(1)` is an `ok`. -/
theorem wit32_get_ok : ∃ σ' v, rufAt wP wO 0 1 WFn.get w0 (argEnv 1 (by decide) (by decide)) =
    RufAusgang.ok σ' v := ⟨_, _, rfl⟩

/-- `put` lowers its division to an unsigned division, `get` its remainder to an unsigned remainder. -/
theorem wit32_put_udiv : (lowerFn wLay wP WFn.put "put").map (usesOp .udiv) = some true := by decide +kernel

theorem wit32_get_urem : (lowerFn wLay wP WFn.get "get").map (usesOp .urem) = some true := by decide +kernel

end C32

end Gabbro.Code.Lower.Wit
