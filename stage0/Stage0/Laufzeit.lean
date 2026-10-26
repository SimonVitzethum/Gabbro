/-
  File:      stage0/Stage0/Laufzeit.lean
  Subject:   STAGE 0 of self-hosting (`dokumente/PLAN-SELF-HOSTING.md` §2): the small Lean runtime that runs the
             minimal Gabbro the Gabbro-written checker, compiler and GabbroV are first started with.

  This file holds the parts of `boot src ein` (`Lauf/Boot.lean`) around the run, every one an accepted Lean
  function and nothing new beside them:

  1. the Lean pipeline (`lex`, `parseTopTief`, `pre108`, `elabU`, `lowerAllg` -- the stages of `uebersetzeAllg`);
  2. the goal theorem's checker Bool on the elaborated unit (`akzeptiertU`, i.e. `AkzeptiertX`): a refused program
     is not run;
  3. the subset gate (`imKernB`): no foreign body, no device register, no atomic static, no open region. These are
     the forms whose meaning is a machine answer (the oracle) or, for the open region, whose provider is not yet
     fresh in the model; stage 0 does not run them rather than answer them by a guess;
  4. the declared initial memory (`sp0Of`), with the input bytes written into the field `ein` of the table `io`
     and their number into the static `ein_len`;
  5. the thread machine itself (`Schritt/`, `Lauf/`): `main` on thread 0 of `RufStartG`, every step taken by `zug`
     with its rule of `RufSchrittG` (its parameters are table pointers, whose value is `()`);
  6. the output: the field `aus` of `io` at the slots `0 .. aus_len`.

  The I/O convention is therefore declared IN the program, as ordinary Gabbro:

      static mut ein_len : u32 in 0 .. N = 0;
      static mut aus_len : u32 in 0 .. N = 0;
      table io count N { slot { ein : u32 in 0 .. 255, aus : u32 in 0 .. 255, } }
      impl fn main(t : ptr<normal, rw> io) effects { ... } { ... }

  The run is the semantics, not a second interpreter: `boot_ist_lauf` proves that every output is read from a
  machine the thread machine reaches from the start machine of the pipeline's program. It is exact and slow (a
  world slot is a chain of closures).
-/
import Grammatik.Parser.Cover.Differenz
import Grammatik.GabbroV.GvStartPflicht
import Grammatik.Parser.Elab.UebersetzePipeline

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-! ## Values between bytes and the model -/

/-- The number a value of an integer or `bool` type stands for. -/
def alsZahl {F : Type} {p : F → Nat → Bool} : (τ : Ty) → Val F p τ → Option Int
  | .int _ _, v => some v.n
  | .bool, b => some (cond (show Bool from b) 1 0)
  | _, _ => none

/-- The value of an integer or `bool` type a number stands for, if it lies in the type. -/
def ausZahl {F : Type} {p : F → Nat → Bool} : (τ : Ty) → Int → Option (Val F p τ)
  | .int lo hi, n => if h : lo ≤ n ∧ n ≤ hi then some ⟨n, h.1, h.2⟩ else none
  | .bool, n => if n = 0 then some false else if n = 1 then some true else none
  | _, _ => none

/-- The arguments of `main`: every parameter a table pointer, whose value is `()`. -/
def zeigerArgs {D : Deklaration} : (Γ : Ctx) → Option (Env D Γ)
  | [] => some .nil
  | .ptr t rw :: Γ => (zeigerArgs Γ).map fun ρ => Env.cons (τ := .ptr t rw) () ρ
  | _ :: _ => none

/-! ## The subset and the names of the convention -/

/-- **The subset stage 0 runs**: no foreign body, no device register, no atomic static, no open region. -/
def imKernB (u : UProg) : Bool :=
  u.axs.isEmpty && u.regs.isEmpty && u.globs.all (fun g => !g.atomic) && u.tabs.all (fun t => t.von.isNone)

/-- A field of a table by name. -/
def feldIdx (u : UProg) (t : Fin u.tabs.length) (n : String) : Except String (Fin (fieldCount u t)) :=
  match (List.finRange (fieldCount u t)).find? (fun f => ((tabAt u t).cols[f.val]?.map (·.1)) == some n) with
  | some f => .ok f
  | none => .error ("field unknown: " ++ (tabAt u t).name ++ "." ++ n)

/-- The places of the I/O convention in an elaborated unit. -/
structure Orte (u : UProg) where
  io : Fin u.tabs.length
  ein : Fin (fieldCount u io)
  aus : Fin (fieldCount u io)
  einLen : Fin u.globs.length
  ausLen : Fin u.globs.length
  main : Fin u.fns.length

/-- Find the places of the convention by name. -/
def orteVon (u : UProg) : Except String (Orte u) := do
  let io ← tabIdx u.tabs "io"
  let ein ← feldIdx u io "ein"
  let aus ← feldIdx u io "aus"
  let einLen ← globIdx u.globs "ein_len"
  let ausLen ← globIdx u.globs "aus_len"
  let main ← fnIdx u.fns "main"
  pure ⟨io, ein, aus, einLen, ausLen, main⟩

/-! ## Input, run, output -/

/-- The machine's answers for a unit of the subset: never asked (no foreign body, no register, no atomic). -/
def orakelLeer (D : Deklaration) : Orakel D where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbar := fun _ _ => true

/-- Write the input bytes from slot `k` on into the field `ein`. -/
def schreibEin (u : UProg) (o : Orte u) : World (declOf u) → Int → List UInt8 → Except String (World (declOf u))
  | σ, _, [] => .ok σ
  | σ, k, b :: bs =>
    match ausZahl ((declOf u).typ o.io o.ein) b.toNat with
    | some v => schreibEin u o (σ.storeSlot o.io k o.ein v) (k + 1) bs
    | none => .error "input byte outside the type of io.ein"

/-- **The start world**: the declared initial memory, the input in `io.ein`, its length in `ein_len`. -/
def startWelt (u : UProg) (o : Orte u) (h : sp0OkB u = true) (ein : List UInt8) :
    Except String (World (declOf u)) := do
  if (ein.length : Int) > (declOf u).count o.io then throw "input longer than the table io"
  let σ ← schreibEin u o ((sp0Of u h).welt []) 0 ein
  match ausZahl ((declOf u).gtyp o.einLen) ein.length with
  | some v => pure (σ.storeGlob o.einLen v)
  | none => throw "input length outside the type of ein_len"

/-- The output bytes `io.aus` at the slots `0 .. n`. -/
def leseAus (u : UProg) (o : Orte u) (σ : World (declOf u)) : Nat → Except String (List UInt8)
  | 0 => .ok []
  | n + 1 => do
    let vorn ← leseAus u o σ n
    match alsZahl _ (σ.slots o.io n o.aus) with
    | some z =>
      if 0 ≤ z ∧ z < 256 then pure (vorn ++ [z.toNat.toUInt8]) else throw "output value outside a byte"
    | none => throw "io.aus is not a number field"

/-- **The output of an end world**: `aus_len` bytes of `io.aus`. -/
def ausgabe (u : UProg) (o : Orte u) (σ : World (declOf u)) : Except String (List UInt8) :=
  match alsZahl _ (σ.globs o.ausLen) with
  | some n => if n < 0 then .error "aus_len negative" else leseAus u o σ n.toNat
  | none => .error "aus_len is not a number"

/-- The budgets of a run: machine steps and loop passes (`passes`). -/
structure Budget where
  schritte : Nat := 100000000
  passes : Nat := 1000000

end Gabbro.Stage0
