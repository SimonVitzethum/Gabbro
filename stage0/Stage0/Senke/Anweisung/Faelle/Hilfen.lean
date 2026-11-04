/-
  File:      stage0/Stage0/Senke/Anweisung/Faelle/Hilfen.lean
  Subject:   The helper definitions of the statement lowering (`Anweisung.lean`): float literal, call tails,
             return/else/traverse/tag/narrow code pieces. Split out of `Anweisung.lean` unchanged.
-/
module
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Return
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotContext
public import Stage0.Senke.Ausdruck.Gleit.Bereich
public import Stage0.Senke.Stopp
public import Stage0.Senke.Tor
public import Stage0.Senke.Tore.Code
public import Stage0.Senke.Sperre.Code
public import Stage0.Senke.Anweisung.Bytes.Code
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Allocation
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- Materialise a kernel-rounded constant, or stop exactly at G's range check.
    The continuation is lazy: a failing range never lowers unreachable code. -/
def floatLiteralL (d : Nat) (q low high : Int × Int)
    (rest : Unit → Option (List II × Nat)) : Option (List II × Nat) :=
  match gleitPasst low high (bruch q) with
  | none => some (stopC 107 d, d + 8)
  | some _ => do
    let cr ← rest ()
    let cw := konstWL 4 (Gleitkomma.zuBits Gleitkomma.f64 (bruch q)) d
    pure (cw.1 ++ cr.1, max cw.2 cr.2)

/-- The arguments of a call into the callee's parameter slots from `p` (the callee frame's first variable slot);
    the head goes highest. The last argument is computed first, so a later one's scratch slots lie above every
    argument already in place. -/
def lowA (L : Lay D) {Λ : List (Res D)} : {Γ : Ctx} → {τs : List Ty} → Args D Γ Λ τs → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, _, .nil, p, _ => some ([], p)
  | _, _ :: τs, .cons e rest, p, reserved => do
    let cr ← lowA L rest p reserved
    let ce ← lowE L e (p + contextWords τs) reserved
    pure (cr.1 ++ ce.1, max cr.2 ce.2)

/-- The shared call tail: depth one less, a constant target or the pointer saved at `F` before arguments
    are evaluated, then `call`. The argument count determines the scratch slot above the callee frame. -/
def callTailN (np address F : Nat) (indirect : Bool) : List II :=
  [ci 1 ((F + FB + np : Nat) : Int) 1 0,
   ci 4 ((F + 2 : Nat) : Int) 2 ((F + FB + np : Nat) : Int),
   if indirect then ci 2 ((F + FB + np : Nat) : Int) F 0
   else ci 1 ((F + FB + np : Nat) : Int) address 0,
   ci 20 ((F + FB + np : Nat) : Int) F 0]

def callTail (A : D.Fn → Nat) (f : D.Fn) (F : Nat) (indirect : Bool := false) : List II :=
  callTailN (contextWords (D.params f)) (A f) F indirect

def callC (A : D.Fn → Nat) (f : D.Fn) (F : Nat) (ca : List II) : List II := ca ++ callTail A f F

def callTop (f : D.Fn) (F t : Nat) : Nat := max t (F + FB + (contextWords (D.params f)) + 1)

/-- The pointer is evaluated before the arguments, into the future callee's return-pc slot.
    Argument evaluation and the depth calculation preserve it until the call loads its target. -/
def indC (n F : Nat) (cp ca : List II) : List II := cp ++ (ca ++ callTailN (contextWords (D.sigNr n).params) 0 F true)

def indTop (n F tp ta : Nat) : Nat := max tp (max ta (F + FB + (contextWords (D.sigNr n).params) + 1))

def lowInd (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (reserved : Nat := 0) : Option (List II × Nat) := do
  if (D.sigNr n).gruende = 0 then do
    let cp ← lowE (reserved := reserved) L p ((frei Γ reserved))
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    pure (indC (D := D) n ((frei Γ reserved)) cp.1 ca.1, indTop (D := D) n ((frei Γ reserved)) cp.2 ca.2)
  else none

def lowIndElse (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (reserved : Nat := 0) : Option (List II × Nat) := do
  if 0 < (D.sigNr n).gruende then do
    let cp ← lowE (reserved := reserved) L p ((frei Γ reserved))
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    pure (indC (D := D) n ((frei Γ reserved)) cp.1 ca.1, indTop (D := D) n ((frei Γ reserved)) cp.2 ca.2)
  else none

/-- The top of a fallible indirect call with its two continuations: the call
    frame from `lowIndElse`, the shared receive area, and both arms.
    Written with the explicit receive area (not `receiveTop`) so `omega`
    sees the same atoms as the `callIndElse_ok` bound. -/
def elseTopInd (n : Nat) (s tc tr te : Nat) : Nat :=
  max tc (max (s + FB + (contextWords (D.sigNr n).params) + returnWords (D.sigNr n).erg (D.sigNr n).gruende + 1) (max tr te))

def lowErg (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → ErgExpr D Γ Λ e → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, .empty, d, reserved => some ([ci 1 d 0 0], d + 1)
  | some τ, .val e, d, reserved =>
    (lowE (reserved := reserved) L e d).map fun p => (p.1, max p.2 (d + valueWords τ))

/-- A scoped normal return emits the ordinary return code; the release of the
    scopes is ghost (`RueckgabeScoped`). -/
def lowRetScoped {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} (L : Lay D)
    (layout : FrameLayout) (ens : List II × Nat) (d : Nat)
    (e : ErgExpr D Γ Λ V.erg) (reserved : Nat := 0) : Option (List II × Nat) := do
  let ce ← lowErg (reserved := reserved) L e d
  pure (ce.1 ++ retC layout d ens.1, max ce.2 (max ens.2 (retTop layout)))

/-- A scoped reason return emits the ordinary reason code; the release of the
    scopes is ghost (`RueckgabeScoped`). -/
def lowRetWhyScoped (layout : FrameLayout) {V : Vertrag D} (r : Fin V.gruende)
    (d : Nat) : Option (List II × Nat) :=
  some (retWhyC layout r.val, max d (retTop layout))

/-- Receive the entire shared return area. Its unused padding is copied as raw
    frame words; only a complete normal value or reason is interpreted by the
    selected continuation. The following status word is outside this footprint. -/
def receiveC (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (F : Nat) : List II :=
  copyWords (returnWords signature.erg signature.gruende) F (F + FB + contextWords signature.params)

def receiveTop (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (F : Nat) : Nat :=
  F + FB + contextWords signature.params + returnWords signature.erg signature.gruende + 1

/-- Both return channels use the same complete received area. Zero status takes
    the reason arm; normal fallthrough skips it after the success continuation. -/
def elseC (signature : Signatur D.Tab D.Glob D.Lock D.Marke) (s : Nat) (cc cr ce : List II) : List II :=
  cc ++ receiveC signature s ++
    [ci 19 (s + FB + contextWords signature.params + returnWords signature.erg signature.gruende) (16 * (cr.length + 2)) 0] ++
    cr ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce

def elseTop (f : D.Fn) (s ta tr te : Nat) : Nat :=
  max (callTop f s ta) (max (s + FB + (contextWords (D.params f)) + returnWords (D.erg f) (D.gruende f) + 1) (max tr te))

/-- The targets of `leave` and `next` as byte offsets from the end of a piece of code; a piece followed by `n`
    instructions sees them `16 n` further. -/
def exPlus (ex : Int × Int) (n : Nat) : Int × Int := (ex.1 + 16 * n, ex.2 + 16 * n)

/-- Keep small counts as one instruction; materialize larger counts as full words. -/
def travCountC (d : Nat) (n : Int) : List II :=
  if lit32 n then [ci 1 d n 0] else (konstWL 4 (BitVec.ofInt 64 n).toNat d).1

/-- Instruction count used by every traversal target, independent of frame placement. -/
def travCountSize (n : Int) : Nat := if lit32 n then 1 else 17

/-- The code of `traverse` (`PLAN-SELF-HOSTING.md` §2.1.4), the counter `k` in slot `s` (the index's own slot, which
    the body may not write), the invariant's code `ci'` into slot `s + 1`, the body's code `cb`:

    `k := 0`; head: the invariant, false: the stop 104; `k < n`, false: the end; the body (its `leave` to the leave
    part, its `next` and its end to the next part); next part: `k := k + 1`, back to the head; leave part: the
    invariant, false: the stop, true: the end; the stop; the end. -/
def travCode (s : Nat) (n : Int) (ci' cb : List II) : List II :=
  [ci 1 s 0 0] ++ (ci' ++
    (([ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0, ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0]) ++ (cb ++
    ([ci 1 (s + 1) 1 0, ci 3 s s (s + 1), ci 18 (-(16 * (6 + travCountSize n + ci'.length + cb.length))) 0 0] ++ (ci' ++
    ([ci 19 ((s + 1 : Nat) : Int) 32 0, ci 18 64 0 0] ++ stopC 104 (s + 1)))))))

def travC (s : Nat) (n : Int) (ci' cb : List II × Nat) : Option (List II × Nat) :=
  if 16 * (9 + travCountSize n + ci'.1.length + cb.1.length) < 2 ^ 31 then
    some (travCode s n ci'.1 cb.1, max ci'.2 (max cb.2 (s + 9)))
  else none

/-- The code of `exchange` (`PLAN-SELF-HOSTING.md` §2.1.6): the old word of the global at `ga` into slot `s` (the new
    variable's), the new value `cn` into `s + 1`, `cas` of the global from `s` to `s + 1`; when another thread changed
    it in between (the old word read back differs): again from the start. -/
def exC (s ga : Nat) (cn : List II) : List II :=
  [ci 1 s ga 0, ci 15 s s 0] ++ cn ++
  [ci 1 ((s + 2 : Nat) : Int) ga 0, ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s,
   ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s, ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0]

/-- `st (s+1) s`: the word of slot `s` to the address in slot `s + 1`. -/
def stC (s : Nat) : II := ci 16 ((s + 1 : Nat) : Int) s 0

/-- Test the low byte of the packed sum in `s` against arm `k`, preserving `s`. -/
def tagTestC (s k : Nat) : List II :=
  [ci 2 (s + 1) s 0, ci 1 (s + 2) 255 0, ci 8 (s + 1) (s + 1) (s + 2),
   ci 1 (s + 2) k 0, ci 14 (s + 1) (s + 1) (s + 2)]

/-- Decode a one-word payload in its binding slot, materialising the lower bound in two scratch words. -/
def tagPayloadC (s : Nat) : Option Ty → Option (List II)
  | none => some []
  | some (.int lo hi) => if decide (valueWords (.int lo hi) = 1) then
      some ([ci 1 (s + 1) 8 0, ci 12 s s (s + 1)] ++ (wordConstant (s + 1) lo).1 ++ [ci 3 s s (s + 1)])
    else none
  | some _ => none


/-- Include each endpoint separately, so even an empty target interval has a
    representable comparison; an empty interval always selects the error arm. -/
def narrowWords (lo hi low high : Int) : Nat :=
  max (engWords lo hi low high) (max (signedWords low low) (signedWords high high))

/-- The comparison kernel's actual scratch extent, also covering the retained value. -/
def narrowTop (d : Nat) (lo hi low high : Int) : Nat :=
  d + 5 * narrowWords lo hi low high + 22

/-- The flag is outside the retained limbs. The success arm starts with the
    target type's complete integer encoding already in its binding span. -/
def narrowC (d : Nat) (lo hi low high : Int) (ce cx cr : List II) : List II :=
  ce ++ wideExtendC (extSigned lo) (integerWords lo hi) (narrowWords lo hi low high) d ++
    wideOutC (narrowWords lo hi low high) d low high ++
    ([ci 19 (d + narrowWords lo hi low high + 3) (16 * (cx.length + 2)) 0] ++ cx ++
      [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr)

theorem narrowWords_source (lo hi low high : Int) :
    signedWords lo hi ≤ narrowWords lo hi low high :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

theorem narrowWords_target (lo hi low high : Int) :
    signedWords low high ≤ narrowWords lo hi low high :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem narrowWords_low (lo hi low high : Int) :
    signedWords low low ≤ narrowWords lo hi low high :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem narrowWords_high (lo hi low high : Int) :
    signedWords high high ≤ narrowWords lo hi low high :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem narrowC_length (d : Nat) (lo hi low high : Int) (ce cx cr : List II) :
    (narrowC d lo hi low high ce cx cr).length =
      ce.length + (wideExtendC (extSigned lo) (integerWords lo hi)
        (narrowWords lo hi low high) d).length +
      (wideOutC (narrowWords lo hi low high) d low high).length + 1 + cx.length + 1 + cr.length := by
  simp only [narrowC, List.length_append, List.length_singleton]
  omega

/-- Compare a reason's entire word, preserving its slot for subsequent arms. -/
def whyTestC (s k : Nat) : List II :=
  [ci 2 (s + 1) s 0, ci 1 (s + 2) k 0, ci 14 (s + 1) (s + 1) (s + 2)]

/-- Check the range first; the selected success arm then binds the unchanged raw value. -/
def floatNarrowC (d : Nat) (cc cx ce cr : List II) : List II :=
  cc ++ [ci 19 d (16 * (cx.length + 2)) 0] ++ cx ++
    [ci 18 (16 * (ce.length + cr.length + 1)) 0 0] ++ (ce ++ cr)

end Gabbro.Stage0.Senke
