/-
  File:      stage0/Stage0/Senke/Anweisung.lean
  Subject:   The lowering of stage 0, part 2: statements and blocks of machine G into `S0IR`.

  The first free slot of a context `Γ` is `frei Γ`: an expression of a statement is computed there; a `bind`
  computes its value there, which is then the new variable's slot. `assignVar x e` moves the value into `x`'s slot;
  `ite c t e` tests `c` with `brz` and jumps over the other branch; a call (`call`, `bindCall`) places the
  callee's frame at the first free slot (`callC`). `lo` is the lowest slot an assignment may write (a function's
  body keeps its parameters for `ensures`); `A f` is the code address of `f`; `ens` the function's `ensures` code, which
  a `ret` runs (`retC`). Accepted so far: `assignVar`, `ite`, `onTag`, `onWhy`, `onOption` (the index word kept for the bound variable), `call`, `callInd`, `ret`, `retWhy`, the writes `assignGlob`, `assignSlot`, `assignThru`, `putBytes` (zero through eight bytes, operands captured once), the checked state transition `shift` (failed prestate: stop 106), `leave` and `next` (a jump to their target), `traverse` (`travC`), `breaking` (its block), `advances` and `retires` (no code: G only marks them), the gates `axiomCall` and `bindAxiom` (`torC`), `publish` (a store, release under TSO), `locks` without `ret` in its body (`locksCode`: take, the body,
  give on every way out), and the blocks `nil`, `cons`, `bind`, `floatLit` (kernel-rounded binary64 bits), `floatNarrow` (inclusive range with its fallback), `bindCall`, `bindCallElse`, `bindCallInd`, `awaits` (a load) and `exchange` (`exC`, a `cas` loop); everything else is refused (`none`). The answer's
  number is an upper bound of the slots the code writes. End blocks also lower `retWhy`, `bindCallElse`,
  `leave` and `next`; the latter two retain the enclosing loop targets.
-/
import Stage0.Senke.Ausdruck
import Stage0.Senke.Stopp
import Stage0.Senke.Tor
import Stage0.Senke.Sperre.Code
import Stage0.Senke.Anweisung.Bytes.Code
import Stage0.Senke.Anweisung.Faelle.Schleifen.Allocation

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
    let ce ← lowE L e (p + τs.length) reserved
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
  callTailN (D.params f).length (A f) F indirect

def callC (A : D.Fn → Nat) (f : D.Fn) (F : Nat) (ca : List II) : List II := ca ++ callTail A f F

def callTop (f : D.Fn) (F t : Nat) : Nat := max t (F + FB + (D.params f).length + 1)

/-- The pointer is evaluated before the arguments, into the future callee's return-pc slot.
    Argument evaluation and the depth calculation preserve it until the call loads its target. -/
def indC (n F : Nat) (cp ca : List II) : List II := cp ++ (ca ++ callTailN (D.sigNr n).params.length 0 F true)

def indTop (n F tp ta : Nat) : Nat := max tp (max ta (F + FB + (D.sigNr n).params.length + 1))

def lowInd (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (reserved : Nat := 0) : Option (List II × Nat) := do
  if (D.sigNr n).gruende = 0 then do
    let cp ← lowE (reserved := reserved) L p ((frei Γ reserved))
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    pure (indC (D := D) n ((frei Γ reserved)) cp.1 ca.1, indTop (D := D) n ((frei Γ reserved)) cp.2 ca.2)
  else none

def lowErg (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → ErgExpr D Γ Λ e → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, .empty, d, reserved => some ([], d + 1)
  | _, .val e, d, reserved => lowE (reserved := reserved) L e d

/-- A call binds either word into the same slot. Zero status takes the reason arm;
    normal fallthrough skips that arm after the success continuation. -/
def elseC (flag s : Nat) (cc cr ce : List II) : List II :=
  cc ++ [ci 2 s (s + 2) 0] ++ [ci 19 flag (16 * (cr.length + 2)) 0] ++
    cr ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce

def elseTop (f : D.Fn) (s ta tr te : Nat) : Nat :=
  max (callTop f s ta) (max (s + FB + (D.params f).length + 2) (max tr te))

/-- `ret`: the result from slot `r` into slot `q` (`FB + np`, the slot of `ensures`' result variable), the
    `ensures` code `ens`, the check, slot 2, back. The successful ensures word
    in `q + 1` is the normal return flag and is preserved by the return tail. -/
def retC (q r : Nat) (ens : List II) : List II :=
  [ci 2 q r 0] ++ ens ++ [ci 19 ((q + 1 : Nat) : Int) 48 0, ci 2 2 q 0, ci 21 0 0 0] ++ stopC 102 (q + 1)

/-- A reason bypasses ensures, as in G. Slot 2 carries the ordinal; the ensures
    result slot carries zero, distinguishing it from every successful normal return. -/
def retWhyC (q r : Nat) : List II :=
  [ci 1 2 r 0, ci 1 (q + 1) 0 0, ci 21 0 0 0]

def retTop (q : Nat) : Nat := q + 1 + 8

/-- The targets of `leave` and `next` as byte offsets from the end of a piece of code; a piece followed by `n`
    instructions sees them `16 n` further. -/
def exPlus (ex : Int × Int) (n : Nat) : Int × Int := (ex.1 + 16 * n, ex.2 + 16 * n)

/-- The code of `traverse` (`PLAN-SELF-HOSTING.md` §2.1.4), the counter `k` in slot `s` (the index's own slot, which
    the body may not write), the invariant's code `ci'` into slot `s + 1`, the body's code `cb`:

    `k := 0`; head: the invariant, false: the stop 104; `k < n`, false: the end; the body (its `leave` to the leave
    part, its `next` and its end to the next part); next part: `k := k + 1`, back to the head; leave part: the
    invariant, false: the stop, true: the end; the stop; the end. -/
def travCode (s : Nat) (n : Int) (ci' cb : List II) : List II :=
  [ci 1 s 0 0] ++ (ci' ++
    ([ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0, ci 2 ((s + 1 : Nat) : Int) s 0,
      ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ (cb ++
    ([ci 1 (s + 1) 1 0, ci 3 s s (s + 1), ci 18 (-(16 * (7 + ci'.length + cb.length))) 0 0] ++ (ci' ++
    ([ci 19 ((s + 1 : Nat) : Int) 32 0, ci 18 64 0 0] ++ stopC 104 (s + 1)))))))

def travC (s : Nat) (n : Int) (ci' cb : List II × Nat) : Option (List II × Nat) :=
  if 16 * (10 + ci'.1.length + cb.1.length) < 2 ^ 31 then
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

/-- Decode a payload in its binding slot. Its lower bound must currently fit a literal. -/
def tagPayloadC (s : Nat) : Option (Int × Int) → Option (List II)
  | none => some []
  | some (lo, _) => if lit32 lo then
      some [ci 1 (s + 1) 8 0, ci 12 s s (s + 1), ci 1 (s + 1) lo 0, ci 3 s s (s + 1)]
    else none

/-- An outside flag selects the terminating error arm; the value stays in `d`. -/
def narrowC (d : Nat) (lo hi : Int) (ce cx cr : List II) : List II :=
  ce ++ (engTest d lo hi ++ [ci 19 (d + 1) (16 * (cx.length + 2)) 0] ++ cx ++
    [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr)

/-- Compare a reason's entire word, preserving its slot for subsequent arms. -/
def whyTestC (s k : Nat) : List II :=
  [ci 2 (s + 1) s 0, ci 1 (s + 2) k 0, ci 14 (s + 1) (s + 1) (s + 2)]

/-- Check the range first; the selected success arm then binds the unchanged raw value. -/
def floatNarrowC (d : Nat) (cc cx ce cr : List II) : List II :=
  cc ++ [ci 19 d (16 * (cx.length + 2)) 0] ++ cx ++
    [ci 18 (16 * (ce.length + cr.length + 1)) 0 0] ++ (ce ++ cr)

mutual
def lowS (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, .assignVar x e, reserved =>
    if lo ≤ (vslot x reserved) ∧ (vslot x reserved) ∉ pr then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      pure (ce.1 ++ [ci 2 ((vslot x reserved)) ((frei Γ reserved)) 0], ce.2)
    else none
  | _, Γ, _, _, .ite c t e, reserved => do
    let cc ← lowE (reserved := reserved) L c ((frei Γ reserved))
    let ce ← lowB (reserved := reserved) passes A L lo ens pr ex e
    let ct ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.1.length + 1)) t
    pure (cc.1 ++ [ci 19 ((frei Γ reserved)) (16 * (ct.1.length + 2)) 0] ++ ct.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1,
      max cc.2 (max ct.2 ce.2))
  | _, Γ, _, _, .onOption (n := n) o p a, reserved =>
    if decide (n ≤ 2 ^ 63) then do
      let co ← lowE (reserved := reserved) L o ((frei Γ reserved))
      let ca ← lowB (reserved := reserved) passes A L lo ens pr ex a
      let cp ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (ca.1.length + 1)) p
      pure (co.1 ++ [ci 1 ((frei Γ reserved) + 1) (-1) 0, ci 10 ((frei Γ reserved) + 1) ((frei Γ reserved)) ((frei Γ reserved) + 1)] ++
        [ci 19 ((frei Γ reserved) + 1) (16 * (cp.1.length + 2)) 0] ++ cp.1 ++
        [ci 18 (16 * (ca.1.length + 1)) 0 0] ++ ca.1,
        max co.2 (max ((frei Γ reserved) + 2) (max cp.2 ca.2)))
    else none
  | _, _, _, _, .callInd p args _ _, reserved => lowInd (reserved := reserved) L p args
  | _, Γ, _, _, .onTag (cs := cs) v arms, reserved =>
    if sumFits cs then do
      let cv ← lowE (reserved := reserved) L v ((frei Γ reserved))
      let ca ← lowTags (reserved := reserved) passes A L lo ens pr ex arms 0
      pure (cv.1 ++ ca.1, max cv.2 ca.2)
    else none
  | _, Γ, _, _, .onWhy (n := n) r arms, reserved =>
    if n < 2 ^ 31 then do
      let cv ← lowE (reserved := reserved) L r ((frei Γ reserved))
      let ca ← lowGrund (reserved := reserved) passes A L lo ens pr ex arms 0
      pure (cv.1 ++ ca.1, max cv.2 ca.2)
    else none
  | _, Γ, _, _, .call f args _ _, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    pure (callC A f ((frei Γ reserved)) ca.1, callTop f ((frei Γ reserved)) ca.2)
  | _, Γ, _, _, .retWhy r _, reserved =>
    if r.val < 2 ^ 31 then some (retWhyC lo r.val, max ((frei Γ reserved)) (retTop lo)) else none
  | _, Γ, _, _, .ret e _, reserved => do
    let ce ← lowErg (reserved := reserved) L e ((frei Γ reserved))
    pure (ce.1 ++ retC lo ((frei Γ reserved)) ens.1, max ce.2 (max ens.2 (retTop lo)))
  | _, Γ, _, _, .assignGlob g e _ _, reserved =>
    if lit32 (L.ga g) then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      pure (ce.1 ++ [ci 1 (((frei Γ reserved) + 1 : Nat) : Int) (L.ga g) 0] ++ [stC ((frei Γ reserved))], max ce.2 ((frei Γ reserved) + 2))
    else none
  | _, Γ, _, _, .publish g e _ _ _ _, reserved =>
    if lit32 (L.ga g) then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      pure (ce.1 ++ [ci 1 (((frei Γ reserved) + 1 : Nat) : Int) (L.ga g) 0] ++ [stC ((frei Γ reserved))], max ce.2 ((frei Γ reserved) + 2))
    else none
  | _, Γ, _, _, .assignSlot t f i e _ _, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let ci' ← lowE (reserved := reserved) L i ((frei Γ reserved) + 1)
    let ca ← slotA L t f ((frei Γ reserved) + 1) ci'
    pure (ce.1 ++ ca.1 ++ [stC ((frei Γ reserved))], max ce.2 ca.2)
  | _, Γ, _, _, .assignThru _ t _ f i e _ _, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let ci' ← lowE (reserved := reserved) L i ((frei Γ reserved) + 1)
    let ca ← slotA L t f ((frei Γ reserved) + 1) ci'
    pure (ce.1 ++ ca.1 ++ [stC ((frei Γ reserved))], max ce.2 ca.2)
  | _, Γ, Λ, _, .putBytes t f _ n i hlo hhi e _ _, reserved =>
    if n ≤ 8 then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let ci' ← lowE (reserved := reserved) L i ((frei Γ reserved) + 1)
      let cb ← putBytesL L (Γ := Γ) (Λ := Λ) t f _ _ (256 ^ n - 1) hlo reserved n 0 (by simpa using hhi)
      pure (ce.1 ++ ci'.1 ++ cb.1, max ce.2 (max ci'.2 cb.2))
    else none
  | _, Γ, _, _, .assignSlotRef r t _ _ f e _ _, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let cr ← lowE (reserved := reserved) L r ((frei Γ reserved) + 1)
    let ca ← slotA L t f ((frei Γ reserved) + 1) cr
    pure (ce.1 ++ ca.1 ++ [stC ((frei Γ reserved))], max ce.2 ca.2)
  | _, Γ, _, _, .shift t f (lo := a) (hi := b) _ i von nach _ _ _ _, reserved =>
    if inW a b && lit32 von && lit32 nach then do
      let ci' ← lowE (reserved := reserved) L i ((frei Γ reserved))
      let cr ← slotC L t f ((frei Γ reserved)) ci'
      let cj ← lowE (reserved := reserved) L i ((frei Γ reserved) + 1)
      let ca ← slotA L t f ((frei Γ reserved) + 1) cj
      let test := bin2 14 ((frei Γ reserved)) cr ([ci 1 ((frei Γ reserved) + 1) von 0], (frei Γ reserved) + 2)
      pure (test.1 ++ (guardC ((frei Γ reserved)) 106 ((frei Γ reserved)) ++
        ([ci 1 ((frei Γ reserved)) nach 0] ++ ca.1 ++ [stC ((frei Γ reserved))])),
        max test.2 (max ca.2 ((frei Γ reserved) + 8)))
    else none
  | _, Γ, _, _, .traverse t inv body, reserved =>
    if lit32 (D.count t) then do
      let ci' ← lowE (reserved := reserved) L inv ((frei Γ reserved) + 1)
      let cb ← lowB (reserved := reserved) passes A L lo ens ((frei Γ reserved) :: pr) (48, 0) body
      travC ((frei Γ reserved)) (D.count t) ci' cb
    else none
  | _, Γ, _, _, .retry n bis body overflow, reserved => do
    let cc ← lowE (reserved := reserved) L bis ((frei Γ reserved))
    let cu ← lowB (reserved := reserved) passes A L lo ens pr ex overflow
    retryC ((frei Γ reserved)) cc cu (fun targets => lowB (reserved := reserved) passes A L lo ens pr targets body) n
  | _, Γ, _, _, .forever _ inv body, reserved =>
    let pair := counterPair reserved (counterDepthB body)
    if lo ≤ pair.1 ∧ pair.2 < FB + reserved ∧ pair.1 ∉ pr ∧ pair.2 ∉ pr then do
      let cc ← lowE (reserved := reserved) L inv (frei Γ reserved)
      foreverC pair.1 pair.2 (frei Γ reserved) passes cc
        (fun targets => lowB (reserved := reserved) passes A L lo ens
          (pair.1 :: pair.2 :: pr) targets body)
    else none
  | _, _, _, _, .breaking _ body, reserved => lowB (reserved := reserved) passes A L lo ens pr ex body
  | _, Γ, _, _, .advances .., reserved => some ([], (frei Γ reserved))
  | _, Γ, _, _, .retires .., reserved => some ([], (frei Γ reserved))
  | _, Γ, _, _, .leave _, reserved => if lit32 (16 + ex.1) then some ([ci 18 (16 + ex.1) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, _, .next _, reserved => if lit32 (16 + ex.2) then some ([ci 18 (16 + ex.2) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, _, .axiomCall a args _ _ _ _ _, reserved => torC0 (reserved := reserved) L a args ((frei Γ reserved))
  | _, Γ, _, _, .locks Lk _ body, reserved =>
    if retFreiB body = true ∧ lit32 (16 + ex.1 + 16 * 30) = true ∧ lit32 (16 + ex.2) = true then do
      let cb ← lowB (reserved := reserved) passes A L lo ens pr (16 * 30, 16 * 60) body
      pure (locksCode L (L.lk Lk) ((frei Γ reserved)) cb.1 ex.1 ex.2, max (cb.2 + 1) ((frei Γ reserved) + 18))
    else none
  | _, _, _, _, _, reserved => none

def lowB (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, .nil, reserved => some ([], (frei Γ reserved))
  | _, _, _, _, .cons s rest, reserved => do
    let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
    let cs ← lowS (reserved := reserved) passes A L lo ens pr (exPlus ex cr.1.length) s
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, _, .bind e rest, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, _, .bindCallElse f args _ _ _ err rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let ce ← lowEnd (reserved := reserved) passes A L lo ens pr ex err
    let cr ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.1.length + 1)) rest
    pure (elseC ((frei Γ reserved) + FB + (D.params f).length + 1) ((frei Γ reserved)) (callC A f ((frei Γ reserved)) ca.1) cr.1 ce.1,
      elseTop f ((frei Γ reserved)) ca.2 cr.2 ce.2)
  | _, Γ, _, _, .floatNarrow e low high err rest, reserved =>
    if decide (Gleitkomma.klasse Gleitkomma.f64 (bruch low) ≠ .nan) &&
        decide (Gleitkomma.klasse Gleitkomma.f64 (bruch high) ≠ .nan) then do
      let cc ← floatRangeL ((frei Γ reserved)) low high (lowE (reserved := reserved) L e)
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
      let cx ← lowEnd (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.1.length + cr.1.length + 1)) err
      pure (floatNarrowC ((frei Γ reserved)) cc.1 cx.1 ce.1 cr.1, max cc.2 (max ce.2 (max cr.2 cx.2)))
    else lowEnd (reserved := reserved) passes A L lo ens pr ex err
  | _, Γ, _, _, .floatLit q low high rest, reserved =>
    floatLiteralL ((frei Γ reserved)) q low high (fun _ => lowB (reserved := reserved) passes A L lo ens pr ex rest)
  | _, Γ, _, _, .floatOf e low high rest, reserved =>
    match e with
    | .lit n => floatLiteralL ((frei Γ reserved)) (n, 1) low high (fun _ => lowB (reserved := reserved) passes A L lo ens pr ex rest)
    | _ => none
  | _, Γ, _, _, .bindCall f args _ _ _ rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
    pure (callC A f ((frei Γ reserved)) ca.1 ++ [ci 2 ((frei Γ reserved)) ((frei Γ reserved) + 2) 0] ++ cr.1, max (callTop f ((frei Γ reserved)) ca.2) cr.2)
  | _, Γ, _, _, .bindCallInd p args _ _ _ rest, reserved => do
    let cc ← lowInd (reserved := reserved) L p args
    let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
    pure (cc.1 ++ [ci 2 ((frei Γ reserved)) ((frei Γ reserved) + 2) 0] ++ cr.1, max cc.2 cr.2)
  | _, Γ, _, _, .narrow (lo := lo') (hi := hi') e low high err rest, reserved =>
    if inW lo' hi' && lit32 low && lit32 high then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
      let cx ← lowEnd (reserved := reserved) passes A L lo ens pr (exPlus ex (cr.1.length + 1)) err
      pure (narrowC ((frei Γ reserved)) low high ce.1 cx.1 cr.1, max ce.2 (max ((frei Γ reserved) + 3) (max cx.2 cr.2)))
    else none
  | _, Γ, _, _, .bindAxiom a args _ _ _ _ _ rest, reserved => do
    let ct ← torC0 (reserved := reserved) L a args ((frei Γ reserved))
    let ck ← chkC (D.aerg a) ((frei Γ reserved))
    let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max ((frei Γ reserved) + 10) cr.2))
  | _, Γ, _, _, .bindAxiomElse a args _ _ _ _ _ _ err rest, reserved =>
    match L.tor a, D.aerg a with
    | some b, some (.int lo' hi') =>
      if fehlGut (D.agruende a) b.fehler = true ∧ 0 ≤ lo' ∧ 0 < D.agruende a then do
        let ct ← torC (reserved := reserved) L a args ((frei Γ reserved))
        let ck ← chkC (some (.int lo' hi')) ((frei Γ reserved))
        let ce ← lowEnd (reserved := reserved) passes A L lo ens pr ex err
        let cr ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.1.length + 1)) rest
        if 16 + 16 * (6 * b.fehler.length) + 16 * (ck.length + (cr.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0]).length) < 2 ^ 31 then
          pure (ct.1 ++ fehlC ((frei Γ reserved)) b.fehler ((16 * (ck.length + (cr.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0]).length) : Nat) : Int) ++ ck ++ (cr.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0]) ++ ce.1,
            max ct.2 (max ((frei Γ reserved) + 10) (max cr.2 ce.2)))
        else none
      else none
    | _, _ => none
  | _, Γ, _, _, .check c err rest, reserved => do
    let cc ← lowE (reserved := reserved) L c ((frei Γ reserved))
    let ce ← lowEnd (reserved := reserved) passes A L lo ens pr ex err
    let cr ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.1.length + 1)) rest
    pure (cc.1 ++ [ci 19 ((frei Γ reserved)) (16 * (cr.1.length + 2)) 0] ++ cr.1 ++
      [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1, max cc.2 (max cr.2 ce.2))
  | _, Γ, _, _, .awaits g _ _ _ _ rest, reserved =>
    if lit32 (L.ga g) then do
      let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
      pure ([ci 1 ((frei Γ reserved)) (L.ga g) 0, ci 15 ((frei Γ reserved)) ((frei Γ reserved)) 0] ++ cr.1, max ((frei Γ reserved) + 1) cr.2)
    else none
  | _, Γ, _, _, .exchange g neu _ _ rest, reserved =>
    if lit32 (L.ga g) then do
      let cn ← lowE (reserved := reserved) L neu ((frei Γ reserved) + 1)
      let cr ← lowB (reserved := reserved) passes A L lo ens pr ex rest
      if 16 * (cn.1.length + 5) < 2 ^ 31 then
        pure (exC ((frei Γ reserved)) (L.ga g) cn.1 ++ cr.1, max (max cn.2 ((frei Γ reserved) + 4)) cr.2)
      else none
    else none
  -- Rounded integer conversion and IEEE arithmetic need their software algorithms and proofs.
  | _, _, _, _, .float .., reserved => none
  | _, _, _, _, _, reserved => none

/-- Dispatch in declaration order. Each branch jumps over the remaining arms; loop exits
    are measured from the end of the entire dispatch. The empty case is unreachable. -/
def lowTags (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option (Int × Int))} →
    Arms D V l Γ Λ Λ' cs → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, _, .nil, _, reserved => some ([], (frei Γ reserved) + 3)
  | _, Γ, _, _, c :: _, .cons b rest, k, reserved => if k < 256 then do
      let cr ← lowTags (reserved := reserved) passes A L lo ens pr ex rest (k + 1)
      let cp ← tagPayloadC ((frei Γ reserved)) c
      let cb ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (cr.1.length + 1)) b
      pure (tagTestC ((frei Γ reserved)) k ++ [ci 19 ((frei Γ reserved) + 1) (16 * (cp.length + cb.1.length + 2)) 0] ++
        cp ++ cb.1 ++ [ci 18 (16 * (cr.1.length + 1)) 0 0] ++ cr.1,
        max ((frei Γ reserved) + 3) (max cb.2 cr.2))
    else none

/-- Reason dispatch uses full word comparisons in declaration order. -/
def lowGrund (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    GrundArms D V l Γ Λ Λ' n → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, _, .nil, _, reserved => some ([], (frei Γ reserved) + 3)
  | _, Γ, _, _, _, .cons b rest, k, reserved => if k < 2 ^ 31 then do
      let cr ← lowGrund (reserved := reserved) passes A L lo ens pr ex rest (k + 1)
      let cb ← lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (cr.1.length + 1)) b
      pure (whyTestC ((frei Γ reserved)) k ++ [ci 19 ((frei Γ reserved) + 1) (16 * (cb.1.length + 2)) 0] ++
        cb.1 ++ [ci 18 (16 * (cr.1.length + 1)) 0 0] ++ cr.1,
        max ((frei Γ reserved) + 3) (max cb.2 cr.2))
    else none

def lowEnd (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, .leave _, reserved => if lit32 (16 + ex.1) then some ([ci 18 (16 + ex.1) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, .next _, reserved => if lit32 (16 + ex.2) then some ([ci 18 (16 + ex.2) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, .retWhy r _, reserved =>
    if r.val < 2 ^ 31 then some (retWhyC lo r.val, max ((frei Γ reserved)) (retTop lo)) else none
  | _, Γ, _, .ret e _, reserved => do
    let ce ← lowErg (reserved := reserved) L e ((frei Γ reserved))
    pure (ce.1 ++ retC lo ((frei Γ reserved)) ens.1, max ce.2 (max ens.2 (retTop lo)))
  | _, _, _, .cons s rest, reserved => do
    let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
    let cs ← lowS (reserved := reserved) passes A L lo ens pr (exPlus ex cr.1.length) s
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, .bind e rest, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, .bindCallElse f args _ _ _ err rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let ce ← lowEnd (reserved := reserved) passes A L lo ens pr ex err
    let cr ← lowEnd (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.1.length + 1)) rest
    pure (elseC ((frei Γ reserved) + FB + (D.params f).length + 1) ((frei Γ reserved)) (callC A f ((frei Γ reserved)) ca.1) cr.1 ce.1,
      elseTop f ((frei Γ reserved)) ca.2 cr.2 ce.2)
  | _, Γ, _, .bindCall f args _ _ _ rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
    pure (callC A f ((frei Γ reserved)) ca.1 ++ [ci 2 ((frei Γ reserved)) ((frei Γ reserved) + 2) 0] ++ cr.1, max (callTop f ((frei Γ reserved)) ca.2) cr.2)
  | _, Γ, _, .bindCallInd p args _ _ _ rest, reserved => do
    let cc ← lowInd (reserved := reserved) L p args
    let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
    pure (cc.1 ++ [ci 2 ((frei Γ reserved)) ((frei Γ reserved) + 2) 0] ++ cr.1, max cc.2 cr.2)
  | _, Γ, _, .ite c t e, reserved => do
    let cc ← lowE (reserved := reserved) L c ((frei Γ reserved))
    let ce ← lowEnd (reserved := reserved) passes A L lo ens pr ex e
    let ct ← lowEnd (reserved := reserved) passes A L lo ens pr (exPlus ex ce.1.length) t
    pure (cc.1 ++ [ci 19 ((frei Γ reserved)) (16 * (ct.1.length + 1)) 0] ++ ct.1 ++ ce.1, max cc.2 (max ct.2 ce.2))
  | _, Γ, _, .narrow (lo := lo') (hi := hi') e low high err rest, reserved =>
    if inW lo' hi' && lit32 low && lit32 high then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
      let cx ← lowEnd (reserved := reserved) passes A L lo ens pr (exPlus ex (cr.1.length + 1)) err
      pure (narrowC ((frei Γ reserved)) low high ce.1 cx.1 cr.1, max ce.2 (max ((frei Γ reserved) + 3) (max cx.2 cr.2)))
    else none
  | _, Γ, _, .bindAxiom a args _ _ _ _ _ rest, reserved => do
    let ct ← torC0 (reserved := reserved) L a args ((frei Γ reserved))
    let ck ← chkC (D.aerg a) ((frei Γ reserved))
    let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max ((frei Γ reserved) + 10) cr.2))
  | _, Γ, _, .awaits g _ _ _ _ rest, reserved =>
    if lit32 (L.ga g) then do
      let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
      pure ([ci 1 ((frei Γ reserved)) (L.ga g) 0, ci 15 ((frei Γ reserved)) ((frei Γ reserved)) 0] ++ cr.1, max ((frei Γ reserved) + 1) cr.2)
    else none
  | _, Γ, _, .exchange g neu _ _ rest, reserved =>
    if lit32 (L.ga g) then do
      let cn ← lowE (reserved := reserved) L neu ((frei Γ reserved) + 1)
      let cr ← lowEnd (reserved := reserved) passes A L lo ens pr ex rest
      if 16 * (cn.1.length + 5) < 2 ^ 31 then
        pure (exC ((frei Γ reserved)) (L.ga g) cn.1 ++ cr.1, max (max cn.2 ((frei Γ reserved) + 4)) cr.2)
      else none
    else none
  | _, Γ, _, .bindAxiomElse a args _ _ _ _ _ _ err rest, reserved =>
    match L.tor a, D.aerg a with
    | some b, some (.int lo' hi') =>
      if fehlGut (D.agruende a) b.fehler = true ∧ 0 ≤ lo' ∧ 0 < D.agruende a then do
        let ct ← torC (reserved := reserved) L a args ((frei Γ reserved))
        let ck ← chkC (some (.int lo' hi')) ((frei Γ reserved))
        let ce ← lowEnd (reserved := reserved) passes A L lo ens pr ex err
        let cr ← lowEnd (reserved := reserved) passes A L lo ens pr (exPlus ex ce.1.length) rest
        if 16 + 16 * (6 * b.fehler.length) + 16 * (ck.length + cr.1.length) < 2 ^ 31 then
          pure (ct.1 ++ fehlC ((frei Γ reserved)) b.fehler ((16 * (ck.length + cr.1.length) : Nat) : Int) ++ ck ++ cr.1 ++ ce.1,
            max ct.2 (max ((frei Γ reserved) + 10) (max cr.2 ce.2)))
        else none
      else none
    | _, _ => none
  | _, _, _, _, reserved => none

end

end Gabbro.Stage0.Senke
