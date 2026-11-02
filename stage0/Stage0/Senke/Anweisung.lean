/-
  File:      stage0/Stage0/Senke/Anweisung.lean
  Subject:   The lowering of stage 0, part 2: statements and blocks of machine G into `S0IR`.

  The first free slot of a context `Γ` is `frei Γ`: an expression of a statement is computed there; a `bind`
  computes its value there, which is then the new variable's slot. `assignVar x e` moves the value into `x`'s slot;
  `ite c t e` tests `c` with `brz` and jumps over the other branch; a call (`call`, `bindCall`) places the
  callee's frame at the first free slot (`callC`). `layout.internalResult` is the lowest slot an assignment may write (a function's
  body keeps its parameters for `ensures`); `A f` is the code address of `f`; `ens` the shared ensures/invariant epilogue, which
  a `ret` runs (`retC`). Accepted so far: `assignVar`, `ite`, `onTag`, `onWhy`, `onOption` (the index word kept for the bound variable), `call`, `callInd`, `ret`, `retWhy`, the writes `assignGlob`, `assignSlot`, `assignThru`, `putBytes` (zero through eight bytes, operands captured once), the checked state transition `shift` (failed prestate: stop 106), `leave` and `next` (a jump to their target), `traverse` (`travC`), `breaking` (its block), `advances` and `retires` (no code: G only marks them), the gates `axiomCall` and `bindAxiom` (`torC`), `publish` (a store, release under TSO), `locks` without `ret` in its body (`locksCode`: take, the body,
  give on every way out), and the blocks `nil`, `cons`, `bind`, `floatLit` (kernel-rounded binary64 bits), `floatOf` (signed-word conversion or arbitrary integer literals), `floatNarrow` (inclusive range with its fallback), `bindCall`, `bindCallElse`, `bindCallInd`, `awaits` (a load) and `exchange` (`exC`, a `cas` loop); everything else is refused (`none`). The answer's
  number is an upper bound of the slots the code writes. End blocks also lower `retWhy`, `bindCallElse`,
  `leave` and `next`; the latter two retain the enclosing loop targets.
-/
module
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotContext
public import Stage0.Senke.Ausdruck.Gleit.Bereich
public import Stage0.Senke.Stopp
public import Stage0.Senke.Tor
public import Stage0.Senke.Sperre.Code
public import Stage0.Senke.Anweisung.Bytes.Code
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Allocation
public import Stage0.Senke.Anweisung.Faelle.Hilfen
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

mutual
def lowS (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, .assignVar (τ := τ) x e, reserved =>
    if layout.internalResult ≤ (vslot x reserved) ∧ pr.all (fun j => decide (j < vslot x reserved ∨ vslot x reserved + valueWords τ ≤ j)) then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      pure (ce.1 ++ copyWords (valueWords τ) (vslot x reserved) (frei Γ reserved), max ce.2 (frei Γ reserved + valueWords τ))
    else none
  | _, Γ, _, _, .ite c t e, reserved => do
    let cc ← lowE (reserved := reserved) L c ((frei Γ reserved))
    let ce ← lowB (reserved := reserved) passes A L layout ens pr ex e
    let ct ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (ce.1.length + 1)) t
    pure (cc.1 ++ [ci 19 ((frei Γ reserved)) (16 * (ct.1.length + 2)) 0] ++ ct.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1,
      max cc.2 (max ct.2 ce.2))
  | _, Γ, _, _, .onOption (n := n) o p a, reserved =>
    if decide (n ≤ 2 ^ 63) then do
      let co ← lowE (reserved := reserved) L o ((frei Γ reserved))
      let ca ← lowB (reserved := reserved) passes A L layout ens pr ex a
      let cp ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (ca.1.length + 1)) p
      pure (co.1 ++ [ci 1 ((frei Γ reserved) + 1) (-1) 0, ci 10 ((frei Γ reserved) + 1) ((frei Γ reserved)) ((frei Γ reserved) + 1)] ++
        [ci 19 ((frei Γ reserved) + 1) (16 * (cp.1.length + 2)) 0] ++ cp.1 ++
        [ci 18 (16 * (ca.1.length + 1)) 0 0] ++ ca.1,
        max co.2 (max ((frei Γ reserved) + 2) (max cp.2 ca.2)))
    else none
  | _, _, _, _, .callInd p args _ _, reserved => lowInd (reserved := reserved) L p args
  | _, Γ, _, _, .onTag (cs := cs) v arms, reserved =>
    if sumFits cs then do
      let cv ← lowE (reserved := reserved) L v ((frei Γ reserved))
      let ca ← lowTags (reserved := reserved) passes A L layout ens pr ex arms 0
      pure (cv.1 ++ ca.1, max cv.2 ca.2)
    else none
  | _, Γ, _, _, .onWhy (n := n) r arms, reserved =>
    if n < 2 ^ 31 then do
      let cv ← lowE (reserved := reserved) L r ((frei Γ reserved))
      let ca ← lowGrund (reserved := reserved) passes A L layout ens pr ex arms 0
      pure (cv.1 ++ ca.1, max cv.2 ca.2)
    else none
  | _, Γ, _, _, .call f args _ _, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    pure (callC A f ((frei Γ reserved)) ca.1, callTop f ((frei Γ reserved)) ca.2)
  | _, Γ, _, _, .retWhy r _, reserved =>
    some (retWhyC layout r.val, max ((frei Γ reserved)) (retTop layout))
  | _, Γ, _, _, .ret e _, reserved => do
    let ce ← lowErg (reserved := reserved) L e ((frei Γ reserved))
    pure (ce.1 ++ retC layout ((frei Γ reserved)) ens.1, max ce.2 (max ens.2 (retTop layout)))
  | _, Γ, _, _, .assignGlob g e _ _, reserved => do
      let ce ← lowE (reserved := reserved) L e (frei Γ reserved)
      globalStoreC L g (frei Γ reserved) ce
  | _, Γ, _, _, .publish g e _ _ _ _, reserved =>
    if lit32 (L.ga g) && aggregateFits (D.gtyp g) then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      pure (ce.1 ++ [ci 1 (((frei Γ reserved) + 1 : Nat) : Int) (L.ga g) 0] ++ [stC ((frei Γ reserved))], max ce.2 ((frei Γ reserved) + 2))
    else none
  | _, Γ, _, _, .assignSlot t f i e _ _, reserved => do
    let ce ← lowE (reserved := reserved) L e (frei Γ reserved)
    let ci' ← lowE (reserved := reserved) L i (frei Γ reserved + valueWords (D.typ t f))
    slotStoreC L t f (frei Γ reserved) ce ci'
  | _, Γ, _, _, .assignThru _ t _ f i e _ _, reserved => do
    let ce ← lowE (reserved := reserved) L e (frei Γ reserved)
    let ci' ← lowE (reserved := reserved) L i (frei Γ reserved + valueWords (D.typ t f))
    slotStoreC L t f (frei Γ reserved) ce ci'
  | _, Γ, Λ, _, .putBytes (lo := lo) (hi := hi) t f _ n i hlo hhi e _ _, reserved =>
    if n ≤ 8 then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let ci' ← lowE (reserved := reserved) L i ((frei Γ reserved) + 1)
      let cb ← putBytesL L (Γ := Γ) (Λ := Λ) t f lo hi (256 ^ n - 1) hlo reserved n 0 (by simpa using hhi)
      pure (ce.1 ++ ci'.1 ++ cb.1, max ce.2 (max ci'.2 cb.2))
    else none
  | _, Γ, _, _, .assignSlotRef r t _ _ f e _ _, reserved => do
    let ce ← lowE (reserved := reserved) L e (frei Γ reserved)
    let cr ← lowE (reserved := reserved) L r (frei Γ reserved + valueWords (D.typ t f))
    slotStoreC L t f (frei Γ reserved) ce cr
  | _, Γ, _, _, .shift t f (lo := a) (hi := b) _ i von nach _ _ _ _, reserved =>
    if inW a b && inW von von then do
      let ci' ← lowE (reserved := reserved) L i ((frei Γ reserved))
      let cr ← slotC L t f ((frei Γ reserved)) ci'
      let cj ← lowE (reserved := reserved) L i ((frei Γ reserved) + 1)
      let ca ← slotA L t f ((frei Γ reserved) + 1) cj
      let test := bin2 14 ((frei Γ reserved)) cr (wordConstant (frei Γ reserved + 1) von)
      pure (test.1 ++ (guardC ((frei Γ reserved)) 106 ((frei Γ reserved)) ++
        ((wordConstant (frei Γ reserved) nach).1 ++ ca.1 ++ [stC ((frei Γ reserved))])),
        max test.2 (max ca.2 ((frei Γ reserved) + 8)))
    else none
  | _, Γ, _, _, .traverse t inv body, reserved =>
    if inW (D.count t) (D.count t) then do
      let ci' ← lowE (reserved := reserved) L inv ((frei Γ reserved) + 1)
      let cb ← lowB (reserved := reserved) passes A L layout ens ((frei Γ reserved) :: pr) (48, 0) body
      travC ((frei Γ reserved)) (D.count t) ci' cb
    else none
  | _, Γ, _, _, .retry n bis body overflow, reserved => do
    let cc ← lowE (reserved := reserved) L bis ((frei Γ reserved))
    let cu ← lowB (reserved := reserved) passes A L layout ens pr ex overflow
    retryC ((frei Γ reserved)) cc cu (fun targets => lowB (reserved := reserved) passes A L layout ens pr targets body) n
  | _, Γ, _, _, .forever _ inv body, reserved =>
    let pair := counterPair reserved (counterDepthB body)
    if layout.internalResult ≤ pair.1 ∧ pair.2 < FB + reserved ∧ pair.1 ∉ pr ∧ pair.2 ∉ pr then do
      let cc ← lowE (reserved := reserved) L inv (frei Γ reserved)
      foreverC pair.1 pair.2 (frei Γ reserved) passes cc
        (fun targets => lowB (reserved := reserved) passes A L layout ens
          (pair.1 :: pair.2 :: pr) targets body)
    else none
  | _, _, _, _, .breaking _ body, reserved => lowB (reserved := reserved) passes A L layout ens pr ex body
  | _, Γ, _, _, .advances .., reserved => some ([], (frei Γ reserved))
  | _, Γ, _, _, .retires .., reserved => some ([], (frei Γ reserved))
  | _, Γ, _, _, .leave _, reserved => if lit32 (16 + ex.1) then some ([ci 18 (16 + ex.1) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, _, .next _, reserved => if lit32 (16 + ex.2) then some ([ci 18 (16 + ex.2) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, _, .axiomCall a args _ _ _ _ _, reserved => torC0 (reserved := reserved) L a args ((frei Γ reserved))
  | _, Γ, _, _, .axiomCallElse _ _ _ _ _ _ _ _ _, reserved => none
  | _, Γ, _, _, .locks Lk _ body, reserved =>
    if retFreiB body = true ∧ lit32 (16 + ex.1 + 16 * 30) = true ∧ lit32 (16 + ex.2) = true then do
      let cb ← lowB (reserved := reserved) passes A L layout ens pr (16 * 30, 16 * 60) body
      pure (locksCode L (L.lk Lk) ((frei Γ reserved)) cb.1 ex.1 ex.2, max (cb.2 + 1) ((frei Γ reserved) + 18))
    else none
  | _, _, _, _, .consumeTraverse .., reserved => none
  -- C11 execStmt still ignores R.scopes: scope unwinding and invariant
  -- restoration are OPEN in Kern/Semantik/Semantik/T2/Teil2.lean.
  -- Keep both scoped returns refused until the canonical semantics is complete.
  | _, _, _, _, .retScoped .., reserved => none
  | _, _, _, _, .retWhyScoped .., reserved => none
  | _, _, _, _, _, reserved => none

def lowB (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, .nil, reserved => some ([], (frei Γ reserved))
  | _, _, _, _, .cons s rest, reserved => do
    let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
    let cs ← lowS (reserved := reserved) passes A L layout ens pr (exPlus ex cr.1.length) s
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, _, .bind e rest, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, _, .bindCallElse f args _ _ _ err rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let ce ← lowEnd (reserved := reserved) passes A L layout ens pr ex err
    let cr ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (ce.1.length + 1)) rest
    pure (elseC (D.signatur f) ((frei Γ reserved)) (callC A f ((frei Γ reserved)) ca.1) cr.1 ce.1,
      elseTop f ((frei Γ reserved)) ca.2 cr.2 ce.2)
  | _, Γ, _, _, .floatNarrow e low high err rest, reserved =>
    if decide (Gleitkomma.klasse Gleitkomma.f64 (bruch low) ≠ .nan) &&
        decide (Gleitkomma.klasse Gleitkomma.f64 (bruch high) ≠ .nan) then do
      let cc ← floatRangeL ((frei Γ reserved)) low high (lowE (reserved := reserved) L e)
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
      let cx ← lowEnd (reserved := reserved) passes A L layout ens pr (exPlus ex (ce.1.length + cr.1.length + 1)) err
      pure (floatNarrowC ((frei Γ reserved)) cc.1 cx.1 ce.1 cr.1, max cc.2 (max ce.2 (max cr.2 cx.2)))
    else lowEnd (reserved := reserved) passes A L layout ens pr ex err
  | _, Γ, _, _, .floatLit q low high rest, reserved =>
    floatLiteralL ((frei Γ reserved)) q low high (fun _ => lowB (reserved := reserved) passes A L layout ens pr ex rest)
  | _, Γ, _, _, .floatOf e low high rest, reserved =>
    match e with
    | .lit n => floatLiteralL ((frei Γ reserved)) (n, 1) low high (fun _ => lowB (reserved := reserved) passes A L layout ens pr ex rest)
    | _ => do
      let cc ← canonicalFloatRangeL (frei Γ reserved) low high
        (fun d => computedFloatOfE (reserved := reserved) L Gleitkomma.f64 e d)
      let ce ← computedFloatOfE (reserved := reserved) L Gleitkomma.f64 e (frei Γ reserved)
      let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
      pure (floatNarrowC (frei Γ reserved) cc.1 (stopC 107 (frei Γ reserved)) ce.1 cr.1,
        max cc.2 (max (frei Γ reserved + 8) (max ce.2 cr.2)))
  | _, Γ, _, _, .bindCall f args _ _ _ rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
    pure (callC A f ((frei Γ reserved)) ca.1 ++ receiveC (D.signatur f) (frei Γ reserved) ++ cr.1,
      max (callTop f ((frei Γ reserved)) ca.2) (max (receiveTop (D.signatur f) (frei Γ reserved)) cr.2))
  | _, Γ, _, _, .bindCallInd (n := n) p args _ _ _ rest, reserved => do
    let cc ← lowInd (reserved := reserved) L p args
    let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
    pure (cc.1 ++ receiveC (D.sigNr n) (frei Γ reserved) ++ cr.1,
      max cc.2 (max (receiveTop (D.sigNr n) (frei Γ reserved)) cr.2))
  | _, Γ, _, _, .narrow (lo := lo') (hi := hi') e low high err rest, reserved =>
    if inW lo' hi' && inW low low && inW high high then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
      let cx ← lowEnd (reserved := reserved) passes A L layout ens pr (exPlus ex (cr.1.length + 1)) err
      pure (narrowC ((frei Γ reserved)) low high ce.1 cx.1 cr.1, max ce.2 (max ((frei Γ reserved) + 4) (max cx.2 cr.2)))
    else none
  | _, Γ, _, _, .narrowRequired (lo := lo') (hi := hi') e low high rest, reserved =>
    if inW lo' hi' && inW low low && inW high high then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
      pure (narrowC ((frei Γ reserved)) low high ce.1 (stopC 107 (frei Γ reserved)) cr.1, max ce.2 (max ((frei Γ reserved) + 4) (max (frei Γ reserved + 1) cr.2)))
    else none
  | _, Γ, _, _, .bindAxiom a args _ _ _ _ _ rest, reserved => do
    let ct ← torC0 (reserved := reserved) L a args ((frei Γ reserved))
    let ck ← chkC (D.aerg a) ((frei Γ reserved))
    let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max ((frei Γ reserved) + 10) cr.2))
  | _, Γ, _, _, .bindAxiomOpt (e := some τ) a args _ _ _ _ _ rest, reserved => do
    let ct ← torC0 (reserved := reserved) L a args ((frei Γ reserved))
    let ck ← chkC (D.aerg a) ((frei Γ reserved))
    let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max ((frei Γ reserved) + 10) cr.2))
  | _, Γ, _, _, .bindAxiomOpt (e := none) _ _ _ _ _ _ _ _, reserved => none
  | _, Γ, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ _, reserved => none
  | _, Γ, _, _, .bindAxiomElse a args _ _ _ _ _ _ err rest, reserved =>
    match L.tor a, D.aerg a with
    | some b, some (.int lo' hi') =>
      if fehlGut (D.agruende a) b.fehler = true ∧ 0 ≤ lo' ∧ 0 < D.agruende a ∧
          valueWords (.why (D.agruende a)) = 1 then do
        let ct ← torC (reserved := reserved) L a args ((frei Γ reserved))
        let ck ← chkC (some (.int lo' hi')) ((frei Γ reserved))
        let ce ← lowEnd (reserved := reserved) passes A L layout ens pr ex err
        let cr ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (ce.1.length + 1)) rest
        if 16 + 16 * (6 * b.fehler.length) + 16 * (ck.length + (cr.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0]).length) < 2 ^ 31 then
          pure (ct.1 ++ fehlC ((frei Γ reserved)) b.fehler ((16 * (ck.length + (cr.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0]).length) : Nat) : Int) ++ ck ++ (cr.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0]) ++ ce.1,
            max ct.2 (max ((frei Γ reserved) + 10) (max cr.2 ce.2)))
        else none
      else none
    | _, _ => none
  | _, Γ, _, _, .check c err rest, reserved => do
    let cc ← lowE (reserved := reserved) L c ((frei Γ reserved))
    let ce ← lowEnd (reserved := reserved) passes A L layout ens pr ex err
    let cr ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (ce.1.length + 1)) rest
    pure (cc.1 ++ [ci 19 ((frei Γ reserved)) (16 * (cr.1.length + 2)) 0] ++ cr.1 ++
      [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1, max cc.2 (max cr.2 ce.2))
  | _, Γ, _, _, .awaits g _ _ _ _ rest, reserved =>
    if lit32 (L.ga g) && aggregateFits (D.gtyp g) then do
      let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
      pure ([ci 1 ((frei Γ reserved)) (L.ga g) 0, ci 15 ((frei Γ reserved)) ((frei Γ reserved)) 0] ++ cr.1, max ((frei Γ reserved) + 1) cr.2)
    else none
  | _, Γ, _, _, .exchange g neu _ _ rest, reserved =>
    if lit32 (L.ga g) && aggregateFits (D.gtyp g) then do
      let cn ← lowE (reserved := reserved) L neu ((frei Γ reserved) + 1)
      let cr ← lowB (reserved := reserved) passes A L layout ens pr ex rest
      if 16 * (cn.1.length + 5) < 2 ^ 31 then
        pure (exC ((frei Γ reserved)) (L.ga g) cn.1 ++ cr.1, max (max cn.2 ((frei Γ reserved) + 4)) cr.2)
      else none
    else none
  -- IEEE arithmetic needs its software algorithms and proofs.
  | _, _, _, _, .float .., reserved => none
  | _, _, _, _, .narrowRequired .., reserved => none
  | _, _, _, _, _, reserved => none

/-- Dispatch in declaration order. Each branch jumps over the remaining arms; loop exits
    are measured from the end of the entire dispatch. The empty case is unreachable. -/
def lowTags (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option Ty)} →
    Arms D V l Γ Λ Λ' cs → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, _, .nil, _, reserved => some ([], (frei Γ reserved) + 3)
  | _, Γ, _, _, c :: _, .cons b rest, k, reserved => if k < 256 then do
      let cr ← lowTags (reserved := reserved) passes A L layout ens pr ex rest (k + 1)
      let cp ← tagPayloadC ((frei Γ reserved)) c
      let cb ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (cr.1.length + 1)) b
      pure (tagTestC ((frei Γ reserved)) k ++ [ci 19 ((frei Γ reserved) + 1) (16 * (cp.length + cb.1.length + 2)) 0] ++
        cp ++ cb.1 ++ [ci 18 (16 * (cr.1.length + 1)) 0 0] ++ cr.1,
        max ((frei Γ reserved) + 3) (max cb.2 cr.2))
    else none

/-- Reason dispatch uses full word comparisons in declaration order. -/
def lowGrund (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    GrundArms D V l Γ Λ Λ' n → Nat → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, _, _, .nil, _, reserved => some ([], (frei Γ reserved) + 3)
  | _, Γ, _, _, _, .cons b rest, k, reserved => if k < 2 ^ 31 then do
      let cr ← lowGrund (reserved := reserved) passes A L layout ens pr ex rest (k + 1)
      let cb ← lowB (reserved := reserved) passes A L layout ens pr (exPlus ex (cr.1.length + 1)) b
      pure (whyTestC ((frei Γ reserved)) k ++ [ci 19 ((frei Γ reserved) + 1) (16 * (cb.1.length + 2)) 0] ++
        cb.1 ++ [ci 18 (16 * (cr.1.length + 1)) 0 0] ++ cr.1,
        max ((frei Γ reserved) + 3) (max cb.2 cr.2))
    else none

def lowEnd (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → (reserved : Nat := 0) → Option (List II × Nat)
  | _, Γ, _, .leave _, reserved => if lit32 (16 + ex.1) then some ([ci 18 (16 + ex.1) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, .next _, reserved => if lit32 (16 + ex.2) then some ([ci 18 (16 + ex.2) 0 0], (frei Γ reserved)) else none
  | _, Γ, _, .retWhy r _, reserved =>
    some (retWhyC layout r.val, max ((frei Γ reserved)) (retTop layout))
  | _, Γ, _, .ret e _, reserved => do
    let ce ← lowErg (reserved := reserved) L e ((frei Γ reserved))
    pure (ce.1 ++ retC layout ((frei Γ reserved)) ens.1, max ce.2 (max ens.2 (retTop layout)))
  | _, _, _, .cons s rest, reserved => do
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
    let cs ← lowS (reserved := reserved) passes A L layout ens pr (exPlus ex cr.1.length) s
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, .bind e rest, reserved => do
    let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, .bindCallElse f args _ _ _ err rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let ce ← lowEnd (reserved := reserved) passes A L layout ens pr ex err
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr (exPlus ex (ce.1.length + 1)) rest
    pure (elseC (D.signatur f) ((frei Γ reserved)) (callC A f ((frei Γ reserved)) ca.1) cr.1 ce.1,
      elseTop f ((frei Γ reserved)) ca.2 cr.2 ce.2)
  | _, Γ, _, .bindCall f args _ _ _ rest, reserved => do
    let ca ← lowA (reserved := reserved) L args ((frei Γ reserved) + FB)
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
    pure (callC A f ((frei Γ reserved)) ca.1 ++ receiveC (D.signatur f) (frei Γ reserved) ++ cr.1,
      max (callTop f ((frei Γ reserved)) ca.2) (max (receiveTop (D.signatur f) (frei Γ reserved)) cr.2))
  | _, Γ, _, .bindCallInd (n := n) p args _ _ _ rest, reserved => do
    let cc ← lowInd (reserved := reserved) L p args
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
    pure (cc.1 ++ receiveC (D.sigNr n) (frei Γ reserved) ++ cr.1,
      max cc.2 (max (receiveTop (D.sigNr n) (frei Γ reserved)) cr.2))
  | _, Γ, _, .ite c t e, reserved => do
    let cc ← lowE (reserved := reserved) L c ((frei Γ reserved))
    let ce ← lowEnd (reserved := reserved) passes A L layout ens pr ex e
    let ct ← lowEnd (reserved := reserved) passes A L layout ens pr (exPlus ex ce.1.length) t
    pure (cc.1 ++ [ci 19 ((frei Γ reserved)) (16 * (ct.1.length + 1)) 0] ++ ct.1 ++ ce.1, max cc.2 (max ct.2 ce.2))
  | _, Γ, _, .narrow (lo := lo') (hi := hi') e low high err rest, reserved =>
    if inW lo' hi' && inW low low && inW high high then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
      let cx ← lowEnd (reserved := reserved) passes A L layout ens pr (exPlus ex (cr.1.length + 1)) err
      pure (narrowC ((frei Γ reserved)) low high ce.1 cx.1 cr.1, max ce.2 (max ((frei Γ reserved) + 4) (max cx.2 cr.2)))
    else none
  | _, Γ, _, .narrowRequired (lo := lo') (hi := hi') e low high rest, reserved =>
    if inW lo' hi' && inW low low && inW high high then do
      let ce ← lowE (reserved := reserved) L e ((frei Γ reserved))
      let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
      pure (narrowC ((frei Γ reserved)) low high ce.1 (stopC 107 (frei Γ reserved)) cr.1, max ce.2 (max ((frei Γ reserved) + 4) (max (frei Γ reserved + 1) cr.2)))
    else none
  | _, Γ, _, .bindAxiom a args _ _ _ _ _ rest, reserved => do
    let ct ← torC0 (reserved := reserved) L a args ((frei Γ reserved))
    let ck ← chkC (D.aerg a) ((frei Γ reserved))
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max ((frei Γ reserved) + 10) cr.2))
  | _, Γ, _, .bindAxiomOpt (e := some τ) a args _ _ _ _ _ rest, reserved => do
    let ct ← torC0 (reserved := reserved) L a args ((frei Γ reserved))
    let ck ← chkC (D.aerg a) ((frei Γ reserved))
    let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max ((frei Γ reserved) + 10) cr.2))
  | _, Γ, _, .bindAxiomOpt (e := none) _ _ _ _ _ _ _ _, reserved => none
  | _, Γ, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ _, reserved => none
  | _, Γ, _, .awaits g _ _ _ _ rest, reserved =>
    if lit32 (L.ga g) && aggregateFits (D.gtyp g) then do
      let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
      pure ([ci 1 ((frei Γ reserved)) (L.ga g) 0, ci 15 ((frei Γ reserved)) ((frei Γ reserved)) 0] ++ cr.1, max ((frei Γ reserved) + 1) cr.2)
    else none
  | _, Γ, _, .exchange g neu _ _ rest, reserved =>
    if lit32 (L.ga g) && aggregateFits (D.gtyp g) then do
      let cn ← lowE (reserved := reserved) L neu ((frei Γ reserved) + 1)
      let cr ← lowEnd (reserved := reserved) passes A L layout ens pr ex rest
      if 16 * (cn.1.length + 5) < 2 ^ 31 then
        pure (exC ((frei Γ reserved)) (L.ga g) cn.1 ++ cr.1, max (max cn.2 ((frei Γ reserved) + 4)) cr.2)
      else none
    else none
  | _, Γ, _, .bindAxiomElse a args _ _ _ _ _ _ err rest, reserved =>
    match L.tor a, D.aerg a with
    | some b, some (.int lo' hi') =>
      if fehlGut (D.agruende a) b.fehler = true ∧ 0 ≤ lo' ∧ 0 < D.agruende a ∧
          valueWords (.why (D.agruende a)) = 1 then do
        let ct ← torC (reserved := reserved) L a args ((frei Γ reserved))
        let ck ← chkC (some (.int lo' hi')) ((frei Γ reserved))
        let ce ← lowEnd (reserved := reserved) passes A L layout ens pr ex err
        let cr ← lowEnd (reserved := reserved) passes A L layout ens pr (exPlus ex ce.1.length) rest
        if 16 + 16 * (6 * b.fehler.length) + 16 * (ck.length + cr.1.length) < 2 ^ 31 then
          pure (ct.1 ++ fehlC ((frei Γ reserved)) b.fehler ((16 * (ck.length + cr.1.length) : Nat) : Int) ++ ck ++ cr.1 ++ ce.1,
            max ct.2 (max ((frei Γ reserved) + 10) (max cr.2 ce.2)))
        else none
      else none
    | _, _ => none
  | _, _, _, .narrowRequired .., reserved => none
  -- C11 execEnd has the same placeholder as execStmt; it ignores R.scopes.
  -- Keep both scoped returns refused until scope unwinding is modelled.
  | _, _, _, .retScoped .., reserved => none
  | _, _, _, .retWhyScoped .., reserved => none
  | _, _, _, _, reserved => none

end

end Gabbro.Stage0.Senke
