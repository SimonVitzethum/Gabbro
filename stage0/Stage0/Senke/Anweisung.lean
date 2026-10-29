/-
  File:      stage0/Stage0/Senke/Anweisung.lean
  Subject:   The lowering of stage 0, part 2: statements and blocks of machine G into `S0IR`.

  The first free slot of a context `Γ` is `frei Γ`: an expression of a statement is computed there; a `bind`
  computes its value there, which is then the new variable's slot. `assignVar x e` moves the value into `x`'s slot;
  `ite c t e` tests `c` with `brz` and jumps over the other branch; a call (`call`, `bindCall`) places the
  callee's frame at the first free slot (`callC`). `lo` is the lowest slot an assignment may write (a function's
  body keeps its parameters for `ensures`); `A f` is the code address of `f`; `ens` the function's `ensures` code, which
  a `ret` runs (`retC`). Accepted so far: `assignVar`, `ite`, `onOption` (the index word kept for the bound variable), `call`, `ret`, the writes `assignGlob`, `assignSlot`, `assignThru`, `leave` and `next` (a jump to their target), `traverse` (`travC`), `breaking` (its block), `advances` and `retires` (no code: G only marks them), the gates `axiomCall` and `bindAxiom` (`torC`), `publish` (a store, release under TSO), `locks` without `ret` in its body (`locksCode`: take, the body,
  give on every way out), and the blocks `nil`, `cons`, `bind`, `bindCall`, `awaits` (a load) and `exchange` (`exC`, a `cas` loop); everything else is refused (`none`). The answer's
  number is an upper bound of the slots the code writes.
-/
import Stage0.Senke.Ausdruck
import Stage0.Senke.Stopp
import Stage0.Senke.Tor
import Stage0.Senke.Sperre.Code

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- The arguments of a call into the callee's parameter slots from `p` (the callee frame's first variable slot);
    the head goes highest. The last argument is computed first, so a later one's scratch slots lie above every
    argument already in place. -/
def lowA (L : Lay D) {Λ : List (Res D)} : {Γ : Ctx} → {τs : List Ty} → Args D Γ Λ τs → Nat → Option (List II × Nat)
  | _, _, .nil, p => some ([], p)
  | _, _ :: τs, .cons e rest, p => do
    let cr ← lowA L rest p
    let ce ← lowE L e (p + τs.length)
    pure (cr.1 ++ ce.1, max cr.2 ce.2)

/-- A call of `f` with its frame at slot `F` of the caller: the arguments (`ca`), the depth one less, the
    address of `f`, `call`. -/
def callTail (A : D.Fn → Nat) (f : D.Fn) (F : Nat) : List II :=
  [ci 1 ((F + FB + (D.params f).length : Nat) : Int) 1 0,
   ci 4 ((F + 2 : Nat) : Int) 2 ((F + FB + (D.params f).length : Nat) : Int),
   ci 1 ((F + FB + (D.params f).length : Nat) : Int) (A f) 0,
   ci 20 ((F + FB + (D.params f).length : Nat) : Int) F 0]

def callC (A : D.Fn → Nat) (f : D.Fn) (F : Nat) (ca : List II) : List II := ca ++ callTail A f F

def callTop (f : D.Fn) (F t : Nat) : Nat := max t (F + FB + (D.params f).length + 1)

def lowErg (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → ErgExpr D Γ Λ e → Nat → Option (List II × Nat)
  | _, .empty, d => some ([], d + 1)
  | _, .val e, d => lowE L e d

/-- `ret`: the result from slot `r` into slot `q` (`FB + np`, the slot of `ensures`' result variable), the
    `ensures` code `ens`, the check, slot 2, back. -/
def retC (q r : Nat) (ens : List II) : List II :=
  [ci 2 q r 0] ++ ens ++ [ci 19 ((q + 1 : Nat) : Int) 48 0, ci 2 2 q 0, ci 21 0 0 0] ++ stopC 102 (q + 1)

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

mutual
def lowS (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → Option (List II × Nat)
  | _, Γ, _, _, .assignVar x e =>
    if lo ≤ vslot x ∧ vslot x ∉ pr then do
      let ce ← lowE L e (frei Γ)
      pure (ce.1 ++ [ci 2 (vslot x) (frei Γ) 0], ce.2)
    else none
  | _, Γ, _, _, .ite c t e => do
    let cc ← lowE L c (frei Γ)
    let ce ← lowB A L lo ens pr ex e
    let ct ← lowB A L lo ens pr (exPlus ex (ce.1.length + 1)) t
    pure (cc.1 ++ [ci 19 (frei Γ) (16 * (ct.1.length + 2)) 0] ++ ct.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1,
      max cc.2 (max ct.2 ce.2))
  | _, Γ, _, _, .onOption (n := n) o p a =>
    if decide (n ≤ 2 ^ 63) then do
      let co ← lowE L o (frei Γ)
      let ca ← lowB A L lo ens pr ex a
      let cp ← lowB A L lo ens pr (exPlus ex (ca.1.length + 1)) p
      pure (co.1 ++ [ci 1 (frei Γ + 1) (-1) 0, ci 10 (frei Γ + 1) (frei Γ) (frei Γ + 1)] ++
        [ci 19 (frei Γ + 1) (16 * (cp.1.length + 2)) 0] ++ cp.1 ++
        [ci 18 (16 * (ca.1.length + 1)) 0 0] ++ ca.1,
        max co.2 (max (frei Γ + 2) (max cp.2 ca.2)))
    else none
  | _, Γ, _, _, .call f args _ _ => do
    let ca ← lowA L args (frei Γ + FB)
    pure (callC A f (frei Γ) ca.1, callTop f (frei Γ) ca.2)
  | _, Γ, _, _, .ret e _ => do
    let ce ← lowErg L e (frei Γ)
    pure (ce.1 ++ retC lo (frei Γ) ens.1, max ce.2 (max ens.2 (retTop lo)))
  | _, Γ, _, _, .assignGlob g e _ _ =>
    if lit32 (L.ga g) then do
      let ce ← lowE L e (frei Γ)
      pure (ce.1 ++ [ci 1 ((frei Γ + 1 : Nat) : Int) (L.ga g) 0] ++ [stC (frei Γ)], max ce.2 (frei Γ + 2))
    else none
  | _, Γ, _, _, .publish g e _ _ _ _ =>
    if lit32 (L.ga g) then do
      let ce ← lowE L e (frei Γ)
      pure (ce.1 ++ [ci 1 ((frei Γ + 1 : Nat) : Int) (L.ga g) 0] ++ [stC (frei Γ)], max ce.2 (frei Γ + 2))
    else none
  | _, Γ, _, _, .assignSlot t f i e _ _ => do
    let ce ← lowE L e (frei Γ)
    let ci' ← lowE L i (frei Γ + 1)
    let ca ← slotA L t f (frei Γ + 1) ci'
    pure (ce.1 ++ ca.1 ++ [stC (frei Γ)], max ce.2 ca.2)
  | _, Γ, _, _, .assignThru _ t _ f i e _ _ => do
    let ce ← lowE L e (frei Γ)
    let ci' ← lowE L i (frei Γ + 1)
    let ca ← slotA L t f (frei Γ + 1) ci'
    pure (ce.1 ++ ca.1 ++ [stC (frei Γ)], max ce.2 ca.2)
  | _, Γ, _, _, .traverse t inv body =>
    if lit32 (D.count t) then do
      let ci' ← lowE L inv (frei Γ + 1)
      let cb ← lowB A L lo ens (frei Γ :: pr) (48, 0) body
      travC (frei Γ) (D.count t) ci' cb
    else none
  | _, _, _, _, .breaking _ body => lowB A L lo ens pr ex body
  | _, Γ, _, _, .advances .. => some ([], frei Γ)
  | _, Γ, _, _, .retires .. => some ([], frei Γ)
  | _, Γ, _, _, .leave _ => if lit32 (16 + ex.1) then some ([ci 18 (16 + ex.1) 0 0], frei Γ) else none
  | _, Γ, _, _, .next _ => if lit32 (16 + ex.2) then some ([ci 18 (16 + ex.2) 0 0], frei Γ) else none
  | _, Γ, _, _, .axiomCall a args _ _ _ _ _ => torC0 L a args (frei Γ)
  | _, Γ, _, _, .locks Lk _ body =>
    if retFreiB body = true ∧ lit32 (16 + ex.1 + 16 * 30) = true ∧ lit32 (16 + ex.2) = true then do
      let cb ← lowB A L lo ens pr (16 * 30, 16 * 60) body
      pure (locksCode L (L.lk Lk) (frei Γ) cb.1 ex.1 ex.2, max (cb.2 + 1) (frei Γ + 18))
    else none
  | _, _, _, _, _ => none

def lowB (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → Option (List II × Nat)
  | _, Γ, _, _, .nil => some ([], frei Γ)
  | _, _, _, _, .cons s rest => do
    let cr ← lowB A L lo ens pr ex rest
    let cs ← lowS A L lo ens pr (exPlus ex cr.1.length) s
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, _, .bind e rest => do
    let ce ← lowE L e (frei Γ)
    let cr ← lowB A L lo ens pr ex rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, _, .bindCall f args _ _ _ rest => do
    let ca ← lowA L args (frei Γ + FB)
    let cr ← lowB A L lo ens pr ex rest
    pure (callC A f (frei Γ) ca.1 ++ [ci 2 (frei Γ) (frei Γ + 2) 0] ++ cr.1, max (callTop f (frei Γ) ca.2) cr.2)
  | _, Γ, _, _, .bindAxiom a args _ _ _ _ _ rest => do
    let ct ← torC0 L a args (frei Γ)
    let ck ← chkC (D.aerg a) (frei Γ)
    let cr ← lowB A L lo ens pr ex rest
    pure (ct.1 ++ ck ++ cr.1, max ct.2 (max (frei Γ + 10) cr.2))
  | _, Γ, _, _, .awaits g _ _ _ _ rest =>
    if lit32 (L.ga g) then do
      let cr ← lowB A L lo ens pr ex rest
      pure ([ci 1 (frei Γ) (L.ga g) 0, ci 15 (frei Γ) (frei Γ) 0] ++ cr.1, max (frei Γ + 1) cr.2)
    else none
  | _, Γ, _, _, .exchange g neu _ _ rest =>
    if lit32 (L.ga g) then do
      let cn ← lowE L neu (frei Γ + 1)
      let cr ← lowB A L lo ens pr ex rest
      if 16 * (cn.1.length + 5) < 2 ^ 31 then
        pure (exC (frei Γ) (L.ga g) cn.1 ++ cr.1, max (max cn.2 (frei Γ + 4)) cr.2)
      else none
    else none
  | _, _, _, _, _ => none
end

end Gabbro.Stage0.Senke
