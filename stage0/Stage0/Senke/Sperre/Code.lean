/-
  File:      stage0/Stage0/Senke/Sperre/Code.lean
  Subject:   The code of a lock (`PLAN-SELF-HOSTING.md` §2.1.6): three words per lock at `L.lk` -- owner (the holding
             thread's number + 1), count, waiters. `nimmC`: the owner is me -- count + 1; else `cas owner 0 -> me`
             and count 1, and on failure waiters + 1, `futex_wait` on the owner word, waiters - 1, again. `gibC`:
             count - 1; at 0 `cas owner me -> 0` and `futex_wake` when there are waiters. `meC` computes the thread's
             number from its frame: `(fp - sb) / st + 1`.
-/
import Stage0.Senke.Ausdruck
import Stage0.Senke.Stopp

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- The thread's number + 1 into slot `t` (scratch `t + 1`). -/
def meC (L : Lay D) (t : Nat) : List II :=
  [ci 17 t 0 0, ci 1 ((t : Int) + 1) L.sb 0, ci 4 t t ((t : Int) + 1), ci 1 ((t : Int) + 1) L.st 0,
    ci 6 t t ((t : Int) + 1), ci 1 ((t : Int) + 1) 1 0, ci 3 t t ((t : Int) + 1)]

/-- `w := w + d` for the word at `a` by `cas`, again until it holds (scratch from `u`): 7 instructions. -/
def addC (a u : Nat) (d : Int) : List II :=
  [ci 1 u a 0, ci 15 ((u + 1 : Nat) : Int) u 0, ci 1 ((u + 3 : Nat) : Int) d 0,
    ci 3 ((u + 2 : Nat) : Int) ((u + 1 : Nat) : Int) ((u + 3 : Nat) : Int),
    ci 22 ((u + 4 : Nat) : Int) u ((u + 1 : Nat) : Int),
    ci 14 ((u + 4 : Nat) : Int) ((u + 4 : Nat) : Int) ((u + 1 : Nat) : Int),
    ci 19 ((u + 4 : Nat) : Int) (-96) 0]

/-- `futex (a, op, v)` with `v` from slot `v`, the request block from `q`: 8 instructions. -/
def futexC (a op : Nat) (v q : Nat) (vConst : Option Int) : List II :=
  [ci 1 q 202 0, ci 1 ((q + 1 : Nat) : Int) a 0, ci 1 ((q + 2 : Nat) : Int) op 0,
    (match vConst with
     | some k => ci 1 ((q + 3 : Nat) : Int) k 0
     | none => ci 2 ((q + 3 : Nat) : Int) v 0),
    ci 1 ((q + 4 : Nat) : Int) 0 0, ci 1 ((q + 5 : Nat) : Int) 0 0, ci 1 ((q + 6 : Nat) : Int) 0 0,
    ci 23 ((q + 7 : Nat) : Int) q 0]

/-- **Take the lock** with words at `a`, scratch from slot `s` (to `s + 17`). -/
def nimmC (L : Lay D) (a s : Nat) : List II :=
  -- me; owner = me?
  meC L s ++ [ci 1 ((s + 1 : Nat) : Int) a 0, ci 15 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 14 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) s, ci 19 ((s + 1 : Nat) : Int) (16 * 7) 0] ++
  -- mine: count + 1, done (jump over the rest: 5 + 29 + 3 instructions after this jump)
  [ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0, ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 1 ((s + 3 : Nat) : Int) 1 0, ci 3 ((s + 2 : Nat) : Int) ((s + 2 : Nat) : Int) ((s + 3 : Nat) : Int),
    ci 16 ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int) 0, ci 18 (16 * (1 + 5 + 23 + 3)) 0 0] ++
  -- not mine: cas owner 0 -> me; old 0: got it
  [ci 1 ((s + 1 : Nat) : Int) a 0, ci 1 ((s + 2 : Nat) : Int) 0 0, ci 2 ((s + 3 : Nat) : Int) s 0,
    ci 22 ((s + 4 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
    ci 19 ((s + 4 : Nat) : Int) (16 * 24) 0] ++
  -- wait: waiters + 1, futex_wait (owner word, the owner seen), waiters - 1, again
  addC (a + 16) (s + 5) 1 ++ futexC a 128 (s + 4) (s + 10) none ++ addC (a + 16) (s + 5) (-1) ++
  [ci 18 (-(16 * 27)) 0 0] ++
  -- got it: count 1
  [ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0, ci 1 ((s + 2 : Nat) : Int) 1 0,
    ci 16 ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int) 0]

/-- **Give the lock** with words at `a`, scratch from slot `s` (to `s + 17`). -/
def gibC (L : Lay D) (a s : Nat) : List II :=
  -- count - 1; not 0: done
  [ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0, ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 1 ((s + 3 : Nat) : Int) 1 0, ci 4 ((s + 2 : Nat) : Int) ((s + 2 : Nat) : Int) ((s + 3 : Nat) : Int),
    ci 16 ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int) 0,
    ci 19 ((s + 2 : Nat) : Int) 32 0, ci 18 (16 * (1 + 7 + 4 + 3 + 8)) 0 0] ++
  -- 0: cas owner me -> 0
  meC L s ++ [ci 1 ((s + 1 : Nat) : Int) a 0, ci 2 ((s + 3 : Nat) : Int) s 0, ci 1 ((s + 4 : Nat) : Int) 0 0,
    ci 22 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 3 : Nat) : Int)] ++
  -- waiters: wake one
  [ci 1 ((s + 1 : Nat) : Int) ((a + 16 : Nat) : Int) 0, ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 19 ((s + 2 : Nat) : Int) (16 * 9) 0] ++
  futexC a 129 0 (s + 10) (some 1)

theorem meC_len (L : Lay D) (t : Nat) : (meC L t).length = 7 := rfl
theorem nimmC_len (L : Lay D) (a s : Nat) : (nimmC L a s).length = 7 + 4 + 6 + 5 + 7 + 8 + 7 + 1 + 3 := rfl
theorem gibC_len (L : Lay D) (a s : Nat) : (gibC L a s).length = 7 + 7 + 4 + 3 + 8 := rfl

variable {V : Vertrag D}

mutual
/-- A statement without `ret` or `retWhy`, among the forms the lowering takes (every other form: `false`). -/
def retFreiS : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → Bool
  | _, _, _, _, .assignVar .. | _, _, _, _, .assignGlob .. | _, _, _, _, .assignSlot ..
  | _, _, _, _, .assignThru .. | _, _, _, _, .call .. | _, _, _, _, .advances .. | _, _, _, _, .retires ..
  | _, _, _, _, .leave _ | _, _, _, _, .next _ | _, _, _, _, .axiomCall .. | _, _, _, _, .publish .. => true
  | _, _, _, _, .ite _ t e => retFreiB t && retFreiB e
  | _, _, _, _, .onOption _ p a => retFreiB p && retFreiB a
  | _, _, _, _, .traverse _ _ b => retFreiB b
  | _, _, _, _, .breaking _ b => retFreiB b
  | _, _, _, _, .locks _ _ b => retFreiB b
  | _, _, _, _, _ => false

def retFreiB : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → Bool
  | _, _, _, _, .nil => true
  | _, _, _, _, .cons s r => retFreiS s && retFreiB r
  | _, _, _, _, .bind _ r => retFreiB r
  | _, _, _, _, .bindCall _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .awaits _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .exchange _ _ _ _ r => retFreiB r
  | _, _, _, _, _ => false
end

/-- The code of `locks Lk { body }` around the body's code `cb`, with `g` the length of `gibC`: take; the body (its
    `leave` and `next` to the two stubs after the end); give; over the stubs; the `leave` stub: give, on to the
    outer `leave` target `exL`; the `next` stub: give, on to `exN` (both from the end of this code). -/
def locksCode (L : Lay D) (a s : Nat) (cb : List II) (exL exN : Int) : List II :=
  nimmC L a s ++ cb ++ gibC L a s ++ [ci 18 (16 * (1 + 2 * ((gibC L a s).length + 1))) 0 0] ++
    gibC L a s ++ [ci 18 (16 + exL + 16 * ((gibC L a s).length + 1)) 0 0] ++
    gibC L a s ++ [ci 18 (16 + exN) 0 0]

end Gabbro.Stage0.Senke
