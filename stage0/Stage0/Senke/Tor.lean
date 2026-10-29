/-
  File:      stage0/Stage0/Senke/Tor.lean
  Subject:   The code of a gate call (`PLAN-SELF-HOSTING.md` §2.1.4): the request block at slot `s` -- the system-call
             number in `s`, the arguments in `s + 1 ..` in the order of the argument registers, zero in every register
             the gate does not use -- then `sys s s`, the kernel's word into slot `s`. A bound answer is tested against
             its declared range (`chkC`): outside it, the stop 110, G's hardware outcome `annahme`.

  Accepted: a gate bound on this machine whose parameters go in order into the first argument registers
  (`torGut`), without a reason channel, its parameters words; an answer of an integer type.
-/
import Stage0.Senke.Ausdruck
import Stage0.Senke.Stopp

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- The arguments of a gate, the first into slot `d`, each next one a slot higher. A later argument's scratch slots
    lie above every argument already in place. -/
def lowR (L : Lay D) {Λ : List (Res D)} : {Γ : Ctx} → {τs : List Ty} → Args D Γ Λ τs → Nat → Option (List II × Nat)
  | _, _, .nil, d => some ([], d)
  | _, _, .cons e rest, d => do
    let ce ← lowE L e d
    let cr ← lowR L rest (d + 1)
    pure (ce.1 ++ cr.1, max ce.2 cr.2)

/-- Zero into the `k` slots from `d`. -/
def zeroC (d : Nat) : Nat → List II
  | 0 => []
  | k + 1 => ci 1 d 0 0 :: zeroC (d + 1) k

/-- The registers of a binding whose `n` parameters go in order into the first argument registers. -/
def regsIn (n : Nat) : List (Option Nat) := (List.range 6).map fun i => if i < n then some i else none

/-- A binding the lowering takes, for a gate of `n` parameters. -/
def torGut (b : TorB) (n : Nat) : Bool := decide (n ≤ 6) && b.regs == regsIn n && lit32 b.nr

/-- The call of a gate of `n` parameters, its request block at slot `s`, the arguments' code `ca`. -/
def torCode (nr s n : Nat) (ca : List II) : List II :=
  ca ++ zeroC (s + 1 + n) (6 - n) ++ [ci 1 s nr 0, ci 23 s s 0]

/-- A parameter type whose value is one word of the request. -/
def wortTy : Ty → Bool
  | .int _ _ => true
  | .bool => true
  | _ => false

def torC (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (s : Nat) :
    Option (List II × Nat) :=
  match L.tor a with
  | some b =>
    if torGut b (D.aparams a).length = true ∧ (D.aparams a).all wortTy = true then do
      let ca ← lowR L args (s + 1)
      pure (torCode b.nr s (D.aparams a).length ca.1, max ca.2 (s + 7))
    else none
  | none => none

/-- The call of a gate without a reason channel: its raw answer is the kernel's word. -/
def torC0 (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (s : Nat) :
    Option (List II × Nat) :=
  if D.agruende a = 0 then torC L a args s else none

/-- `d := slot s` with `d = s + 1`, then `d := d < k` (the constant into `d + 1`). -/
def sltC (s : Nat) (k : Int) : List II :=
  [ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) k 0,
    ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)]

/-- `lo ≤ slot s`, else the stop 110: `d := s < lo`, `d := (d = 0)`, the guard over `d`. -/
def loC (s : Nat) (lo : Int) : List II :=
  sltC s lo ++ [ci 1 (((s + 1 : Nat) : Int) + 1) 0 0,
    ci 14 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)] ++ guardC (s + 1) 110 (s + 2)

/-- `slot s ≤ hi`, else the stop 110: `d := s < hi + 1`, the guard over `d`. -/
def hiC (s : Nat) (hi : Int) : List II := sltC s (hi + 1) ++ guardC (s + 1) 110 (s + 2)

/-- The test of the answer in slot `s` against its declared type; it writes the slots `s + 1 .. s + 9`. A bound beyond
    64 bits needs no test; any other must be a 32-bit literal. -/
def chkC : Option Ty → Nat → Option (List II)
  | some (.int lo hi), s =>
    let a := if lo ≤ -2 ^ 63 then some [] else if lit32 lo then some (loC s lo) else none
    let b := if 2 ^ 63 - 1 ≤ hi then some [] else if lit32 (hi + 1) then some (hiC s hi) else none
    match a, b with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | _, _ => none

/-- The test of one listed errno `e` with its case `i` (`d = s + 1`): if slot `s` holds `e`, the case into slot `s`
    and a jump to `J` bytes past the end of this test; else on after it. -/
def fehlC1 (s : Nat) (e : Int) (i : Nat) (J : Int) : List II :=
  [ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) e 0,
    ci 14 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
    ci 19 ((s + 1 : Nat) : Int) 48 0, ci 1 s i 0, ci 18 (16 + J) 0 0]

/-- The tests of the listed errnos, in order; a hit jumps to `J` bytes past the end of all of them. -/
def fehlC (s : Nat) : List (Int × Nat) → Int → List II
  | [], _ => []
  | (e, i) :: r, J => fehlC1 s e i (16 * (6 * r.length) + J) ++ fehlC s r J

/-- An errno map the lowering takes for a gate with `n` reasons: every errno an error word, every case a reason. -/
def fehlGut (n : Nat) (l : List (Int × Nat)) : Bool :=
  l.all fun x => decide (-4095 ≤ x.1) && decide (x.1 ≤ -1) && decide (x.2 < n) && decide (x.2 < 2 ^ 31)

end Gabbro.Stage0.Senke
