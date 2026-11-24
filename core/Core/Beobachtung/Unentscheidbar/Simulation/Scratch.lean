module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Scratch

open Nat.Partrec.Code

def natZuCode : Nat → Code
  | 0 => .zero
  | n + 1 => .succ (natZuCode n)

def codeZuNat : Code → Option Nat
  | .zero => some 0
  | .succ c => (codeZuNat c).map Nat.succ
  | _ => none

theorem codeZuNat_natZuCode (n : Nat) : codeZuNat (natZuCode n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natZuCode, codeZuNat, ih]

inductive Mini where
  | leaf : Nat → Mini
  | node : Mini → Mini → Mini

def miniZuCode : Mini → Code
  | .leaf n => .pair (natZuCode 0) (natZuCode n)
  | .node a b => .pair (natZuCode 1) (.pair (miniZuCode a) (.pair (miniZuCode b) .zero))

def miniVonCode : Code → Option Mini
  | .pair tag kids =>
      match codeZuNat tag with
      | some 0 => do
          let n ← codeZuNat kids
          some (.leaf n)
      | some 1 =>
          match kids with
          | .pair a (.pair b .zero) => do
              let a' ← miniVonCode a
              let b' ← miniVonCode b
              some (.node a' b')
          | _ => none
      | _ => none
  | _ => none

theorem miniVonCode_miniZuCode : ∀ m : Mini, miniVonCode (miniZuCode m) = some m
  | .leaf n => by simp [miniZuCode, miniVonCode, codeZuNat_natZuCode]
  | .node a b => by
      have ih1 := miniVonCode_miniZuCode a
      have ih2 := miniVonCode_miniZuCode b
      simp [miniZuCode, miniVonCode, codeZuNat_natZuCode, ih1, ih2]

end Scratch
