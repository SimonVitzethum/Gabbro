module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Scratch

open Nat.Partrec

def natZuCode : Nat → Code
  | 0 => Code.zero
  | n + 1 => Code.pair Code.right (natZuCode n)

def codeZuNat : Code → Option Nat
  | Code.zero => some 0
  | Code.pair Code.right c => (codeZuNat c).map Nat.succ
  | _ => none

theorem codeZuNat_natZuCode (n : Nat) : codeZuNat (natZuCode n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natZuCode, codeZuNat, ih]

inductive Mini where
  | leaf : Nat → Mini
  | node : Mini → Mini → Mini

def miniZuCode : Mini → Code
  | .leaf n => Code.pair (natZuCode 0) (natZuCode n)
  | .node a b => Code.pair (natZuCode 1) (Code.pair (miniZuCode a) (Code.pair (miniZuCode b) Code.zero))

def miniVonCode : Code → Option Mini
  | Code.pair tag kids =>
      match codeZuNat tag with
      | some 0 => do
          let n ← codeZuNat kids
          some (.leaf n)
      | some 1 =>
          match kids with
          | Code.pair a (Code.pair b Code.zero) => do
              let a' ← miniVonCode a
              let b' ← miniVonCode b
              some (.node a' b')
          | _ => none
      | _ => none
  | _ => none

theorem miniVonCode_miniZuCode : ∀ m : Mini, miniVonCode (miniZuCode m) = some m
  | .leaf n => by
      change miniVonCode (Code.pair Code.zero (natZuCode n)) = some (.leaf n)
      unfold miniVonCode
      simp [codeZuNat, natZuCode, codeZuNat_natZuCode]
  | .node a b => by
      have ih1 := miniVonCode_miniZuCode a
      have ih2 := miniVonCode_miniZuCode b
      simp [miniZuCode, miniVonCode, natZuCode, codeZuNat, codeZuNat_natZuCode, ih1, ih2]

end Scratch
