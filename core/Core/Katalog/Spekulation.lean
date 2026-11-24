module

public import Core.Katalog.Ziel

@[expose] public section

namespace Gabbro.Core.Katalog

/-- An adversarial prediction for a branch, indirect target or store-to-load forwarding choice.
    The inputs are the site and the preceding sequence of speculative sites. -/
structure Praediktor where
  sprung : Nat → List Nat → Bool
  indirekt : Nat → List Nat → Nat
  weiterleitung : Nat → List Nat → Option Nat

/-- A finite window may be used only when it is covered by a catalogue assumption. -/
structure Spekulationshuelle where
  fenster : Option Nat

/-- No finite speculation window has been established for the current platform rows. -/
def Plattform.spekulationshuelle : Plattform → Spekulationshuelle
  | .x86_64 | .aarch64 | .riscv64 => ⟨none⟩

/-- One slot per speculative instruction, including instructions that touch no address. -/
def Spekulationshuelle.zugriffe (h : Spekulationshuelle) (ausfuehrung : List (Option Ort)) : List Ort :=
  (match h.fenster with
   | none => ausfuehrung
   | some n => ausfuehrung.take n).filterMap id

end Gabbro.Core.Katalog
