module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecEinSchritt
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBleibt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Reverse direction of the primitive-recursion body. Any run of the body that
    reaches its end determines the value of the step code at the paired input.
    The boundary between the two pairing segments and the step block is located
    with `randAusEndePrefix`; the final segment is the standalone step block,
    whose own reverse lemma supplies the evaluation witness. -/
def precRumpfRueckAussage (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (aus frei freiCg y i a : Nat) (r rEnd : Rahmen) (k : Nat)
    (hlenCg : 0 < cgBlk.length)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei) (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hk : (Schritt (precRumpf cgBlk aus frei))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (precRumpf cgBlk aus frei).length) :
    ∃ v, Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y i)) = Part.some v ∧
      rEnd.temp aus = some (natVal v) ∧
      (∀ s, s < frei + 10 → s ≠ aus → s ≠ frei + 4 → s ≠ frei + 5 → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := True

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
