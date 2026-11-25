module

public import Core.Beobachtung.Unentscheidbar.Simulation.SubstratBau
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.BlockKette

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

/-- Closing a translated block: bind its output slot into the local scope and
    end the program there. The block itself contains no `.ende`, so it stays
    relocatable; the bind is the only consumer of its result. -/
def abschliessen (blk : List Befehl) (aus : Nat) : List Befehl :=
  blk ++ [.binden nameX aus, .ende]

def frameBinden (rEnd : Rahmen) (aus : Nat) : Rahmen :=
  { rEnd with pc := rEnd.pc + 1, lokale := rEnd.temp aus :: rEnd.lokale }

def frameEnde (rB : Rahmen) : Rahmen :=
  { rB with rueckgabe := rB.lokale.head?.join, stopp := some .fertig }

/-- The forward half of the bridge: a correct block, closed by a bind and an
    end, halts with exactly the value the coded evaluation produces. -/
theorem haeltMitAusBlock (blk : List Befehl) (c : Nat.Partrec.Code) (ein aus frei : Nat)
    (hblk : BlockKorrekt blk c ein aus frei)
    (n : Nat) (r : Rahmen) (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (a : Nat) (ha : Nat.Partrec.Code.eval c n = Part.some a) :
    HaeltMit (abschliessen blk aus) r a := by
  rcases hblk with ⟨hein, haus, hun, hnr⟩
  rcases hnr n r hpc hr with ⟨hfwd, hbwd⟩
  obtain ⟨k, rEnd, hrun, hpcE, htempE, hpres, hlok, hrueck, hstopp⟩ := hfwd a ha
  have hbleib := laufBleibtVorEnde blk r k rEnd hrun hpcE
  have hprefix : (Schritt (abschliessen blk aus))^[k] (some r) = some rEnd := by
    change (Schritt (blk ++ [.binden nameX aus, .ende]))^[k] (some r) = some rEnd
    exact (laufAnhang blk [.binden nameX aus, .ende] r k hbleib).trans hrun
  let rB := frameBinden rEnd aus
  let rE := frameEnde rB
  have hgetB : (blk ++ [.binden nameX aus, .ende])[rEnd.pc]? = some (.binden nameX aus) := by
    rw [hpcE]
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using
      (getNachPrefix blk [.binden nameX aus, .ende] 0 (by simp))
  have hsB : Schritt (abschliessen blk aus) (some rEnd) = some rB := by
    change Schritt (blk ++ [.binden nameX aus, .ende]) (some rEnd) = some rB
    show (match (blk ++ [.binden nameX aus, .ende])[rEnd.pc]? with
      | none => none | some b => some (b.auswerten rEnd)) = some rB
    rw [hgetB]
    rfl
  have hgetE : (blk ++ [.binden nameX aus, .ende])[rB.pc]? = some (.ende) := by
    change (blk ++ [.binden nameX aus, .ende])[rEnd.pc + 1]? = some (.ende)
    rw [hpcE]
    rw [show blk.length + 1 = blk.length + 1 by rfl]
    simpa only [Nat.add_zero, List.getElem?_cons_succ, List.getElem?_cons_zero] using
      (getNachPrefix blk [.binden nameX aus, .ende] 1 (by simp))
  have hsE : Schritt (abschliessen blk aus) (some rB) = some rE := by
    change Schritt (blk ++ [.binden nameX aus, .ende]) (some rB) = some rE
    show (match (blk ++ [.binden nameX aus, .ende])[rB.pc]? with
      | none => none | some b => some (b.auswerten rB)) = some rE
    rw [hgetE]
    rfl
  have hrunTotal : (Schritt (abschliessen blk aus))^[k + 2] (some r) = some rE := by
    rw [show k + 2 = 2 + k by omega, Function.iterate_add_apply, hprefix]
    change Schritt (abschliessen blk aus) (Schritt (abschliessen blk aus) (some rEnd)) = some rE
    rw [hsB, hsE]
  refine ⟨rE, ⟨k + 2, hrunTotal⟩, ?_⟩
  change rE.rueckgabe.bind NatAusgabe = some a
  have hrueckgabe : rE.rueckgabe = some (natVal a) := by
    change rB.lokale.head?.join = some (natVal a)
    change (rEnd.temp aus :: rEnd.lokale).head?.join = some (natVal a)
    rw [show (rEnd.temp aus :: rEnd.lokale).head? = some (rEnd.temp aus) by rfl]
    change rEnd.temp aus = some (natVal a)
    exact htempE
  rw [hrueckgabe]
  exact natValAusgabe a

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
