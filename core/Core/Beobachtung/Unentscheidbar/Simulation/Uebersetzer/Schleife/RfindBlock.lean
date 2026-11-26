module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Divergenz
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecFolge

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The minimisation loop for `rfind'`. Slot `frei+0` holds `a`, `frei+1` the
    search start `m`, `frei+2` the current candidate `y`. Each iteration forms
    `pair a y` into `frei+4`, runs the translated `cf` block from `frei+4` into
    `frei+6`, and compares `frei+6` against zero in `frei+5`. A zero result
    jumps to the exit, which copies `y` into `aus`; otherwise `y` is incremented
    and the loop repeats. The `cf` block must be translated with input `frei+4`
    and output `frei+6`. -/
def rfindSchleife (cfBlk : List Befehl) (aus frei : Nat) : List Befehl :=
  paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10) ++
    cfBlk ++
    [.literal (frei + 5) 0, .vergleichen .lt (frei + 5),
      .springeWenn (frei + 5) false 3] ++
    [.literal (frei + 7) 1, .binaer .add (frei + 2),
      .zurueckSprung (49 + cfBlk.length)] ++
    kopie aus (frei + 2)

/-- Forward convergence of the minimisation loop, as a pinned obligation. If
    `cf` evaluates to zero first at candidate `y0 >= m` and stays defined up to
    `y0`, the loop reaches its end with `y0` in the output slot. Difficulty:
    hard; proof sketch: induct over `y0 - m`, discharge one iteration with the
    pairing block, the `cf` block and the concrete zero test, then apply the
    induction hypothesis at the incremented candidate. -/
def rfindKonvergenzAussage (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf freiP : Nat) : Prop :=
  ∀ (m y0 v : Nat) (r rEnd : Rahmen) (schr : Nat),
    r.pc = 0 →
    r.temp (frei + 0) = some (natVal a) →
    r.temp (frei + 1) = some (natVal m) →
    r.temp (frei + 2) = some (natVal m) →
    m ≤ y0 →
    Nat.Partrec.Code.eval cf (Nat.pair a y0) = Part.some 0 →
    (∀ y, m ≤ y → y < y0 → ∃ v', Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some v') →
    BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf →
    VerschiebbaresProgramm cfBlk → BleibtImBlock cfBlk →
    frei + 20 ≤ freiCf → frei + 10 ≤ freiP →
    (Schritt (rfindSchleife cfBlk aus frei))^[schr] (some r) = some rEnd →
    rEnd.pc = (rfindSchleife cfBlk aus frei).length →
    rEnd.temp aus = some (natVal y0)

/-- Divergence of the minimisation loop, as a pinned obligation. When no
    candidate yields zero while every candidate is defined, the loop never
    dies; conversely a non-terminating run of the loop means no zero is found.
    Difficulty: hard; proof sketch: prove both directions by induction over
    the candidates and use `laufStirbtNicht_iff` from `Divergenz` to connect the
    zero-free search to `LaufStirbtNicht`. -/
def rfindDivergenzAussage (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf freiP : Nat) (m : Nat) (r : Rahmen) : Prop :=
  ((∀ y, m ≤ y → ∃ v, Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some v) ∧
    (∀ y, m ≤ y → Nat.Partrec.Code.eval cf (Nat.pair a y) ≠ Part.some 0)) ↔
    LaufStirbtNicht (rfindSchleife cfBlk aus frei) r

/-- Block correctness of the `rfind'` block, as a pinned obligation. The block
    reads both components of the input, initialises the candidate from `m` and
    runs the minimisation loop; convergence and divergence are supplied by the
    two pinned obligations above. Difficulty: hard. -/
def blockRfindAussage (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (ein aus frei freiL freiCf freiP : Nat) : Prop :=
  ein < frei → aus < frei → ein ≠ aus →
  frei + 0 < freiL → frei + 1 < freiL →
  frei + 4 < freiCf → frei + 6 < freiCf →
  frei + 10 ≤ freiCf → frei + 10 ≤ freiP →
  BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf →
  BleibtImBlock cfBlk → VerschiebbaresProgramm cfBlk →
  rfindKonvergenzAussage cfBlk cf (frei + 0) aus frei freiCf freiP →
  rfindDivergenzAussage cfBlk cf (frei + 0) aus frei freiCf freiP (frei + 1)
    (startVon 0) →
  BlockKorrekt (cfBlk ++ rfindSchleife cfBlk aus frei) (.rfind' cf) ein aus frei

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
