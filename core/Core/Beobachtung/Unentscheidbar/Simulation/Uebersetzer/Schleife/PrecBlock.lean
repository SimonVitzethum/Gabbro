module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBleibt
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.VerschiebbarBlk

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The primitive-recursion block: read both components of the input, compute
    the base case with `cfBlk` into the accumulator, initialise the counter to
    zero and run the recursion loop. Scratch slots of the projections start at
    `freiL`; slots of the base block start at `freiCf`. -/
def precBlk (cfBlk cgBlk : List Befehl) (ein aus frei freiL freiCf : Nat) : List Befehl :=
  (((leftBlk ein (frei + 0) freiL ++ rightBlk ein (frei + 1) freiL) ++ cfBlk) ++
    [.literal (frei + 2) 0]) ++ precSchleife cgBlk aus frei

/-- The counter initialisation stays inside its one-instruction block. -/
theorem bleibtImBlockPrecInit (frei : Nat) :
    BleibtImBlock [(.literal (frei + 2) 0 : Befehl)] := by
  unfold BleibtImBlock
  rintro ⟨pc, temp, lok, rueck, stopp, z, o, g, fs, f, fu, m, ar, pl, env⟩ b hlt hget
  simp only [List.length_cons, List.length_nil] at hlt ⊢
  interval_cases pc
  simp only [List.getElem?_cons_zero] at hget
  injection hget with hb
  subst b
  simp only [Befehl.auswerten, Rahmen.schreibe]

/-- The counter initialisation is relocatable. -/
theorem verschiebbarPrecInit (frei : Nat) :
    VerschiebbaresProgramm [(.literal (frei + 2) 0 : Befehl)] := by
  unfold VerschiebbaresProgramm
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  simp only [List.getElem?_cons_zero]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [Verschiebbar]
  · intro d hd
    cases hd

/-- The primitive-recursion block stays inside itself, given the stay-inside
    and relocatability facts for the two sub-blocks. These are the induction
    hypotheses of the code induction and are not free assumptions of the
    correctness statement. -/
theorem bleibtImBlockPrecBlk (cfBlk cgBlk : List Befehl) (ein aus frei freiL freiCf : Nat)
    (hcf : BleibtImBlock cfBlk) (hvCf : VerschiebbaresProgramm cfBlk)
    (hcg : BleibtImBlock cgBlk) (hvCg : VerschiebbaresProgramm cgBlk) :
    BleibtImBlock (precBlk cfBlk cgBlk ein aus frei freiL freiCf) := by
  let L := leftBlk ein (frei + 0) freiL
  let R := rightBlk ein (frei + 1) freiL
  let I := [(.literal (frei + 2) 0 : Befehl)]
  let S := precSchleife cgBlk aus frei
  have hL : BleibtImBlock L := by
    dsimp only [L]
    exact bleibtImBlockLeft ein (frei + 0) freiL
  have hR : BleibtImBlock R := by
    dsimp only [R]
    exact bleibtImBlockRight ein (frei + 1) freiL
  have hvR : VerschiebbaresProgramm R := by
    dsimp only [R]
    exact verschiebbarRight ein (frei + 1) freiL
  have hI : BleibtImBlock I := by
    dsimp only [I]
    exact bleibtImBlockPrecInit frei
  have hvI : VerschiebbaresProgramm I := by
    dsimp only [I]
    exact verschiebbarPrecInit frei
  have hS : BleibtImBlock S := by
    dsimp only [S]
    exact bleibtImBlockPrecSchleife cgBlk aus frei hcg hvCg
  have hvS : VerschiebbaresProgramm S := by
    dsimp only [S]
    exact verschiebbarPrecSchleife cgBlk aus frei hvCg
  have h1 : BleibtImBlock (L ++ R) := bleibtImBlockAppend L R hL hvR hR
  have h2 : BleibtImBlock ((L ++ R) ++ cfBlk) := bleibtImBlockAppend (L ++ R) cfBlk h1 hvCf hcf
  have h3 : BleibtImBlock (((L ++ R) ++ cfBlk) ++ I) :=
    bleibtImBlockAppend ((L ++ R) ++ cfBlk) I h2 hvI hI
  have h4 : BleibtImBlock ((((L ++ R) ++ cfBlk) ++ I) ++ S) :=
    bleibtImBlockAppend (((L ++ R) ++ cfBlk) ++ I) S h3 hvS hS
  simpa only [precBlk, L, R, I, S] using h4

/-- Block correctness of the primitive-recursion block, as a pinned obligation.
    The forward half is `precSchleifeVorwaerts` composed with the projection and
    base-case blocks; the reverse half is `precSchleifeRueckAussage`. Difficulty:
    hard; proof sketch: compose `blockLeft`, `blockRight` and the two-input run
    to reach the loop entry, initialise the counter with the literal block, then
    apply the two loop directions with `evalPrecAlsFolge`. -/
def blockPrecAussage (cfBlk cgBlk : List Befehl) (cf cg : Nat.Partrec.Code)
    (ein aus frei freiL freiCf freiCg : Nat) : Prop :=
  ein < frei → aus < frei → ein ≠ aus →
  frei + 0 < freiL → frei + 1 < freiL →
  frei + 0 < freiCf → aus < freiCf →
  frei + 21 ≤ freiCf → frei + 20 ≤ freiCg →
  BlockKorrekt cfBlk cf (frei + 0) aus freiCf →
  BleibtImBlock cfBlk → VerschiebbaresProgramm cfBlk →
  BlockKorrekt cgBlk cg (frei + 5) aus freiCg →
  BleibtImBlock cgBlk → VerschiebbaresProgramm cgBlk →
  precSchleifeRueckAussage cgBlk cf cg (frei + 0) aus frei freiCg →
  BlockKorrekt (precBlk cfBlk cgBlk ein aus frei freiL freiCf)
    (.prec cf cg) ein aus frei

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
