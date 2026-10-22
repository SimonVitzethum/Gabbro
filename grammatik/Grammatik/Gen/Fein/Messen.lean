/-
  File:      Grammatik/Gen/Fein/Messen.lean
  Subject:   THE BODY TABLES OF THE COVERAGE DRIVER (`gen-abdeckung`, `Gen/Abdeckung/Lauf.lean`), built by the filtered
             generator of `Suche.lean`: a body is kept when it brings a fine cell or a register member (`endM`, with the
             cells `@loop`/`@held` and the container pairs) that no smaller body of its context brought. Every member a
             body of the bound can carry is therefore carried by a kept body, and the tables stay small; the exhaustive
             tables grow with every new constructor. Untrusted: the driver measures, it proves nothing.
-/
import Grammatik.Gen.Fein.Suche
import Grammatik.Gen.Abdeckung.Messung

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- A register member as a cell of its own kind (`art = 9`). -/
def mitgliedZelle (m : String) : FZelle := ⟨9, 0, 0, false, [(hash m).toNat]⟩

/-- **The fine cells and the register members.** -/
def Kenner.mitM : Kenner D :=
  ⟨fun e => fzE e ++ (exprM e).map mitgliedZelle, fun s => fzS s ++ (stmtM s).map mitgliedZelle,
   fun b => fzB b ++ (blockM b).map mitgliedZelle, fun x => fzEnd x ++ (endM x).map mitgliedZelle⟩

/-- **The body tables of a member** for the coverage driver: per function the filtered bodies by size up to `nb` (the
    filter `okFuer` of components 3 and 8 as in `Spez.tabellen`). -/
def _root_.Gabbro.Grammatik.Gen.Spez.tabellenF (z : Spez) (nb : Nat) (p3 p8 : Bool) :
    List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) :=
  letI : Zahlen := z.zahlen
  let D := z.deklaration
  (Aufz.fn (D := D)).map fun f =>
    let t := tabN (genTF Kenner.mitM (vertragVon D f) nb nb nb false (D.params f) (Signatur.anfang D (D.signatur f)))
    ⟨f, (List.range (nb + 1)).map fun k => (t k).filter (okFuer p3 p8 (List.finRange z.fns.length) f)⟩

end Gabbro.Grammatik.Gen.Fein
