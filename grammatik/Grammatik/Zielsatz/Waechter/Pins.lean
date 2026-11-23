/-
  File:      Grammatik/Zielsatz/Waechter/Pins.lean
  Subject:   GUARD 2 (B24 step 0, `dokumente/PERFECT-MODEL.md` §6.2): HASH PINS of the goal's foundations. A change of any pinned
             definition stops the build HERE until the owner has reviewed it.

  Pinned, each by `Grundlagen.konstHash` (kind, type, and body or constructor types of the ONE constant):
  * the GOAL: `GabbroZiel`, the statement of `gabbro_ziel`, and every project constant `GabbroZiel` mentions
    directly (its top-level unfolding: the checker interface, the duties, the hardware premise, the runtime start,
    the reachability of the thread machine, the legs `ZielFX`, ...). The set itself is pinned: a constant that
    enters or leaves the statement stops the build too;
  * the ERROR NOTION: `HaltArt` (the stop kinds of the machine) and the two exits of a body, `Logik` and `Hardware`;
  * MACHINE G's step relation `RufSchrittG` with its seven parts, the GX step `RufSchrittGX`, its reachability, and
    the thread machine's step `FadenSchrittX` with its reachability `FadenErreichbarX`;
  * the ACCEPTANCE target `AkzeptiertSpecX`, `BesitzStart`, `Kernzelle.AkkuStart` and the checker interface
    `PrueferX`. The decided checker `AkzeptiertX` and `komp` are pinned in `Gen/Abdeckung/ZellenPruefung.lean`
    (closure hash of definition bodies) and are not repeated here.
  The pins are shallow on purpose: a change below them (a leg, a semantic function) is pinned where it is a
  foundation of its own, by the closure hash of the interim `I` in `Abhaengigkeit.lean`, or by `ZellenPruefung`.
  A mismatch names the constant and its new hash. To accept a change: show the diff of the definition to the owner
  (a change of the goal's meaning is the owner's decision), then update `erwartet`. The hash can also
  move with a change of the Lean toolchain; the pins are renewed the same way.
-/
module
public import Grammatik.Zielsatz.Waechter.Grundlagen
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd
public import Grammatik.Bausteine.Kernzelle.Start
meta import Lean
meta import Grammatik.Zielsatz.Waechter.Grundlagen
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Waechter.Pins

open Lean Meta

/-- The explicitly pinned foundations (the goal's top-level unfolding is added by `pruefe`). -/
def fundamente : List Name :=
  [``GabbroZiel, ``gabbro_ziel,
   ``HaltArt, ``Logik, ``Hardware,
   ``RufSchrittG, ``RufSchrittG1, ``RufSchrittG2, ``RufSchrittG3, ``RufSchrittG4, ``RufSchrittG5,
   ``RufSchrittG6, ``RufSchrittG7, ``RufSchrittGX, ``RufErreichbarGX, ``FadenSchrittX, ``FadenErreichbarX,
   ``AkzeptiertSpecX, ``BesitzStart, ``Kernzelle.AkkuStart, ``PrueferX]

/-- The pins (constant, hash). -/
def erwartet : List (String × Nat) :=
  [("Gabbro.Grammatik.ArenaOwnership.Body.ArenaIface", 2015042850979675306),
   ("Gabbro.Grammatik.ArenaOwnership.Body.ArenaIface.mitRuhe", 9162612990869930285),
   ("Gabbro.Grammatik.CallSitePflicht", 9530866131580058033),
   ("Gabbro.Grammatik.Deklaration", 1714867822632439978),
   ("Gabbro.Grammatik.Deklaration.Fn", 17204742538371299011),
   ("Gabbro.Grammatik.Deklaration.Glob", 9809598458606827167),
   ("Gabbro.Grammatik.Deklaration.Lock", 9621973680224979707),
   ("Gabbro.Grammatik.Deklaration.Tab", 3967831657932548808),
   ("Gabbro.Grammatik.Deklaration.mitRuhe", 1918711195057099193),
   ("Gabbro.Grammatik.Deklaration.params", 2281756250370356686),
   ("Gabbro.Grammatik.Env", 12224569182990433734),
   ("Gabbro.Grammatik.Faden", 14403385194728597129),
   ("Gabbro.Grammatik.FadenErreichbarX", 13471155707658304474),
   ("Gabbro.Grammatik.FadenMaschine", 11471888026139355551),
   ("Gabbro.Grammatik.FadenSchrittX", 7723776471298794706),
   ("Gabbro.Grammatik.FadenStart", 10196911527510091920),
   ("Gabbro.Grammatik.ForeignVertrag", 4170385999753763496),
   ("Gabbro.Grammatik.Hardware", 9710838574722742003),
   ("Gabbro.Grammatik.HardwareAnnahmenHw", 11545019595201106216),
   ("Gabbro.Grammatik.Kernzelle.AkkuStart", 7661969142440665383),
   ("Gabbro.Grammatik.Logik", 2034376749497188344),
   ("Gabbro.Grammatik.Orakel", 17979933563844943804),
   ("Gabbro.Grammatik.Orakel.mitRuhe", 4920826142900139369),
   ("Gabbro.Grammatik.PostDeckt", 6966285080597660895),
   ("Gabbro.Grammatik.Programm.mitRuhe", 39513566710970032),
   ("Gabbro.Grammatik.RufErreichbarGX", 39002645452898813),
   ("Gabbro.Grammatik.RufSchrittG", 10629364002582776938),
   ("Gabbro.Grammatik.RufSchrittG1", 5354039865245379230),
   ("Gabbro.Grammatik.RufSchrittG2", 7475213346088696455),
   ("Gabbro.Grammatik.RufSchrittG3", 1998554824880272312),
   ("Gabbro.Grammatik.RufSchrittG4", 9301915198496933086),
   ("Gabbro.Grammatik.RufSchrittG5", 6733764078020005352),
   ("Gabbro.Grammatik.RufSchrittG6", 15012039328993882063),
   ("Gabbro.Grammatik.RufSchrittG7", 4495356088239155602),
   ("Gabbro.Grammatik.RufSchrittGX", 3544935177436106871),
   ("Gabbro.Grammatik.RufStartG", 264372132229778863),
   ("Gabbro.Grammatik.Speicher", 16205526301227654416),
   ("Gabbro.Grammatik.SperrInv.mitRuhe", 13084384350175552992),
   ("Gabbro.Grammatik.Zielsatz.AkzeptiertSpecX", 993163876264741096),
   ("Gabbro.Grammatik.Zielsatz.Aufzaehlung", 918620576238753556),
   ("Gabbro.Grammatik.Zielsatz.BesitzStart", 5112494802886740462),
   ("Gabbro.Grammatik.Zielsatz.Einheit", 3131441607351251131),
   ("Gabbro.Grammatik.Zielsatz.Einheit.P", 4127216547473909902),
   ("Gabbro.Grammatik.Zielsatz.Einheit.Q", 5401677272433480697),
   ("Gabbro.Grammatik.Zielsatz.Einheit.S", 5424270171859170496),
   ("Gabbro.Grammatik.Zielsatz.Einheit.arenen", 16635920511234464261),
   ("Gabbro.Grammatik.Zielsatz.Einheit.ws", 11439083774032863037),
   ("Gabbro.Grammatik.Zielsatz.GabbroZiel", 11346472482990690075),
   ("Gabbro.Grammatik.Zielsatz.GeteiltV", 1637750752879958823),
   ("Gabbro.Grammatik.Zielsatz.HaltArt", 2448775503336247766),
   ("Gabbro.Grammatik.Zielsatz.Laufzeit", 12243269587258651039),
   ("Gabbro.Grammatik.Zielsatz.NutzerPflichtA", 7108488666839424791),
   ("Gabbro.Grammatik.Zielsatz.PrueferX", 15431571038677044340),
   ("Gabbro.Grammatik.Zielsatz.PrueferX.akzeptiert", 10584986775344213285),
   ("Gabbro.Grammatik.Zielsatz.ZielFX", 9535624463376634407),
   ("Gabbro.Grammatik.Zielsatz.gabbro_ziel", 5405798519669835328)]

def pruefe : MetaM Unit := do
  let env ← getEnv
  let some (.defnInfo z) := env.find? ``GabbroZiel | throwError "GabbroZiel is not a definition"
  let oben := z.value.getUsedConstants.toList.filter (imProjekt env)
  let namen := (fundamente ++ oben).eraseDups.toArray.qsort (fun a b => a.toString < b.toString)
  let gemessen := namen.toList.map fun n => (n.toString, (konstHash env n).toNat)
  let mut befunde : List String := []
  for (k, h) in gemessen do
    match erwartet.lookup k with
    | none => befunde := befunde ++ [s!"NEW (not pinned): {k} (hash {h})"]
    | some e => if e != h then befunde := befunde ++ [s!"CHANGED: {k} (hash {h}, pinned {e})"]
  for (k, _) in erwartet do
    if (gemessen.lookup k).isNone then befunde := befunde ++ [s!"GONE from the foundations: {k}"]
  melde "a foundation of the goal changed" befunde
    ("show the diff to the owner (PERFECT-MODEL.md §6); after the owner's consent update `erwartet` in " ++
     s!"Waechter/Pins.lean. Measured:\nerwartet := {alsListe gemessen}")

run_meta pruefe

end Gabbro.Grammatik.Zielsatz.Waechter.Pins
