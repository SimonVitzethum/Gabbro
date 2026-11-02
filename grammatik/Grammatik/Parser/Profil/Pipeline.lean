module

public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Profil.Auswahl
public import Grammatik.Parser.Profil.Register

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/Pipeline.lean
  Subject:   **C14: the translation pipeline of one build mode with the profile bound.** One function for
             every source text and an explicit `BauModus`: lex, parse, SELECT (`Auswahl.waehleL` over the
             original items), refuse a reserved `TESTBUILD` name, admit the profile binding of the selected
             tree (`bindungB`), take the profile blocks out (they are metadata now, kept in
             `ProfilZert`), then the same stages as `uebersetzeAllg`: `pre108`, `elabU`, `lowerAllg`.

  * `uebersetzeWahl_eq_allg` -- a unit without a gate and without a profile block, whose (empty) binding is
    admitted, translates exactly as `uebersetzeAllg` does, in either mode: the unit of before;
  * a unit with a profile now translates (before, `profT` was an item without G form), but only with an
    ADMITTED binding: conflicting modes, unsupported values, unresolved or ambiguous `assume`, a second
    profile and uncovered library requirements are refused here, before elaboration;
  * `ProfilZert` -- the certificate the unit statement carries (`Zielsatz/Projekte/Profil.lean`): the
    selection (original, mode, selected) and the profile binding read off the SELECTED tree.
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

mutual
/-- The tree without its profile blocks: their content lives in the binding, not in the elaborated unit. -/
def ohneProfilI : SItemTief → List SItemTief
  | .modT n b => [.modT n (ohneProfilL b)]
  | .pubT it => (ohneProfilI it).map SItemTief.pubT
  | .profT _ _ => []
  | it => [it]
/-- The list form. -/
def ohneProfilL : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => ohneProfilI it ++ ohneProfilL rest
end

mutual
/-- No profile block stands anywhere in the item. -/
def profilfreiI : SItemTief → Bool
  | .modT _ b => profilfreiL b
  | .pubT it => profilfreiI it
  | .profT _ _ => false
  | _ => true
/-- The list form. -/
def profilfreiL : List SItemTief → Bool
  | [] => true
  | it :: rest => profilfreiI it && profilfreiL rest
end

mutual
/-- **Without a profile block, taking them out changes nothing.** -/
theorem ohneProfilI_id (it : SItemTief) (h : profilfreiI it = true) : ohneProfilI it = [it] := by
  cases it with
  | modT n b =>
      have ih := ohneProfilL_id b (by simpa only [profilfreiI] using h)
      simp only [ohneProfilI, ih]
  | pubT x =>
      have ih := ohneProfilI_id x (by simpa only [profilfreiI] using h)
      simp only [ohneProfilI, ih, List.map_cons, List.map_nil]
  | profT a b => simp only [profilfreiI, Bool.false_eq_true] at h
  | _ => simp [ohneProfilI]
/-- The list form. -/
theorem ohneProfilL_id (its : List SItemTief) (h : profilfreiL its = true) : ohneProfilL its = its := by
  cases its with
  | nil => simp only [ohneProfilL]
  | cons x xs =>
      simp only [profilfreiL, Bool.and_eq_true] at h
      simp only [ohneProfilL, ohneProfilI_id x h.1, ohneProfilL_id xs h.2, List.singleton_append]
end

end Gabbro.Grammatik.Parser.ProfilBindung

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2
open Parser.Auswahl Parser.ProfilBindung

/-- **The certificate a selected, profile-bound unit carries**: the selection of the original tree and the
    profile binding read off the SELECTED tree. -/
structure ProfilZert where
  auswahl : Selection
  bindung : ProfileBinding

/-- The certificate of an original tree in a mode. -/
def ProfilZert.von (m : BauModus) (items : List SItemTief) : ProfilZert :=
  let sel := Selection.von m items
  ⟨sel, ProfileBinding.aus sel.ausgewaehlt⟩

/-- **The certificate is admitted**: no reserved `TESTBUILD` name, and the profile binding passes. -/
def ProfilZert.zulaessig (z : ProfilZert) : Bool := z.auswahl.zulaessig && bindungB z.bindung

/-- **THE TRANSLATION OF AN ITEM TREE IN A BUILD MODE**: select, admit the certificate, take the profile
    blocks out, then the stages of `uebersetzeAllg`. -/
def uebersetzeWahlItems (m : BauModus) (items : List SItemTief) :
    Except String (Σ u : UProg, Programm (declOf u) × List (declOf u).Fn) :=
  if (ProfilZert.von m items).auswahl.zulaessig = false then
    .error "build selection: `TESTBUILD` is reserved and cannot be declared as a name (G003)"
  else if bindungB (ProfilZert.von m items).bindung = false then
    .error "profile binding refused: modes, assumptions or library requirements are not consistent"
  else
    match elabU (pre108 (ohneProfilL (ProfilZert.von m items).auswahl.ausgewaehlt)) with
    | .error e => .error e
    | .ok u =>
      match lowerAllg u with
      | .error e => .error e
      | .ok (P, fs) => .ok ⟨u, P, fs⟩

/-- **THE LEAN TRANSLATION PIPELINE IN A BUILD MODE** for every source text. -/
def uebersetzeWahl (m : BauModus) (s : String) :
    Except String (Σ u : UProg, Programm (declOf u) × List (declOf u).Fn) :=
  match lex s with
  | .error _ => .error "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items => uebersetzeWahlItems m items

/-- **The unit of before**: an item tree without a gate and without a profile block, no reserved name and an
    admitted (empty) binding, goes through the stages of `uebersetzeAllg` unchanged, in either mode. -/
theorem uebersetzeWahlItems_unveraendert (m : BauModus) {items : List SItemTief}
    (hg : gatefreiL items = true) (hp : profilfreiL items = true) (hr : reserviertL items = false)
    (hb : bindungB (ProfileBinding.aus items) = true) :
    uebersetzeWahlItems m items =
      (match elabU (pre108 items) with
       | .error e => .error e
       | .ok u =>
         match lowerAllg u with
         | .error e => .error e
         | .ok (P, fs) => .ok ⟨u, P, fs⟩) := by
  have hs : (Selection.von m items).ausgewaehlt = items := Selection.von_gatefrei m hg
  have hz : (ProfilZert.von m items).auswahl.zulaessig = true := by
    simp only [ProfilZert.von, Selection.zulaessig, Selection.von, hr, Bool.not_false]
  have hbz : bindungB (ProfilZert.von m items).bindung = true := by
    simp only [ProfilZert.von, hs]
    exact hb
  have hsel : (ProfilZert.von m items).auswahl.ausgewaehlt = items := hs
  unfold uebersetzeWahlItems
  simp only [hz, hbz, hsel, ohneProfilL_id items hp, Bool.true_eq_false, ↓reduceIte]

/-- **`uebersetzeWahl` on such a source is `uebersetzeAllg`.** -/
theorem uebersetzeWahl_eq_allg (m : BauModus) (s : String) {toks : List Token}
    {items : List SItemTief} (hl : lex s = .ok toks) (hpar : parseTopTief toks = .ok items)
    (hg : gatefreiL items = true) (hp : profilfreiL items = true) (hr : reserviertL items = false)
    (hb : bindungB (ProfileBinding.aus items) = true) :
    uebersetzeWahl m s = uebersetzeAllg s := by
  unfold uebersetzeWahl uebersetzeAllg
  simp only [hl, hpar]
  exact uebersetzeWahlItems_unveraendert m hg hp hr hb

end Gabbro.Grammatik
