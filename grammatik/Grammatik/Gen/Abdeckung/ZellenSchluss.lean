/-
  File:      Grammatik/Gen/Abdeckung/ZellenSchluss.lean
  Subject:   The TEXT of the closing file `Gen/Zeugen/Schluss.lean`, written by `gen-zellen-sammeln`: for every cell of
             the universe its reason -- a witness theorem of `Gen/Zeugen/M` or `N`, or a theorem of
             `Satz/Unmoeglich.lean` -- and from them the cell table and the checker and compiler theorems with no
             assumption left. A cell without a reason is returned as OPEN, and then no closing file is written. The
             text is untrusted: the kernel checks the file.
-/
import Grammatik.Gen.Druck.LeanZeuge

namespace Gabbro.Grammatik.Gen

/-- The atoms of a cell as `a b c` Lean booleans. -/
private def bs (x : Zelle) : List String := x.atome.map toString

/-- The reason a GOOD cell needs no valid test, if a theorem gives one. -/
def unmoeglichGut (x : Zelle) : Option String :=
  match x.komp, x.art, x.atome with
  | 4, 0, [false, true] => some "Or.inr (nie_gut u_4_01)"
  | 8, 0, [a, true, c] => some s!"Or.inr (nie_gut (u_8_ax {a} {c}))"
  | 7, 1, [true, true, false] => some "Or.inr (nie_gut u_7_1_110)"
  | 6, 0, [m, h, g] => if h || g then some s!"Or.inr (nie_gueltig fun e hv => ug_6_0 {m} {h} {g} rfl e hv)" else none
  | _, _, _ => none

/-- A bad cell no program of the source has, if a theorem says so: the proof of `¬ e.Hat x`. -/
def unmoeglichSchlecht (x : Zelle) : Option String :=
  match x.komp, x.art, x.atome with
  | 0, 0, [false, b, c] => some s!"u_0_ohne {b} {c} e"
  | 1, 0, [true, true, false] => some "u_1_0_110 e"
  | 4, 0, [true, false] => some "u_4_10 e"
  | 8, 0, [a, true, c] => some s!"u_8_ax {a} {c} e"
  | _, _, _ => none

/-- How the tests of N cover a bad cell: one test whose needed cells are the cell itself; for a bad root cell `5.0 h g`
    one test per multiplicity of the start (`m_5_0`); for a bad pool cell `6.0 1 h g` one test with its root cell
    (`m_6_0`). -/
inductive NGrund
  | einfach (st : String)
  | wurzel (st0 st1 : String)
  | pool (st : String)

/-- The cells a test may need beside the cell itself. -/
def NGrund.partner (x : Zelle) (m : Bool) : Option Zelle :=
  match x.komp, x.art, x.atome with
  | 5, 0, [h, g] => some ⟨6, 0, true, [m, h, g]⟩
  | 6, 0, [true, h, g] => if h || g then some ⟨5, 0, true, [h, g]⟩ else none
  | _, _, _ => none

/-- A test `st` covers `x` when its needed cells are `x` (and `p` if given). -/
private def deckt (st : String) (x : Zelle) (p : Option Zelle) : String :=
  match p with
  | none => s!"⟨{st}.bnoetig, fun w hw => by\n        obtain rfl := (by decide : ∀ w ∈ {st}.bnoetig, w = {x.lean}) w hw\n        exact h, {st}.zellen⟩"
  | some q => s!"⟨{st}.bnoetig, fun w hw => by\n        rcases (by decide : ∀ w ∈ {st}.bnoetig, w = {x.lean} ∨ w = {q.lean}) w hw with rfl | rfl <;> assumption,\n        {st}.zellen⟩"

/-- The proof term for a bad cell. -/
def schlechtBeweis (x : Zelle) : NGrund → String
  | .einfach st => s!"fun e h => {deckt st x none}"
  | .wurzel st0 st1 =>
    match x.atome with
    | [h, g] => s!"fun e h => by\n      obtain ⟨m, hm⟩ := m_5_0 {h} {g} e h\n      cases m\n      · exact {deckt st0 x (NGrund.partner x false)}\n      · exact {deckt st1 x (NGrund.partner x true)}"
    | _ => "?"
  | .pool st =>
    match x.atome with
    | [_, h, g] => s!"fun e h => by\n      have hm := (m_6_0 true {h} {g} rfl e h).1\n      exact {deckt st x (NGrund.partner x true)}"
    | _ => "?"

/-- **The closing file**, or the open cells. `gut x` names the M witness of a good cell, `schl x` how N covers a bad
    cell; `mods` are the witness modules. -/
def schlussText (gut : Zelle → Option String) (schl : Zelle → Option NGrund) (mods : List String) :
    Except (List Zelle) String :=
  let fall := fun (x : Zelle) =>
    if x.schlecht then
      match unmoeglichSchlecht x with
      | some u => some s!"fun e h => absurd h ({u})"
      | none => (schl x).map (schlechtBeweis x)
    else
      match gut x with
      | some st => some s!"Or.inl ({st}.zellen _ (by decide))"
      | none => unmoeglichGut x
  let offen := zellAlle.filter fun x => (fall x).isNone
  if !offen.isEmpty then .error offen else
  let liste := String.intercalate ",\n    " (zellAlle.map Zelle.lean)
  let pat := String.intercalate " | " (zellAlle.map fun _ => "rfl")
  let gutF := String.join (zellAlle.map fun x =>
    if x.schlecht then "  · exact absurd hs (by decide)\n" else s!"  · exact {(fall x).getD "?"}\n")
  let schlF := String.join (zellAlle.map fun x =>
    if x.schlecht then s!"  · exact {(fall x).getD "?"}\n" else "  · exact absurd hs (by decide)\n")
  let erreicht := zellAlle.filter fun x => !x.schlecht && (gut x).isSome
  let erreichtF := String.join (erreicht.map fun x => s!"  · exact {(gut x).getD "?"}.zellen _ (by decide)\n")
  let erreichtPat := String.intercalate " | " (erreicht.map fun _ => "rfl")
  .ok (s!"/-\n  File:      Grammatik/Gen/Zeugen/Schluss.lean\n  Subject:   GENERATED (`gen-zellen-sammeln`, `ZellenSchluss.lean`): every cell of the universe has its reason, so\n             M and N are complete and a neutral checker or compiler that treats them right treats every program of\n             the source right. Do not edit.\n-/\n" ++
    String.join (mods.map fun m => s!"import {m}\n") ++
    "import Grammatik.Gen.Abdeckung.Satz.Neutral\nimport Grammatik.Gen.Abdeckung.Satz.Unmoeglich\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace Gabbro.Grammatik.Gen.Zeugen\n\nopen Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz\n\n" ++
    s!"theorem zellAlle_liste : zellAlle = [\n    {liste}] := by decide\n\n" ++
    s!"theorem erreicht_raum : ∀ w ∈ erreicht, RaumGut ncZiel w := by\n  intro w hw\n  simp only [erreicht, List.mem_cons, List.not_mem_nil, or_false] at hw\n  rcases hw with {erreichtPat}\n{erreichtF}\n" ++
    s!"theorem schluss_gut : GutGedeckt ncZiel := by\n  intro x hx hs\n  rw [zellAlle_liste] at hx\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx\n  rcases hx with {pat}\n{gutF}\n" ++
    s!"theorem schluss_schlecht : SchlechtGedeckt ncZiel erreicht := by\n  intro x hx hs\n  rw [zellAlle_liste] at hx\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx\n  rcases hx with {pat}\n{schlF}\n" ++
    "/-- **M and N are complete.** -/\ntheorem mn_vollstaendig : Tafel (mGen ncZiel) (nGen ncZiel) :=\n  tafel_erzeugt ncZiel erreicht schluss_gut schluss_schlecht erreicht_raum\n\n" ++
    "/-- **A neutral checker (a function: terminating, deterministic) that answers like the model on M and N answers like\n    the model on every program of the source.** -/\ntheorem pruefer_korrekt (C : Einsatz → Bool) (hC : Neutral C) (hM : ∀ m ∈ mGen ncZiel, C m = m.gueltig)\n    (hN : ∀ n ∈ nGen ncZiel, C n = n.gueltig) (e : Einsatz) : C e = e.gueltig :=\n  pruefer_hinreichend ncZiel erreicht schluss_gut schluss_schlecht erreicht_raum C hC hM hN e\n\n" ++
    "/-- **A neutral compiler correct on M is correct on every valid program of the source.** -/\ntheorem compiler_korrekt (K : Einsatz → Prop) (hK : NeutralKorrekt K) (hM : ∀ m ∈ mGen ncZiel, K m) (e : Einsatz)\n    (hv : e.gueltig = true) : K e :=\n  compiler_hinreichend ncZiel erreicht schluss_gut schluss_schlecht erreicht_raum K hK hM e hv\n\nend Gabbro.Grammatik.Gen.Zeugen\n")

end Gabbro.Grammatik.Gen
