/-
  Emit an accepted M/refused N table and its neutral compiler theorem.
  Semantic gate refusals are not characterized by structural cells.
-/
module
public import Grammatik.Gen.Druck.LeanTerm
public import Grammatik.Gen.Abdeckung.Waehlen
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Gen.Druck.LeanZeuge
@[expose] public section


namespace Gabbro.Grammatik.Gen


/-- The reason a GOOD cell needs no valid test, if a theorem gives one. -/
def unmoeglichGut (x : Zelle) : Option String :=
  match x.komp, x.art, x.atome with
  | 4, 0, [false, true] => some "Or.inr (nie_gut u_4_01)"
  | 2, 0, [a, b, true, true] => some s!"Or.inr (nie_gut (u_2_0_11 {a} {b}))"
  | 2, 0, [true, b, false, d] => some s!"Or.inr (nie_gut (u_2_0_sig {b} {d}))"
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
  | 3, 0, [true, false] => some "u_3_0_10 e"
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

/-- How the explicit list `Nw` covers a test `st` whose needed cells are `x` (and `p` if given), for the table of the
    witness lists. -/
def decktT (st : String) (x : Zelle) (p : Option Zelle) : String :=
  let teil := match p with
    | none => s!"(fun w hw => by\n        obtain rfl := (by decide : ∀ w ∈ {st}.bnoetig, w = {x.lean}) w hw\n        exact h)"
    | some q => s!"(fun w hw => by\n        rcases (by decide : ∀ w ∈ {st}.bnoetig, w = {x.lean} ∨ w = {q.lean}) w hw with rfl | rfl <;> assumption)"
  s!"⟨{st}.e, by simp [Nw], n_deckt Mw erreicht erreicht_mw {st}.e e {st}.bnoetig {st}.e_gedeckt\n        {teil}⟩"

/-- The proof term of `Tafel.schlecht` at a bad cell over the witness lists. -/
def schlechtBeweisT (x : Zelle) : NGrund → String
  | .einfach st => s!"fun e h => {decktT st x none}"
  | .wurzel st0 st1 =>
    match x.atome with
    | [h, g] => s!"fun e h => by\n      obtain ⟨m, hm⟩ := m_5_0 {h} {g} e h\n      cases m\n      · exact {decktT st0 x (NGrund.partner x false)}\n      · exact {decktT st1 x (NGrund.partner x true)}"
    | _ => "?"
  | .pool st =>
    match x.atome with
    | [_, h, g] => s!"fun e h => by\n      have hm := (m_6_0 true {h} {g} rfl e h).1\n      exact {decktT st x (NGrund.partner x true)}"
    | _ => "?"

/-- **The closing file**, or the open cells. `gut x` names the M witness of a good cell, `schl x` how N covers a bad
    cell; `mods` are the witness modules. -/
def schlussTextExplicit (gut : Zelle → Option String) (schl : Zelle → Option NGrund)
    (mSt nSt gSt : List String) (mods : List String) :
    Except (List Zelle) String :=
  let gutT := fun (x : Zelle) => match gut x with
    | some st => some s!"Or.inl ⟨{st}.e, by simp [Mw], {st}.e_hat _ (by decide)⟩"
    | none => unmoeglichGut x
  let schlT := fun (x : Zelle) => match unmoeglichSchlecht x with
    | some u => some s!"fun e h => absurd h ({u})"
    | none => (schl x).map (schlechtBeweisT x)
  let offen := zellAlle.filter fun x =>
    if x.schlecht then (schlT x).isNone else (gutT x).isNone
  if !offen.isEmpty then .error offen else
  let liste := String.intercalate ",\n    " (zellAlle.map Zelle.lean)
  let pat := String.intercalate " | " (zellAlle.map fun _ => "rfl")
  let erreicht := zellAlle.filter fun x => !x.schlecht && (gut x).isSome
  let erreichtPat := String.intercalate " | " (erreicht.map fun _ => "rfl")
  let gutTF := String.join (zellAlle.map fun x =>
    if x.schlecht then "  · exact absurd hs (by decide)\n" else s!"  · exact {(gutT x).getD "?"}\n")
  let schlTF := String.join (zellAlle.map fun x =>
    if x.schlecht then s!"  · exact {((schlT x).getD "?").replace "\n" "\n  "}\n" else "  · exact absurd hs (by decide)\n")
  let erreichtMF := String.join (erreicht.map fun x =>
    s!"  · exact ⟨{(gut x).getD "?"}.e, by simp [Mw], {(gut x).getD "?"}.e_hat _ (by decide)⟩\n")
  let mList := String.intercalate ", " (mSt.map (· ++ ".e"))
  let nList := String.intercalate ", " (nSt.map (· ++ ".e"))
  let mPat := String.intercalate " | " (mSt.map fun _ => "rfl")
  let nPat := String.intercalate " | " (nSt.map fun _ => "rfl")
  let gPat := String.intercalate " | " (gSt.map fun _ => "rfl")
  let gProof := String.join (gSt.map fun st =>
    s!"    · exact Gap.checked_gap {st}.e (by simp [Gap.fragmentGaps])\n")
  let gList := String.intercalate ", " (gSt.map (· ++ ".e"))
  let gapText := if gSt.isEmpty then "" else
    s!"/-- Fragment refusals are an annex, never wrong-program coverage. -/\ntheorem gap_annex : GapAnnex ([{gList}] : List Einsatz) where\n  refused g hg := by\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg\n    rcases hg with {gPat}\n{gProof}\n"
  let zeugenText :=
    s!"/-! ## The witnesses alone: M and N as explicit lists of programs of the source -/\n\n/-- **M**: witnesses with a full checker acceptance proof. -/\ndef Mw : List Einsatz := [{mList}]\n\n/-- **N**: wrong programs with structural model refusals. -/\ndef Nw : List Einsatz := [{nList}]\n\n" ++
    s!"theorem zeugen_m_akzeptiert : ∀ m ∈ Mw, m.gueltig = true := by\n  intro m hm\n  simp only [Mw, List.mem_cons, List.not_mem_nil, or_false] at hm\n" ++
      (if mSt.isEmpty then "" else s!"  rcases hm with {mPat}\n" ++
        String.join (mSt.map fun st => s!"  · exact {st}.e_gueltig\n")) ++ "\n" ++
    s!"theorem erreicht_mw : ∀ w ∈ erreicht, ∃ m ∈ Mw, m.Hat w := by\n  intro w hw\n  simp only [erreicht, List.mem_cons, List.not_mem_nil, or_false] at hw\n  rcases hw with {erreichtPat}\n{erreichtMF}\n" ++
    "/-- Every good cell is witnessed in accepted M, or impossible for valid source. -/\ntheorem zeugen_deckung : ∀ x ∈ zellAlle, x.schlecht = false →\n    (∃ m ∈ Mw, m.Hat x) ∨ (∀ e : Einsatz, e.Hat x → e.gueltig = false) := by\n" ++
    s!"  intro x hx hs\n  rw [zellAlle_liste] at hx\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx\n  rcases hx with {pat}\n{gutTF}\n" ++
    s!"theorem zeugen_n_abgelehnt : ∀ n ∈ Nw, n.gueltig = false := by\n  intro n hn\n  simp only [Nw, List.mem_cons, List.not_mem_nil, or_false] at hn\n  rcases hn with {nPat}\n" ++ String.join (nSt.map fun st => s!"  · exact {st}.e_gueltig\n") ++
    s!"\n/-- Bad-cell coverage is structural; it does not characterize semantic gate refusals. -/\ntheorem zeugen_schlecht_deckung : ∀ x ∈ zellAlle, x.schlecht = true → ∀ e : Einsatz, e.Hat x →\n    ∃ n ∈ Nw, ∀ w, n.Hat w → e.Hat w ∨ ∃ m ∈ Mw, m.Hat w := by\n  intro x hx hs\n  rw [zellAlle_liste] at hx\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx\n  rcases hx with {pat}\n{schlTF}\n" ++
    "\ntheorem zeugen_tafel : Tafel Mw Nw where\n  gut_m := zeugen_m_akzeptiert\n  gut := zeugen_deckung\n  n_schlecht := zeugen_n_abgelehnt\n  schlecht := zeugen_schlecht_deckung\n\n" ++
    "\n/-- **A neutral compiler correct on the witness list M is correct on every valid program of the source.** -/\ntheorem compiler_zeugen_korrekt (K : Einsatz → Prop) (hK : NeutralKorrekt K) (hM : ∀ m ∈ Mw, K m) (e : Einsatz)\n    (hv : e.gueltig = true) : K e := by\n  obtain ⟨ψ, hψ⟩ := hK\n  refine (hψ e).2 fun z hz => ?_\n  obtain ⟨m, hm, hmz⟩ := zellen_deckt zeugen_deckung e hv z hz\n  exact (hψ m).1 (hM m hm) z hmz\n\n"
  .ok (s!"/-\n  File:      Grammatik/Gen/Zeugen/Schluss.lean\n  Subject:   GENERATED (`gen-zellen-sammeln`, `ZellenSchluss.lean`): every cell of the universe has its reason, so\n             the accepted-program cell coverage yields the neutral compiler theorem. Do not edit.\n-/\n" ++
    "module\n" ++ String.join (mods.map fun m => s!"public import {m}\n") ++
    "public import Grammatik.Gen.Zeugen.Gap\npublic import Grammatik.Gen.Abdeckung.Satz.Neutral\npublic import Grammatik.Gen.Abdeckung.Satz.Unmoeglich\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace Gabbro.Grammatik.Gen.Zeugen\n\nopen Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz\n\n" ++
    s!"theorem zellAlle_liste : zellAlle = [\n    {liste}] := by decide\n\n" ++ gapText ++ zeugenText ++
    "end Gabbro.Grammatik.Gen.Zeugen\n")

/-- Ad-hoc caller: infer candidates once; production uses explicit lists. -/
def schlussText (gut : Zelle → Option String) (schl : Zelle → Option NGrund)
    (mods : List String) : Except (List Zelle) String :=
  let stems := fun pathPrefix => (mods.filter (·.startsWith pathPrefix)).map
    (·.drop pathPrefix.length |>.toString)
  schlussTextExplicit gut schl (stems "Grammatik.Gen.Zeugen.M.")
    (stems "Grammatik.Gen.Zeugen.N.") [] mods

end Gabbro.Grammatik.Gen
