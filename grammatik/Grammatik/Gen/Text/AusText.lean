/-
  File:      Grammatik/Gen/Text/AusText.lean
  Subject:   A SOURCE TEXT AS A PROGRAM OF THE SOURCE (`Einsatz`): the Lean pipeline (`uebersetzeAllg`: lex, parse,
             preprocess, elaborate, lower onto `declOf u`) and the construction of the `Einsatz` over the declaration it
             built -- the complete enumerations (`aufzU`), the lock family of the source (`sperreU`: each lock protects
             exactly the carriers it guards), the full lists of functions, locks and carriers, the declared starts (the
             `concurrent` members, then the entry dispatch roots: `Starts.roots`), and the two decided fields: every body
             derives its floor (`hBoden`) and the unit has no foreign body (`keinAx`), each checked and an error
             otherwise.

  `ausItems` is the same from parsed items (no lexer, no parser); `ausText_druck`: on the rendered print of printable
  items `ausText` IS `ausItems` -- proved by the syntax round trip (`lex_render`, `parseTopTief_druck`), so a kernel
  check of a printed program never runs the lexer.
-/
import Grammatik.Gen.Text.Delab
import Grammatik.Parser.Elab.UebersetzePipeline

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The complete enumerations of the declaration of an elaborated unit. -/
instance aufzU (u : UProg) : Aufz (declOf u) where
  tab := List.finRange u.tabs.length
  tab_mem := fun t => List.mem_finRange t
  feld := fun t => List.finRange (fieldCount u t)
  feld_mem := fun _ f => List.mem_finRange f
  glob := List.finRange u.globs.length
  glob_mem := fun g => List.mem_finRange g
  lock := List.finRange u.locks.length
  lock_mem := fun L => List.mem_finRange L
  marke := []
  marke_mem := fun m => nomatch m
  fn := List.finRange u.fns.length
  fn_mem := fun f => List.mem_finRange f
  inv := List.finRange u.invs.length
  inv_mem := fun i => List.mem_finRange i
  ax := List.finRange u.axs.length
  ax_mem := fun a => List.mem_finRange a
  reg := List.finRange u.regs.length
  reg_mem := fun r => List.mem_finRange r
  annahme := none :: (List.finRange u.annahmen.length).map some
  annahme_mem := fun a => by
    cases a with
    | none => exact List.mem_cons_self
    | some i => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
  decFn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  decInv := inferInstanceAs (DecidableEq (Fin u.invs.length))
  decAx := inferInstanceAs (DecidableEq (Fin u.axs.length))
  decReg := inferInstanceAs (DecidableEq (Fin u.regs.length))
  decAnnahme := inferInstanceAs (DecidableEq (Option (Fin u.annahmen.length)))

/-- The carriers of an elaborated unit: the tables, then the statics. -/
def traegerU (u : UProg) : List ((declOf u).Tab ⊕ (declOf u).Glob) :=
  (List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr

/-- The lock family of the source: lock `L` protects every carrier it guards. -/
def sperreU (u : UProg) : SperrInv (declOf u) where
  orte := fun L => (traegerU u).filter fun c => decide (L ∈ waechterVon c)
  inv := fun _ _ => true

/-- A fixed numeric scheme (the cells and the verdict do not read it). -/
def zahlenFest : Zahlen := Spez.zahlen {}

/-- **The program of the source** an elaborated and lowered unit is. -/
def mkEinsatz (u : UProg) (P : Programm (declOf u)) : Except String Einsatz :=
  if hb : (List.finRange u.fns.length).all
      (fun f => @Programm.bodenP (declOf u) (aufzU u) P f == ((declOf u).signatur f).boden) = true then
  if ha : u.axs.length = 0 then
    .ok { D := declOf u
          aufz := aufzU u
          zahlen := zahlenFest
          P := P
          S := sperreU u
          fs := List.finRange u.fns.length
          ls := List.finRange u.locks.length
          cs := traegerU u
          ws := (startsOf u).roots
          hvoll := List.mem_finRange
          hls := List.mem_finRange
          hcs := fun
            | .inl t => List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_finRange _, rfl⟩)
            | .inr g => List.mem_append_right _ (List.mem_map.2 ⟨g, List.mem_finRange _, rfl⟩)
          hS := fun L c => by
            simp only [sperreU, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
            intro _
            cases c with
            | inl t => exact List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_finRange _, rfl⟩)
            | inr g => exact List.mem_append_right _ (List.mem_map.2 ⟨g, List.mem_finRange _, rfl⟩)
          hBoden := fun f => by
            have := (List.all_eq_true.1 hb) f (List.mem_finRange f)
            simpa using this
          keinAx := fun a => by
            have := (show Fin u.axs.length from a).isLt
            omega }
  else .error "a foreign body: outside the test sets"
  else .error "a body does not derive its floor"

/-- **A source text as a program of the source.** -/
def ausText (s : String) : Except String Einsatz :=
  match uebersetzeMitStarts s with
  | .error e => .error e
  | .ok ⟨u, P, _, _⟩ => mkEinsatz u P

/-- The same from parsed items. -/
def ausItems (its : List SItemTief) : Except String Einsatz :=
  match elabU (pre108 its) with
  | .error e => .error e
  | .ok u =>
    match lowerAllg u with
    | .error e => .error e
    | .ok (P, _) => mkEinsatz u P

/-- **On the rendered print of printable items, the text reader is the item reader**: the lexer reads the
    rendered tokens back (`lex_render`) and the program reader the items (`parseTopTief_druck`). -/
theorem ausText_druck (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it)
    (ht : ∀ t ∈ druckItems its, TokGut t) :
    ausText (renderText (druckItems its)) = ausItems its := by
  unfold ausText uebersetzeMitStarts uebersetzeAllg ausItems
  rw [lex_render _ ht]
  simp only
  rw [parseTopTief_druck its h]
  simp only
  cases elabU (pre108 its) with
  | error e => rfl
  | ok u =>
    simp only
    cases lowerAllg u with
    | error e => rfl
    | ok p => rfl

end Gabbro.Grammatik.Gen.Text
