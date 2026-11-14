module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Level-4 goal: every `gutRuf` tree parses back from its
-- printed tokens with `brennstoff` fuel.
theorem parse_druck_ruf : ∀ (e : SExpr), gutRuf e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsRuf e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp only [brennstoff, Std.le_refl]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-4 witnesses, corpus-flavoured (`107-summe-zwei-rufe`
-- calls one function from another; `01-tabelle` wraps values
-- in `Some`): a one-argument call and a two-argument call, each
-- as a `parse_druck_ruf` instance and a kernel-computed `match`
-- check.
theorem zeuge_ruf_eins :
    parseOr (brennstoff (.call "f" [.variable "x"]))
    (druckToks (.call "f" [.variable "x"]) ++ [.ende]) =
      .ok (.call "f" [.variable "x"], [.ende]) :=
  parse_druck_ruf _ (by decide)
theorem zeuge_ruf_eins_rech : (match parseOr
    (brennstoff (.call "f" [.variable "x"]))
    (druckToks (.call "f" [.variable "x"]) ++ [.ende]) with
    | .ok (.call "f" [.variable "x"], [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_ruf_zwei :
    parseOr (brennstoff (.call "g" [.variable "x", .lit 1]))
    (druckToks (.call "g" [.variable "x", .lit 1]) ++ [.ende]) =
      .ok (.call "g" [.variable "x", .lit 1], [.ende]) :=
  parse_druck_ruf _ (by decide)
theorem zeuge_ruf_zwei_rech : (match parseOr
    (brennstoff (.call "g" [.variable "x", .lit 1]))
    (druckToks (.call "g" [.variable "x", .lit 1]) ++ [.ende]) with
    | .ok (.call "g" [.variable "x", .lit 1], [.ende]) => true
    | _ => false) = true := by
  decide

-- LEVEL BUILTINS (`sizeof`/`lenof`/`aligned` -- lane 161's
-- `prim_eingebaut` resisted there and was removed, not
-- weakened).
--
-- Index payloads of a kernel suffix chain are kernel trees.
theorem suffGutKern_idx : ∀ (suff : List SuffFrag) (i : SExpr),
    suffGutKern suff = true → .idx i ∈ suff → gutKern i = true := by
  intro suff
  induction suff with
  | nil =>
    intro i _ hm
    simp only [List.not_mem_nil] at hm
  | cons f s ih =>
    intro i hg hm
    cases f with
    | dot g =>
      simp only [suffGutKern] at hg
      simp only [List.mem_cons] at hm
      obtain h | h := hm
      · simp only [reduceCtorEq] at h
      · exact ih i hg h
    | arrow g =>
      simp only [suffGutKern] at hg
      simp only [List.mem_cons] at hm
      obtain h | h := hm
      · simp only [reduceCtorEq] at h
      · exact ih i hg h
    | idx j =>
      simp only [suffGutKern, Bool.and_eq_true] at hg
      obtain ⟨hj, hgs⟩ := hg
      simp only [List.mem_cons] at hm
      obtain h | h := hm
      · injection h with hjj
        subst hjj
        exact hj
      · exact ih i hgs h

-- Suffix chains through `parseSuffixe` with index payloads
-- parsed through kernel legs: lane 161's `suff_rund` (via
-- `kern_suff_rund`) with the `RKern` Or-leg replaced by
-- `legsKern`. No size bound threads through (payload legs
-- come straight from the predicate), so none is taken.
theorem suff_legs : ∀ (suff : List SuffFrag) (base : SExpr)
    (rest : List Token) (F : Nat),
    suffGutKern suff = true → ruhigSuff rest = true →
    12 * (suffGroesse suff + groesse base + 1) + suffGroesse suff ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) =
      .ok (applySuff base suff, rest) := by
  intro suff
  induction suff with
  | nil =>
    intro base rest F hg hr hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append] at ⊢
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro base rest F hg hr hF
      simp only [suffGutKern] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      have hstep : parseSuffixe (F' + 1) base
          (.zeichen "." :: nameTok f :: (suffToks suff ++ rest)) =
            parseSuffixe F' (.field base f) (suffToks suff ++ rest) := by
        unfold nameTok
        split <;> simp only [parseSuffixe, nameText]
      rw [hstep]
      simp only [applySuff] at ⊢
      have hF2 : 12 * (suffGroesse suff + groesse (.field base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hF ⊢
        omega
      exact ih (SExpr.field base f) rest F' hg hr hF2
    | arrow f =>
      intro base rest F hg hr hF
      simp only [suffGutKern] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      simp only [applySuff] at ⊢
      have hF2 : 12 * (suffGroesse suff + groesse (.arrow base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hF ⊢
        omega
      exact ih (SExpr.arrow base f) rest F' hg hr hF2
    | idx i =>
      intro base rest F hg hr hF
      simp only [suffGutKern, Bool.and_eq_true] at hg
      obtain ⟨hi, hgs⟩ := hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      have hki : gutKern i = true := hi
      have hLi := legsKern i hki
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hFi : 12 * (groesse i + 1) + groesse i + 8 ≤ F' := by
        simp only [suffGroesse] at hF ⊢
        omega
      have hOi := hLi.2.2.2.2.2.2.2
        ([.zeichen "]"] ++ suffToks suff ++ rest) F' hr1 hr2 hr3 hFi
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append] at ⊢
      simp only [applySuff] at ⊢
      have hF2 : 12 * (suffGroesse suff + groesse (.index base i) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hF ⊢
        omega
      exact ih (SExpr.index base i) rest F' hgs hr hF2

-- Kernel places through `parseOrt`: mirror of lane 161's
-- `ort_platz_all` (decompose by `zerlege_kern`, read the head,
-- run the chain by `suff_legs`).
theorem ort_legs_kern : ∀ (p : SExpr) (rest : List Token) (F : Nat),
    gutKernPlatz p = true → ruhigSuff rest = true →
    12 * (groesse p + 1) + groesse p ≤ F →
    parseOrt F (druckToks p ++ rest) = .ok (p, rest) := by
  intro p rest F hg hr hF
  obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ :=
    zerlege_kern (groesse p) p (Nat.le_refl _) hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rw [druckToks_applySuff] at ⊢
  have hkaf : istKeinPlatz a = false := kopf_kp (nichtWahr_falsch _ hka)
  simp only [parseOrt, druckToks, nameText_nameTok, hkaf, List.cons_append] at ⊢
  have hF2 : 12 * (suffGroesse suff + groesse (.variable a) + 1) +
      suffGroesse suff ≤ F' := by
    simp only [groesse, groesse_applySuff] at hF ⊢
    omega
  exact suff_legs suff (.variable a) rest F' hgs hr hF2

-- `parseEingebaut` with one argument is the `parseOrt` arm (the
-- `n == 1` test reduces definitionally); with two it is the
-- pair arm. Plain rewrite rules so the primary legs stay
-- mechanical.
theorem parseEingebaut_ein : ∀ (F : Nat) (w : String) (toks : List Token),
    parseEingebaut (F + 1) w 1 toks = match parseOrt F toks with
      | .ok (a, .zeichen ")" :: rest') => match a with
        | .variable s =>
          if istTypWort s then .error (w ++ " over a type")
          else .ok (.built w [a], rest')
        | _ => .ok (.built w [a], rest')
      | .ok (_, _) => .error (w ++ " without )")
      | .error e => .error e := by
  intro F w toks
  simp only [parseEingebaut]
  rfl
theorem parseEingebaut_zwei : ∀ (F : Nat) (w : String) (toks : List Token),
    parseEingebaut (F + 1) w 2 toks = match parseOr F toks with
      | .ok (a, .zeichen "," :: rest) => match parseOr F rest with
        | .ok (b, .zeichen ")" :: rest') =>
          .ok (.built w [a, b], rest')
        | .ok (_, _) => .error (w ++ " without )")
        | .error e => .error e
      | .ok (_, _) => .error (w ++ " without ,")
      | .error e => .error e := by
  intro F w toks
  simp only [parseEingebaut]
  rfl


end Gabbro.Grammatik.Parser
