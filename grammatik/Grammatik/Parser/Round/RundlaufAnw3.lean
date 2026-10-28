/-
  File:      Grammatik/Parser/Round/RundlaufAnw3.lean
  Subject:   Track P: the statement round trip, part three -- a statement list and a block.

  `rundlauf_block_einfach`: a block whose statements are all `Einfach` (return, leave, next, number `let`
  over `gutPrim` expressions) and whose ender is one of those prints and reads back through `parseBlock`
  as the same tree, with the fuel of `fuelListe`, whatever follows the closing brace. The hypothesis
  `EndeGut` is the one the reader forces: a block without an ender must not END in a `return`/`leave`/`next`
  statement, because `schliesseBlock` would read that last statement as the ender
  (`schliesse_ende_noetig` shows the planted defect).
-/
import Grammatik.Parser.Round.RundlaufAnw2

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- The fuel of a statement list: each statement, one step, and the closing `}` check. -/
def fuelListe : List SAnw → Nat
  | [] => 0
  | s :: ss => fuelAnw s + 1 + fuelListe ss

/-- The statement a block ender stands for. -/
def endeAnw : Option SEnde → List SAnw
  | none => []
  | some (.ret x) => [.ret x]
  | some (.leave l) => [.leave l]
  | some (.next l) => [.next l]

theorem druckAnwListe_append : ∀ (a b : List SAnw),
    druckAnwListe (a ++ b) = druckAnwListe a ++ druckAnwListe b := by
  intro a b
  induction a with
  | nil => rfl
  | cons s ss ih => simp only [List.cons_append, druckAnwListe, ih, List.append_assoc]

theorem druckEnde_eq : ∀ (e : Option SEnde), druckEnde e = druckAnwListe (endeAnw e) := by
  intro e
  cases e with
  | none => rfl
  | some e' =>
    cases e' with
    | ret x => cases x <;> simp only [druckEnde, endeAnw, druckAnwListe, druckAnw, List.append_nil, List.cons_append, List.nil_append]
    | leave l => simp only [druckEnde, endeAnw, druckAnwListe, druckAnw, List.append_nil]
    | next l => simp only [druckEnde, endeAnw, druckAnwListe, druckAnw, List.append_nil]

/-- The ender is one of the simple statements. -/
def EinfachEnde : Option SEnde → Prop
  | none => True
  | some (.ret none) => True
  | some (.ret (some e)) => gutPrim e = true
  | some (.leave _) => True
  | some (.next _) => True

theorem einfach_ende : ∀ (e : Option SEnde), EinfachEnde e → ∀ s ∈ endeAnw e, Einfach s := by
  intro e he s hs
  cases e with
  | none => simp only [endeAnw, List.not_mem_nil] at hs
  | some e' =>
    cases e' with
    | ret x =>
      cases x with
      | none => simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs; exact Einfach.retLeer
      | some y => simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs; exact Einfach.ret y he
    | leave l => simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs; exact Einfach.leave l
    | next l => simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs; exact Einfach.next l

/-- A statement that `schliesseBlock` takes for an ender. -/
def istEnder : SAnw → Bool
  | .ret _ => true
  | .leave _ => true
  | .next _ => true
  | _ => false

/-- A block without an ender does not end in an ender statement. -/
def EndeGut (ss : List SAnw) (e : Option SEnde) : Prop :=
  e = none → ∀ s, ss.getLast? = some s → istEnder s = false

/-- A simple statement starts with a keyword and goes on with a fixed tail. -/
theorem druckAnw_kopf (s : SAnw) (hs : Einfach s) :
    ∃ (w : String) (ts : List Token), ∀ r, druckAnw s ++ r = .wort w :: (ts ++ r) := by
  cases hs with
  | retLeer => exact ⟨"return", [.zeichen ";"], fun r => by simp only [druckAnw, List.cons_append, List.nil_append]⟩
  | ret e hg => exact ⟨"return", druckToks e ++ [.zeichen ";"], fun r => by simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]⟩
  | leave l => exact ⟨"leave", [nameTok l, .zeichen ";"], fun r => by simp only [druckAnw, List.cons_append, List.nil_append]⟩
  | next l => exact ⟨"next", [nameTok l, .zeichen ";"], fun r => by simp only [druckAnw, List.cons_append, List.nil_append]⟩
  | bind x e _ hg =>
    exact ⟨"let", [nameTok x, .zeichen "="] ++ druckToks e ++ [.zeichen ";"],
      fun r => by simp only [druckAnw, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append,
  druckTypOpt, List.append_assoc]⟩

/-- **A statement list reads back** (up to the closing `}`). -/
theorem parseStmts_einfach : ∀ (ss : List SAnw), (∀ s ∈ ss, Einfach s) → ∀ (r : List Token) (F : Nat),
    fuelListe ss + 1 ≤ F →
    parseStmts F (druckAnwListe ss ++ .zeichen "}" :: r) = .ok (ss, .zeichen "}" :: r) := by
  intro ss
  induction ss with
  | nil =>
    intro _ r F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseStmts, druckAnwListe, List.nil_append]
  | cons s ss ih =>
    intro hs r F hF
    have hs0 : Einfach s := hs s (List.mem_cons_self ..)
    have hss : ∀ s' ∈ ss, Einfach s' := fun s' h => hs s' (List.mem_cons_of_mem _ h)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hl : fuelListe (s :: ss) = fuelAnw s + 1 + fuelListe ss := rfl
    have hStmt : parseStmt F' (druckAnw s ++ (druckAnwListe ss ++ .zeichen "}" :: r)) =
        .ok (s, druckAnwListe ss ++ .zeichen "}" :: r) :=
      parseStmt_einfach s hs0 _ F' (by omega)
    have hRest := ih hss r F' (by omega)
    obtain ⟨w, ts, hw⟩ := druckAnw_kopf s hs0
    have hd : druckAnwListe (s :: ss) ++ .zeichen "}" :: r =
        .wort w :: (ts ++ (druckAnwListe ss ++ .zeichen "}" :: r)) := by
      rw [← hw (druckAnwListe ss ++ .zeichen "}" :: r)]
      simp only [druckAnwListe, List.append_assoc]
    rw [hd]
    simp only [parseStmts]
    rw [← hw, hStmt]
    simp only [hRest]

/-- **A block reads back.** -/
theorem rundlauf_block_einfach (ss : List SAnw) (e : Option SEnde)
    (hs : ∀ s ∈ ss, Einfach s) (he : EinfachEnde e) (hw : EndeGut ss e)
    (r : List Token) (F : Nat) (hF : fuelListe (ss ++ endeAnw e) + 2 ≤ F) :
    parseBlock F (druckAnw (.block ss e) ++ r) = .ok (.block ss e, r) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hall : ∀ s ∈ ss ++ endeAnw e, Einfach s := by
    intro s hm
    rcases List.mem_append.mp hm with h | h
    · exact hs s h
    · exact einfach_ende e he s h
  have hP := parseStmts_einfach (ss ++ endeAnw e) hall r F' (by omega)
  have hd : druckAnw (.block ss e) ++ r =
      .zeichen "{" :: (druckAnwListe (ss ++ endeAnw e) ++ .zeichen "}" :: r) := by
    simp only [druckAnw, List.cons_append, List.nil_append, druckEnde_eq, List.append_assoc, druckAnwListe_append]
  rw [hd]
  simp only [parseBlock, fordereZeichen, strEq_self, if_true, hP]
  -- the closing brace, then the shape of the block
  have hS : schliesseBlock (ss ++ endeAnw e) = .block ss e := by
    cases e with
    | none =>
      simp only [endeAnw, List.append_nil]
      cases ss with
      | nil => rfl
      | cons s ss' =>
        have hl := hw rfl
        simp only [schliesseBlock]
        cases hg : (s :: ss').getLast? with
        | none => rfl
        | some x =>
          have hx := hl x hg
          cases x <;> simp_all [istEnder]
    | some e' =>
      cases e' with
      | ret x => simp only [schliesseBlock, endeAnw, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self,
  List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
      | leave l => simp only [schliesseBlock, endeAnw, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self,
  List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
      | next l => simp only [schliesseBlock, endeAnw, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self,
  List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
  simp only [hS]

/-- **Witness**: a non-degenerate block (a `let`, a `leave`, a valued `return`) meets every hypothesis, so the
    theorem is not vacuous. -/
theorem rundlauf_block_einfach_zeuge (r : List Token) :
    parseBlock 200 (druckAnw (.block [.bind false "x" none (.lit 1), .leave "i"]
        (some (.ret (some (.variable "x"))))) ++ r) =
      .ok (.block [.bind false "x" none (.lit 1), .leave "i"] (some (.ret (some (.variable "x")))), r) :=
  rundlauf_block_einfach _ _
    (by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact Einfach.bind "x" (.lit 1) (by decide) (by decide)
      · exact Einfach.leave "i")
    (by simp only [EinfachEnde]; decide) (by intro h; simp only [reduceCtorEq] at h) r 200 (by decide)

/-- **Planted defect**: a block without an ender that ENDS in a `return` reads back with that `return` as its
    ender -- the hypothesis `EndeGut` of the theorem is necessary. -/
theorem schliesse_ende_noetig :
    beqTopBlock (parseTopBlock (druckAnw (.block [.ret none] none) ++ [.ende]))
      (.ok (.block [.ret none] none)) = false := by
  decide +kernel

#print axioms Gabbro.Grammatik.Parser.parseStmt_einfach
#print axioms Gabbro.Grammatik.Parser.parseStmts_einfach
#print axioms Gabbro.Grammatik.Parser.rundlauf_block_einfach
#print axioms Gabbro.Grammatik.Parser.rundlauf_block_einfach_zeuge
#print axioms Gabbro.Grammatik.Parser.schliesse_ende_noetig

end Gabbro.Grammatik.Parser
