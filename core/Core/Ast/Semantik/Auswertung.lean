module

public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- The frame relation for expression evaluation uses the resolved de Bruijn slot
    and carries the typed incoming value at every visible binding. -/
def Rahmen.traegt (frame : Rahmen) (env : Umgebung scope) : Prop :=
  ∀ {type} (ref : Local scope type), frame.lokale[ref.index]? = some (some ⟨type, env ref⟩)

def Rahmen.Schritt (code : List Befehl) (before after : Rahmen) : Prop :=
  ∃ b, before.rueckgabe = none ∧ code[before.pc]? = some b ∧ after = b.auswerten before

inductive Rahmen.Lauf (code : List Befehl) : Rahmen → Rahmen → Prop where
  | start : Lauf code frame frame
  | schritt : Lauf code before middle → Schritt code middle after → Lauf code before after

-- Generalise the original expr_ergebnis_typ proof to runtime PC walks and use Logic.skips.
theorem expr_ergebnis_typ (slot : Nat) (tree : Expr scope type) (env : Umgebung scope)
    (frame : Rahmen) (bound : frame.traegt env) (active : frame.rueckgabe = none)
    (atStart : frame.pc = 0) :
    ∃ out, Rahmen.Lauf (expr slot tree).code frame out ∧
      out.pc = (expr slot tree).code.length ∧ out.temp slot = some ⟨type, tree.wert env⟩ ∧
      out.lokale = frame.lokale ∧ out.rueckgabe = none ∧
      ∀ i, i < slot → out.temp i = frame.temp i := by
  have lookupSeq : ∀ (pre : List Befehl) (b : Befehl) (post : List Befehl),
      (pre ++ b :: post)[pre.length]? = some b := by
    intro pre b post
    rw [List.getElem?_append_right (by omega)]
    rw [Nat.sub_self]
    rfl
  have stepAt : ∀ (pre : List Befehl) (b : Befehl) (post : List Befehl) (frame : Rahmen),
      frame.rueckgabe = none → frame.pc = pre.length →
      Rahmen.Schritt (pre ++ b :: post) frame (b.auswerten frame) := by
    intro pre b post frame alive hpc
    refine ⟨b, alive, ?_, rfl⟩
    rw [hpc]
    exact lookupSeq pre b post
  have laufTrans : ∀ (code : List Befehl) {a b c : Rahmen},
      Rahmen.Lauf code a b → Rahmen.Lauf code b c → Rahmen.Lauf code a c := by
    intro code a b c hab hbc
    induction hbc with
    | start => exact hab
    | schritt _ step ih => exact .schritt ih step
  suffices H : ∀ (slot : Nat) {type : Ty .value} (tree : Expr scope type)
      (env : Umgebung scope) (frame : Rahmen) (bound : frame.traegt env)
      (active : frame.rueckgabe = none) (pre post : List Befehl) (hpc : frame.pc = pre.length),
      ∃ out, Rahmen.Lauf (pre ++ (expr slot tree).code ++ post) frame out ∧
        out.pc = pre.length + (expr slot tree).code.length ∧
        out.temp slot = some ⟨type, tree.wert env⟩ ∧
        out.lokale = frame.lokale ∧ out.rueckgabe = none ∧
        ∀ i, i < slot → out.temp i = frame.temp i by
    · obtain ⟨out, walk, pcEq, tmp, lok, ret, preserve⟩ :=
        H slot tree env frame bound active [] [] (by simpa only [List.length_nil] using atStart)
      refine ⟨out, ?_, ?_, tmp, lok, ret, preserve⟩
      · simpa only [List.nil_append, List.append_nil] using walk
      · simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using pcEq
  intro slot type tree
  induction tree generalizing slot
  case lit value =>
      intro env frame bound active pre post hpc
      let b : Befehl := .literal slot value
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.lit (scope := scope) value)).code ++ post)
          frame (b.auswerten frame) := by
        simpa only [b, expr, Fragment.einzel, List.append_assoc, List.singleton_append] using
          stepAt pre b post frame active hpc
      refine ⟨b.auswerten frame, .schritt .start step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, List.length_cons, List.length_nil, Nat.add_zero, hpc]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, Zahl.literal, Expr.wert]
      · rfl
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, active]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
  case trueLit =>
      intro env frame bound active pre post hpc
      let b : Befehl := .wahrheitswert slot true
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.trueLit : Expr scope .bool)).code ++ post)
          frame (b.auswerten frame) := by
        simpa only [b, expr, Fragment.einzel, List.append_assoc, List.singleton_append] using
          stepAt pre b post frame active hpc
      refine ⟨b.auswerten frame, .schritt .start step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, List.length_cons, List.length_nil, Nat.add_zero, hpc]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, active]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
  case falseLit =>
      intro env frame bound active pre post hpc
      let b : Befehl := .wahrheitswert slot false
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.falseLit : Expr scope .bool)).code ++ post)
          frame (b.auswerten frame) := by
        simpa only [b, expr, Fragment.einzel, List.append_assoc, List.singleton_append] using
          stepAt pre b post frame active hpc
      refine ⟨b.auswerten frame, .schritt .start step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, List.length_cons, List.length_nil, Nat.add_zero, hpc]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, active]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
  case binary op left right leftIH rightIH =>
      intro env frame bound active pre post hpc
      let L := (expr slot left).code
      let R := (expr (slot + 1) right).code
      let b : Befehl := .binaer op slot
      obtain ⟨mid, walkL, pcL, tmpL, lokL, retL, preserveL⟩ :=
        leftIH slot env frame bound active pre (R ++ [b] ++ post) hpc
      have boundMid : mid.traegt env := by
        intro ty ref
        rw [lokL]
        exact bound ref
      have hpcMid : mid.pc = (pre ++ L).length := by
        rw [List.length_append]
        exact pcL
      obtain ⟨mid2, walkR, pcR, tmpR, lokR, retR, preserveR⟩ :=
        rightIH (slot + 1) env mid boundMid retL (pre ++ L) ([b] ++ post) hpcMid
      have hpcMid2 : mid2.pc = (pre ++ L ++ R).length := by
        rw [List.length_append, List.length_append]
        rw [List.length_append] at pcR
        exact pcR
      have walkL' : Rahmen.Lauf (pre ++ (expr slot (Expr.binary op left right)).code ++ post)
          frame mid := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkL
      have walkR' : Rahmen.Lauf (pre ++ (expr slot (Expr.binary op left right)).code ++ post)
          mid mid2 := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkR
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.binary op left right)).code ++ post)
          mid2 (b.auswerten mid2) := by
        refine ⟨b, retR, ?_, rfl⟩
        simpa only [b, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
          List.singleton_append, hpcMid2, L, R] using
          (lookupSeq (pre ++ L ++ R) b post :
            ((pre ++ L ++ R) ++ b :: post)[(pre ++ L ++ R).length]? = some b)
      refine ⟨b.auswerten mid2, .schritt (laufTrans _ walkL' walkR') step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr,
          Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
          List.length_nil, Nat.add_zero, hpcMid2, L, R]
        omega
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl,
          alsGanzzahl, Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.pure_def, Ganzzahl.pack, tmpL, tmpR,
          preserveR slot (Nat.lt_succ_self slot), Arith.result, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, lokR, lokL]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, retR]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact (Function.update_of_ne (Nat.ne_of_lt hi) _ _).trans
          ((preserveR i (Nat.lt_trans hi (Nat.lt_succ_self slot))).trans (preserveL i hi))
  case _ ty ref visible ordinary =>
      intro env frame bound active pre post hpc
      let b : Befehl := .lesen slot ref.index
      have hb := bound (type := ty) ref
      have joined : frame.lokale[ref.index]?.join = some ⟨ty, env ref⟩ := by
        rw [hb]
        rfl
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.variable ref visible ordinary)).code ++ post)
          frame (b.auswerten frame) := by
        simpa only [b, expr, Fragment.einzel, List.append_assoc, List.singleton_append] using
          stepAt pre b post frame active hpc
      refine ⟨b.auswerten frame, .schritt .start step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, List.length_cons, List.length_nil, Nat.add_zero, hpc]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, joined, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, active]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
  case negativeLit magnitude =>
      intro env frame bound active pre post hpc
      let b : Befehl := .negativ slot magnitude
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.negativeLit (scope := scope) magnitude)).code ++ post)
          frame (b.auswerten frame) := by
        simpa only [b, expr, Fragment.einzel, List.append_assoc, List.singleton_append] using
          stepAt pre b post frame active hpc
      refine ⟨b.auswerten frame, .schritt .start step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, List.length_cons, List.length_nil, Nat.add_zero, hpc]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr, Fragment.einzel, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, active]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
  case neg operand operandIH =>
      intro env frame bound active pre post hpc
      let L := (expr slot operand).code
      let b : Befehl := .negieren slot
      obtain ⟨mid, walk, pcMid, tmpMid, lokMid, retMid, preserveMid⟩ :=
        operandIH slot env frame bound active pre ([b] ++ post) hpc
      have boundMid : mid.traegt env := by
        intro ty ref
        rw [lokMid]
        exact bound ref
      have hpcMid : mid.pc = (pre ++ L).length := by
        rw [List.length_append]
        exact pcMid
      have walk' : Rahmen.Lauf (pre ++ (expr slot (Expr.neg operand)).code ++ post) frame mid := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walk
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.neg operand)).code ++ post)
          mid (b.auswerten mid) := by
        simpa only [b, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
          List.singleton_append] using stepAt (pre ++ L) b post mid retMid hpcMid
      refine ⟨b.auswerten mid, .schritt walk' step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr,
          Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
          List.length_nil, Nat.add_zero, hpcMid, L]
        omega
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl,
          alsGanzzahl, Option.bind_some, Option.map_some, Ganzzahl.pack, tmpMid, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, lokMid]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, retMid]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact (Function.update_of_ne (Nat.ne_of_lt hi) _ _).trans (preserveMid i hi)
  case not operand operandIH =>
      intro env frame bound active pre post hpc
      let L := (expr slot operand).code
      let b : Befehl := .verneinen slot
      obtain ⟨mid, walk, pcMid, tmpMid, lokMid, retMid, preserveMid⟩ :=
        operandIH slot env frame bound active pre ([b] ++ post) hpc
      have boundMid : mid.traegt env := by
        intro ty ref
        rw [lokMid]
        exact bound ref
      have hpcMid : mid.pc = (pre ++ L).length := by
        rw [List.length_append]
        exact pcMid
      have walk' : Rahmen.Lauf (pre ++ (expr slot (Expr.not operand)).code ++ post) frame mid := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walk
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.not operand)).code ++ post)
          mid (b.auswerten mid) := by
        simpa only [b, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
          List.singleton_append] using stepAt (pre ++ L) b post mid retMid hpcMid
      refine ⟨b.auswerten mid, .schritt walk' step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr,
          Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
          List.length_nil, Nat.add_zero, hpcMid, L]
        omega
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, alsBoolean,
          Option.bind_some, Option.map_some, Option.map, tmpMid, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, lokMid]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, retMid]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact (Function.update_of_ne (Nat.ne_of_lt hi) _ _).trans (preserveMid i hi)
  case div left right nonzero leftIH rightIH =>
      intro env frame bound active pre post hpc
      let L := (expr slot left).code
      let R := (expr (slot + 1) right).code
      let b : Befehl := .teilen slot
      obtain ⟨mid, walkL, pcL, tmpL, lokL, retL, preserveL⟩ :=
        leftIH slot env frame bound active pre (R ++ [b] ++ post) hpc
      have boundMid : mid.traegt env := by
        intro ty ref
        rw [lokL]
        exact bound ref
      have hpcMid : mid.pc = (pre ++ L).length := by
        rw [List.length_append]
        exact pcL
      obtain ⟨mid2, walkR, pcR, tmpR, lokR, retR, preserveR⟩ :=
        rightIH (slot + 1) env mid boundMid retL (pre ++ L) ([b] ++ post) hpcMid
      have hpcMid2 : mid2.pc = (pre ++ L ++ R).length := by
        rw [List.length_append, List.length_append]
        rw [List.length_append] at pcR
        exact pcR
      have walkL' : Rahmen.Lauf (pre ++ (expr slot (Expr.div left right nonzero)).code ++ post)
          frame mid := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkL
      have walkR' : Rahmen.Lauf (pre ++ (expr slot (Expr.div left right nonzero)).code ++ post)
          mid mid2 := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkR
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.div left right nonzero)).code ++ post)
          mid2 (b.auswerten mid2) := by
        refine ⟨b, retR, ?_, rfl⟩
        simpa only [b, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
          List.singleton_append, hpcMid2, L, R] using
          (lookupSeq (pre ++ L ++ R) b post :
            ((pre ++ L ++ R) ++ b :: post)[(pre ++ L ++ R).length]? = some b)
      refine ⟨b.auswerten mid2, .schritt (laufTrans _ walkL' walkR') step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr,
          Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
          List.length_nil, Nat.add_zero, hpcMid2, L, R]
        omega
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl,
          alsGanzzahl, Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.pure_def, Ganzzahl.pack,
          tmpL, tmpR, preserveR slot (Nat.lt_succ_self slot), Arith.result,
          Zahl.div, dif_pos (by simpa only [Divisor] using nonzero), Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, lokR, lokL]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, retR]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact (Function.update_of_ne (Nat.ne_of_lt hi) _ _).trans
          ((preserveR i (Nat.lt_trans hi (Nat.lt_succ_self slot))).trans (preserveL i hi))
  case compare op left right leftIH rightIH =>
      intro env frame bound active pre post hpc
      let L := (expr slot left).code
      let R := (expr (slot + 1) right).code
      let b : Befehl := .vergleichen op slot
      obtain ⟨mid, walkL, pcL, tmpL, lokL, retL, preserveL⟩ :=
        leftIH slot env frame bound active pre (R ++ [b] ++ post) hpc
      have boundMid : mid.traegt env := by
        intro ty ref
        rw [lokL]
        exact bound ref
      have hpcMid : mid.pc = (pre ++ L).length := by
        rw [List.length_append]
        exact pcL
      obtain ⟨mid2, walkR, pcR, tmpR, lokR, retR, preserveR⟩ :=
        rightIH (slot + 1) env mid boundMid retL (pre ++ L) ([b] ++ post) hpcMid
      have hpcMid2 : mid2.pc = (pre ++ L ++ R).length := by
        rw [List.length_append, List.length_append]
        rw [List.length_append] at pcR
        exact pcR
      have walkL' : Rahmen.Lauf (pre ++ (expr slot (Expr.compare op left right)).code ++ post)
          frame mid := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkL
      have walkR' : Rahmen.Lauf (pre ++ (expr slot (Expr.compare op left right)).code ++ post)
          mid mid2 := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkR
      have step : Rahmen.Schritt (pre ++ (expr slot (Expr.compare op left right)).code ++ post)
          mid2 (b.auswerten mid2) := by
        refine ⟨b, retR, ?_, rfl⟩
        simpa only [b, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
          List.singleton_append, hpcMid2, L, R] using
          (lookupSeq (pre ++ L ++ R) b post :
            ((pre ++ L ++ R) ++ b :: post)[(pre ++ L ++ R).length]? = some b)
      refine ⟨b.auswerten mid2, .schritt (laufTrans _ walkL' walkR') step, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, expr,
          Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
          List.length_nil, Nat.add_zero, hpcMid2, L, R]
        omega
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl,
          alsGanzzahl, Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.pure_def, Ganzzahl.pack,
          tmpL, tmpR, preserveR slot (Nat.lt_succ_self slot), Arith.result,
          Zahl.div, Expr.wert]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, lokR, lokL]
      · simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe, retR]
      · intro i hi
        simp only [b, Function.update_self, Befehl.auswerten, Rahmen.schreibe]
        exact (Function.update_of_ne (Nat.ne_of_lt hi) _ _).trans
          ((preserveR i (Nat.lt_trans hi (Nat.lt_succ_self slot))).trans (preserveL i hi))
  case logic op left right leftIH rightIH =>
      intro env frame bound active pre post hpc
      let L := (expr slot left).code
      let R := (expr slot right).code
      let sw : Befehl := .springeWenn slot op.skips (R.length + 1)
      obtain ⟨mid, walkL, pcL, tmpL, lokL, retL, preserveL⟩ :=
        leftIH slot env frame bound active pre ([sw] ++ R ++ post) hpc
      have boundMid : mid.traegt env := by
        intro ty ref
        rw [lokL]
        exact bound ref
      have hpcMid : mid.pc = (pre ++ L).length := by
        rw [List.length_append]
        exact pcL
      have walkL' : Rahmen.Lauf (pre ++ (expr slot (Expr.logic op left right)).code ++ post)
          frame mid := by
        simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkL
      have stepSw : Rahmen.Schritt (pre ++ (expr slot (Expr.logic op left right)).code ++ post)
          mid (sw.auswerten mid) := by
        refine ⟨sw, retL, ?_, rfl⟩
        simpa only [sw, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
          List.singleton_append, hpcMid, L, R] using
          (lookupSeq (pre ++ L) sw (R ++ post) :
            ((pre ++ L) ++ sw :: (R ++ post))[(pre ++ L).length]? = some sw)
      by_cases htake : (left.wert env) = op.skips
      · refine ⟨sw.auswerten mid, .schritt walkL' stepSw, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [sw, Befehl.auswerten, expr, Fragment.anhaengen, Fragment.einzel, hpcMid, tmpL,
            alsBoolean, htake, if_pos rfl, if_true, List.length_append, List.length_cons,
            List.length_nil, Nat.add_zero, L, R]
          omega
        · simp only [sw, Befehl.auswerten, tmpL, alsBoolean, htake, if_pos rfl, if_true, Expr.wert]
        · simp only [sw, Befehl.auswerten, lokL]
        · simp only [sw, Befehl.auswerten, retL]
        · intro i hi
          simp only [sw, Befehl.auswerten]
          exact preserveL i hi
      · have hpcAfter : (sw.auswerten mid).pc = (pre ++ L ++ [sw]).length := by
          simp only [sw, Befehl.auswerten, hpcMid, tmpL, alsBoolean, htake, if_false]
          rw [List.length_append, List.length_append, List.length_cons, List.length_nil,
            Nat.add_zero]
        have boundAfter : (sw.auswerten mid).traegt env := by
          intro ty ref
          simp only [sw, Befehl.auswerten]
          rw [lokL]
          exact bound ref
        have retAfter : (sw.auswerten mid).rueckgabe = none := by
          simp only [sw, Befehl.auswerten, retL]
        obtain ⟨out, walkR, pcR, tmpR, lokR, retR, preserveR⟩ :=
          rightIH slot env (sw.auswerten mid) boundAfter retAfter (pre ++ L ++ [sw]) post hpcAfter
        have walkR' : Rahmen.Lauf (pre ++ (expr slot (Expr.logic op left right)).code ++ post)
            (sw.auswerten mid) out := by
          simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using walkR
        refine ⟨out, (laufTrans _ (.schritt walkL' stepSw) walkR'), ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [expr, Fragment.anhaengen, Fragment.einzel, List.length_append,
            List.length_cons, List.length_nil, Nat.add_zero, L, R] using pcR
        · rw [tmpR]
          simp only [Expr.wert, htake, if_false]
        · rw [lokR, lokL]
        · exact retR
        · exact preserveR

end Gabbro.Core.Ast.Semantik
