module

public import Core.Ast.Semantik.Auswertung
public import Core.Ast.Program.Control

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Count semantic instructions, including a call, return or back-edge. -/
inductive Rahmen.LaufN (code : List Befehl) : Nat → Rahmen → Rahmen → Prop where
  | null : LaufN code 0 frame frame
  | step : before.stopp = none → before.rueckgabe = none →
      code[before.pc]? = some instruction →
      LaufN code n (instruction.auswerten before) after →
      LaufN code (n + 1) before after

def Binnen (code : List Befehl) (budget : Nat) (start : Rahmen) (goal : Rahmen → Prop) : Prop :=
  ∃ n out, n ≤ budget ∧ Rahmen.LaufN code n start out ∧ goal out

theorem Rahmen.LaufN.trans (left : Rahmen.LaufN code n first middle)
    (right : Rahmen.LaufN code m middle last) :
    Rahmen.LaufN code (n + m) first last := by
  induction left generalizing last m with
  | null => simpa only [Nat.zero_add] using right
  | step live returned head _ ih =>
    rw [Nat.add_right_comm _ 1 m]
    exact .step live returned head (ih right)

theorem Rahmen.LaufN.eins {first : Rahmen} (active : first.Aktiv) (lookup : code[first.pc]? = some instruction) :
    LaufN code 1 first (instruction.auswerten first) :=
  .step active.1 active.2 lookup .null

theorem Rahmen.LaufN.lauf (walk : Rahmen.LaufN code n first last) : Rahmen.Lauf code first last := by
  induction walk with
  | null => exact .start
  | step live returned head _ ih => exact Rahmen.Lauf.trans (.schritt .start ⟨_, live, returned, head, rfl⟩) ih

theorem Rahmen.Aktiv.ausdruck {first last : Rahmen} (active : first.Aktiv)
    (same : last = { first with pc := last.pc, temp := last.temp }) : last.Aktiv :=
  ⟨(congrArg Rahmen.stopp same).trans active.1, (congrArg Rahmen.rueckgabe same).trans active.2⟩

theorem Rahmen.traegt_ausdruck {first last : Rahmen} (typed : first.traegt env)
    (same : last = { first with pc := last.pc, temp := last.temp }) : last.traegt env := by
  intro type ref
  rw [congrArg Rahmen.lokale same]
  exact typed ref

theorem code_lookup (pre : List Befehl) (b : Befehl) (post : List Befehl)
    (atPC : pc = pre.length) : (pre ++ b :: post)[pc]? = some b := by
  rw [atPC, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem expression_lookup (pre code post : List Befehl) (pc : Nat)
    (lower : pre.length ≤ pc) (upper : pc < pre.length + code.length) :
    ∃ b, (pre ++ code ++ post)[pc]? = some b ∧ code[pc - pre.length]? = some b := by
  have inside : pc - pre.length < code.length := by omega
  refine ⟨code[pc - pre.length]'inside, ?_, getElem?_pos code (pc - pre.length) inside⟩
  rw [List.append_assoc, List.getElem?_append_right lower, List.getElem?_append_left inside]
  exact getElem?_pos code (pc - pre.length) inside

/-- Walk a condition at any address. Invalid operands may stop the frame. -/
theorem Ausdruckscode.laufN (shape : Ausdruckscode code) (pre post : List Befehl)
    (frame : Rahmen) (active : frame.Aktiv) (lo : pre.length ≤ frame.pc)
    (hi : frame.pc ≤ pre.length + code.length) :
    Binnen (pre ++ code ++ post) (pre.length + code.length - frame.pc) frame (fun out =>
      (out.pc = pre.length + code.length ∧ out = { frame with pc := out.pc, temp := out.temp }) ∨
        out.stopp.isSome = true) := by
  by_cases finished : frame.pc = pre.length + code.length
  · exact ⟨0, frame, Nat.zero_le _, .null, .inl ⟨finished, by cases frame; rfl⟩⟩
  have within : frame.pc < pre.length + code.length := by omega
  obtain ⟨b, lookup, localLookup⟩ := expression_lookup pre code post frame.pc lo within
  let next := b.auswerten frame
  rcases (shape _ b localLookup).2 frame with ⟨advances, stays, same⟩ | stopped
  · change frame.pc < next.pc at advances
    change next.pc ≤ frame.pc + (code.length - (frame.pc - pre.length)) at stays
    have nextLo : pre.length ≤ next.pc := by omega
    have nextHi : next.pc ≤ pre.length + code.length := by omega
    obtain ⟨n, out, bound, walk, outcome⟩ :=
      shape.laufN pre post next (active.ausdruck same) nextLo nextHi
    refine ⟨n + 1, out, by omega, .step active.1 active.2 lookup walk, ?_⟩
    rcases outcome with ⟨endPC, preserve⟩ | stop
    · exact .inl ⟨endPC,
        preserve.trans (congrArg (fun f : Rahmen => { f with pc := out.pc, temp := out.temp }) same)⟩
    · exact .inr stop
  · refine ⟨1, next, by omega, .eins active lookup, .inr ?_⟩
    rw [show next = frame.halt .ungueltigerWert from stopped]
    rfl
termination_by pre.length + code.length - frame.pc
decreasing_by omega

private theorem Rahmen.Lauf.ausdrucksLaenge (shape : Ausdruckscode code)
    (walk : Rahmen.Lauf (pre ++ code) first last)
    (entry : pre.length ≤ first.pc) (suffix : List Befehl) (finalActive : last.Aktiv) :
    ∃ n, first.pc ≤ last.pc ∧ n ≤ last.pc - first.pc ∧
      Rahmen.LaufN (pre ++ code ++ suffix) n first last ∧
      last = { first with pc := last.pc, temp := last.temp } := by
  revert finalActive
  induction walk with
  | start => intro _; exact ⟨0, Nat.le_refl _, Nat.zero_le _, .null, by cases first; rfl⟩
  | @schritt middle last _ step ih =>
    intro finalActive
    obtain ⟨b, live, returned, head, rfl⟩ := step
    obtain ⟨n, forward, budget, counted, preserved⟩ := ih ⟨live, returned⟩
    have lo := Nat.le_trans entry forward
    have lookup := head
    rw [List.getElem?_append_right lo] at lookup
    have stepShape := (shape _ b lookup).2 middle
    have advancesAndPreserved := stepShape.resolve_right (fun stopped => by
      have liveAfter := finalActive.1
      rw [stopped] at liveAfter
      cases liveAfter)
    obtain ⟨advances, _, onlyExpr⟩ := advancesAndPreserved
    have inCode := (List.getElem?_eq_some_iff.mp head).1
    have head' : (pre ++ code ++ suffix)[middle.pc]? = some b :=
      (List.getElem?_append_left inCode).trans head
    refine ⟨n + 1, by omega, by omega,
      counted.trans (.step live returned head' .null), ?_⟩
    let out := b.auswerten middle
    exact onlyExpr.trans (congrArg (fun frame : Rahmen => { frame with pc := out.pc, temp := out.temp }) preserved)

/-- The typed expression walk preserves lower temporary slots as well as the
    frame fields outside the program counter and temporaries. -/
theorem expr_laufN_am (slot : Nat) (tree : Expr scope type) (env : Umgebung scope)
    (frame : Rahmen) (typed : frame.traegt env) (active : frame.Aktiv)
    (pre post : List Befehl) (entry : frame.pc = pre.length)
    (checked : frame.WaechterHalten (pre ++ (expr slot tree).code ++ post)) :
    Binnen (pre ++ (expr slot tree).code ++ post) (expr slot tree).code.length frame (fun out =>
      out.pc = pre.length + (expr slot tree).code.length ∧ out.temp slot = some ⟨type, tree.wert env⟩ ∧
        out = { frame with pc := out.pc, temp := out.temp } ∧
        ∀ i, i < slot → out.temp i = frame.temp i) := by
  obtain ⟨out, trace, value⟩ :=
    expr_ergebnis_typ_am slot tree env frame typed active pre [] entry
      (by simpa only [List.append_nil] using checked.prefix)
  have walk : Rahmen.Lauf (pre ++ (expr slot tree).code) frame out := by
    simpa only [List.append_nil] using trace.walk
  have entryLe : pre.length ≤ frame.pc := by rw [entry]
  obtain ⟨n, _, budget, counted, preserved⟩ :=
    walk.ausdrucksLaenge (expr_ausdruckscode slot tree) entryLe post (trace.aktiv active)
  have atEnd := trace.position
  exact ⟨n, out, by omega, counted, atEnd, value, preserved, trace.lower⟩

/-- Expression evaluation starts at zero and leaves following code untouched. -/
theorem expr_laufN (slot : Nat) (tree : Expr scope type) (env : Umgebung scope)
    (frame : Rahmen) (typed : frame.traegt env) (active : frame.Aktiv) (entry : frame.pc = 0)
    (suffix : List Befehl) (checked : frame.WaechterHalten ((expr slot tree).code ++ suffix)) :
    Binnen ((expr slot tree).code ++ suffix) (expr slot tree).code.length frame (fun out =>
      out.pc = (expr slot tree).code.length ∧ out.temp slot = some ⟨type, tree.wert env⟩ ∧
        out = { frame with pc := out.pc, temp := out.temp }) := by
  obtain ⟨n, out, bound, walk, endPC, tmp, preserved, _⟩ :=
    expr_laufN_am slot tree env frame typed active [] suffix entry
      (by simpa only [List.nil_append] using checked)
  exact ⟨n, out, bound, by simpa only [List.nil_append] using walk,
    by simpa only [List.length_nil, Nat.zero_add] using endPC, tmp, preserved⟩

end Gabbro.Core.Ast.Semantik
