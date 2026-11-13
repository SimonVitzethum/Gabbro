module

public import Grammatik.Logik.WP.BoundedWhile
public import Grammatik.Logik.Fortschritt.KostenG.BoundedWhile
public import Grammatik.Logik.Fortschritt.KostenG.T2.Teil2
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8a

@[expose] public section

namespace Gabbro.Grammatik.BoundedWhileWitness

abbrev V := vertragVon t4D t4F

/-- Reuse the populated three-cell declaration and machine-G fixture. -/
def index (k : Int) (hk : 0 ≤ k ∧ k ≤ 2) :
    Expr t4D [.bool] [] (.index (t4D.count ())) :=
  .widen hk.1 hk.2 (.lit k)

def value (k : Int) (hk : 0 ≤ k ∧ k ≤ 100) :
    Expr t4D [.bool] [] (t4D.typ () ()) :=
  .widen hk.1 hk.2 (.lit k)

/-- One pass writes a body marker, then either clears or retains the condition. -/
def body (finish : Bool) : Block t4D V true [.bool] [] [] :=
  .cons (.assignSlot () () (index 0 (by decide)) (value 5 (by decide)) rfl t4Darf)
    (.cons (.assignVar .here (if finish then .fls else .tru)) .nil)

/-- The exceeded handler writes a different cell, so taking it is observable. -/
def overflow : Block t4D V false [.bool] [] [] :=
  .cons (.assignSlot () () (index 1 (by decide)) (value 7 (by decide)) rfl t4Darf) .nil

def loop (finish : Bool) : Stmt t4D V false [.bool] [] [] :=
  .wloop 3 (.var .here) (body finish) overflow

def whole (finish : Bool) : Endblock t4D V false [] [] :=
  .bind .tru (.cons (loop finish) (.ret (.val (value 9 (by decide))) List.Perm.nil))

/-- Every function has the same signature; no calls, progress item or foreign
    assumption occur in these bodies. -/
def program (finish : Bool) : Programm t4D where
  invariante i := nomatch i
  requires _ := .tru
  ensures _ := .tru
  rumpf _ := whole finish

/-- The body and handler jointly satisfy the existing generic G coverage rule. -/
theorem whole_R (finish : Bool) (A : t4D.Lock → Prop) (C : t4D.Fn → Prop) :
    EndR A C (whole finish) := by
  exact EndR.bind _ _ (EndR.cons _ _
    (StmtR.retry _ _ _ _
      (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _))
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignVar _ _)) BlockR.nil))
      (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
    (EndR.ret _ _))

/-- A true initial condition executes one body pass, becomes false and exits
    with two passes left. The exceeded handler has not written its marker. -/
theorem early_exec_zeuge :
    ∃ (σ' : World t4D) (v : ErgVal t4D V.erg),
      execEnd t4O 0 (rufRumpf (program true) t4O 0 1) (whole true)
        ((t4M t4F (whole true)).weltVon 0) .nil = .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 0 ∧
      (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- A true condition surviving all three passes runs the handler, whose cell
    changes from zero to seven. Both branches perform actual body writes. -/
theorem exhausted_exec_zeuge :
    ∃ (σ' : World t4D) (v : ErgVal t4D V.erg),
      execEnd t4O 0 (rufRumpf (program false) t4O 0 1) (whole false)
        ((t4M t4F (whole false)).weltVon 0) .nil = .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧
      (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- Early termination through actual machine-G steps, including the frame pop.
    Generic adequacy transfers the concrete execution, rather than adding a
    separate loop evaluator or a program-specific execution rule. -/
theorem early_G_zeuge :
    ∃ M' : RufMaschineG t4D,
      RufLaufG (program true) t4O 0 0 (t4M t4F (whole true)) M' ∧
      (M'.speicher.slots () 0 ()).n = 5 ∧
      (M'.speicher.slots () 1 ()).n = 0 := by
  obtain ⟨σ', v, hex, h5, h0, _⟩ := early_exec_zeuge
  obtain ⟨M', _, hl, _, hsp, _⟩ := rufG_adaequat_ruf (program true) t4O 0 1
    (t4M t4F (whole true)) 0 t4F .nil (t4Sp.welt []) t4Unten [] [] [] .nil
    (whole true) (fun _ => False) (whole_R true _ _) rfl rfl t4_held
    (t4_frei t4F (whole true)) σ' v hex
  refine ⟨M', hl, ?_, ?_⟩
  · rw [hsp]
    exact h5
  · rw [hsp]
    exact h0

/-- Exhaustion and the handler's write through actual machine-G steps. The
    initial handler cell is zero, so seven witnesses that the handler ran. -/
theorem exhausted_G_zeuge :
    (t4Sp.slots () 1 ()).n = 0 ∧
    ∃ M' : RufMaschineG t4D,
      RufLaufG (program false) t4O 0 0 (t4M t4F (whole false)) M' ∧
      (M'.speicher.slots () 0 ()).n = 5 ∧
      (M'.speicher.slots () 1 ()).n = 7 := by
  refine ⟨rfl, ?_⟩
  obtain ⟨σ', v, hex, h5, h7, _⟩ := exhausted_exec_zeuge
  obtain ⟨M', _, hl, _, hsp, _⟩ := rufG_adaequat_ruf (program false) t4O 0 1
    (t4M t4F (whole false)) 0 t4F .nil (t4Sp.welt []) t4Unten [] [] [] .nil
    (whole false) (fun _ => False) (whole_R false _ _) rfl rfl t4_held
    (t4_frei t4F (whole false)) σ' v hex
  refine ⟨M', hl, ?_, ?_⟩
  · rw [hsp]
    exact h5
  · rw [hsp]
    exact h7

/-- The same static bound covers both paths, independently of outer passes or
    the callee cost table (there are no calls). Negation is included. -/
theorem kostenStmt_wloop_zeuge (finish : Bool) (cost : t4D.Fn → Nat) (passes : Nat) :
    kostenStmt cost passes (loop finish) = 25 ∧
      kostenEnd cost passes (whole finish) = 29 := by
  cases finish <;> exact ⟨rfl, rfl⟩

theorem wloop_scopesOk_zeuge (finish : Bool) :
    (loop finish).scopesOk [] none = true := by
  cases finish <;> rfl

/-- The inherited time theorem bounds actual G steps of either body by 29,
    including the final test and the possible handler. The frame enters with
    one caller beneath it and may pop only on the run's final step. -/
theorem frame_bound_zeuge (finish : Bool) {M' : RufMaschineG t4D}
    (run : SegLauf (program finish) t4O 0 (t4M t4F (whole finish)) M')
    (active : aktivVor 0 1 run) : segZaehle run 0 ≤ 29 := by
  have accepted : rufTief (program finish) 1 t4F = true := by
    cases finish <;> rfl
  have cost : kostenTief (program finish) 0 1 t4F = 29 := by
    cases finish <;> rfl
  have entry : Eintritt (program finish) 0 t4F .nil (t4Sp.welt []) 1
      (t4M t4F (whole finish)) := ⟨rfl, rfl⟩
  have bound := frame_schritte_beschraenkt (program finish) t4O 0 0 t4F 0
    accepted entry run active
  rw [cost] at bound
  exact bound

/-- Zero fuel checks the condition before selecting the handler: the false
    case preserves both cells and the true case performs the handler write. -/
theorem zero_fuel_zeuge :
    execStmt t4O 0 keinRuf (Stmt.wloop (V := V) (l := false) 0
      (.var .here) (body false) overflow) (t4Sp.welt []) (.cons false .nil) =
        .ok (t4Sp.welt []) (.cons false .nil) ∧
    ∃ σ' : World t4D,
      execStmt t4O 0 keinRuf (Stmt.wloop (V := V) (l := false) 0
        (.var .here) (body false) overflow) (t4Sp.welt []) (.cons true .nil) =
          .ok σ' (.cons true .nil) ∧ (σ'.slots () 1 ()).n = 7 :=
  ⟨rfl, _, rfl, rfl⟩

/-- Jointly satisfiable premises of the new WP rule: a live initial condition,
    a body that clears it, and a real handler proved unreachable by the invariant.
    No progress or measure premise is supplied. -/
theorem wpS_wloop_zeuge (σ0 : World t4D) :
    WP.wpS t4O 0 keinRuf
      (Stmt.wloop (V := V) (l := false) 3 (.var .here)
        (.cons (.assignVar .here .fls) .nil) overflow)
      (fun outcome => outcome = .ok σ0 (.cons false .nil)) σ0 (.cons true .nil) := by
  let I : Nat → World t4D → Env t4D [.bool] → Prop :=
    fun n σ ρ => σ = σ0 ∧ (ρ = .cons false .nil ∨ 0 < n)
  refine WP.wpS_wloop t4O 0 keinRuf 3 (.var .here)
    (.cons (.assignVar .here .fls) .nil) overflow _ I σ0 (.cons true .nil)
    ⟨rfl, Or.inr (by decide)⟩ ?_ ?_ ?_
  · intro n σ ρ hi hc
    rcases hi with ⟨rfl, _⟩
    cases ρ with
    | cons b tail =>
      cases tail
      change b = false at hc
      subst b
      rfl
  · intro σ ρ hi hc
    rcases hi.2 with hf | hn
    · subst ρ
      cases hc
    · omega
  · intro n σ ρ hi _
    cases ρ with
    | cons b tail =>
      cases tail
      change I n σ (.cons false .nil)
      exact ⟨hi.1, Or.inl rfl⟩

end Gabbro.Grammatik.BoundedWhileWitness
