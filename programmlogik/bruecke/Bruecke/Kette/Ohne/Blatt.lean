module
public import Bruecke.Kette.Ende.Simulation
@[expose] public section

/-!
# Lowered leaves contain no `locks`

The statements the reader carries one by one (`LeseEinzeln`), the returns at the top of a body
(no lexically held lock: `pe = []`) and the loop controls lower to G statements and ending blocks
that are not `locks` blocks and not scoped returns. These are the leaves of the induction in
`Kette/Ohne/Seq.lean`, `Ende.lean` and `Lauf.lean`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

/-- Close every branch of an unfolded leaf lowering: an error branch is impossible, an
    `ok` branch names a statement constructor without a nested block. -/
local macro "ohne_blatt" h:ident : tactic => `(tactic| (
  repeat' (first
    | split at $h:ident
    | (simp only [bind, Except.bind, pure, Except.pure] at $h:ident))
  all_goals first
    | (cases $h:ident; done)
    | (cases $h:ident; first | rfl | with_unfolding_all rfl)))

theorem lowSetVarL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {x : String}
    {v : USide} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowSetVarL (l := l) u c Γ fn Λ x v = .ok st) : st.ohneLocks = true := by
  unfold lowSetVarL at h
  ohne_blatt h

theorem lowSetVarBL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {x : String}
    {v : UEns} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowSetVarBL (l := l) u c Γ fn Λ x v = .ok st) : st.ohneLocks = true := by
  unfold lowSetVarBL at h
  ohne_blatt h

theorem lowSetVarOptL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {x : String}
    {num : Nat} {o : UOpt} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowSetVarOptL (l := l) u c Γ fn Λ x num o = .ok st) : st.ohneLocks = true := by
  unfold lowSetVarOptL at h
  ohne_blatt h

theorem lowAssignDurchL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {b f : String} {ix : UIdx} {v : USide} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowAssignDurchL (l := l) u c Γ fn Λ b f ix v = .ok st) : st.ohneLocks = true := by
  unfold lowAssignDurchL at h
  ohne_blatt h

theorem lowAssignTabL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {b f : String} {ix : UIdx} {v : USide} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowAssignTabL (l := l) u c Γ fn Λ b f ix v = .ok st) : st.ohneLocks = true := by
  unfold lowAssignTabL at h
  ohne_blatt h

theorem lowAssignDurchOL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {b f : String} {ix : UIdx} {v : UOpt} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowAssignDurchOL (l := l) u c Γ fn Λ b f ix v = .ok st) : st.ohneLocks = true := by
  unfold lowAssignDurchOL at h
  ohne_blatt h

theorem lowAssignTabOL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {b f : String} {ix : UIdx} {v : UOpt} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowAssignTabOL (l := l) u c Γ fn Λ b f ix v = .ok st) : st.ohneLocks = true := by
  unfold lowAssignTabOL at h
  ohne_blatt h

theorem lowAssignGlobL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {n : String} {v : USide} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowAssignGlobL (l := l) u c Γ fn Λ n v = .ok st) : st.ohneLocks = true := by
  unfold lowAssignGlobL at h
  ohne_blatt h

theorem lowAssignGlobBL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {n : String} {v : UEns} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowAssignGlobBL (l := l) u c Γ fn Λ n v = .ok st) : st.ohneLocks = true := by
  unfold lowAssignGlobBL at h
  ohne_blatt h

theorem lowCallL_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ Λ' : List (Res (declOf u))}
    {cname : String} {args : List UArg} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ'}
    (h : lowCallL (l := l) u c Γ fn Λ cname args = .ok ⟨Λ', st⟩) : st.ohneLocks = true := by
  unfold lowCallL at h
  ohne_blatt h

/-- Push a leaf lowering through `Except.map` into a dependent pair. -/
theorem ohne_map {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res (declOf u))}
    {r : Except String (Stmt (declOf u) (verOf u c) l Γ Λ Λ)}
    {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ'}
    (h : r.map (fun st => (⟨Λ, st⟩ : Σ Λ', Stmt (declOf u) (verOf u c) l Γ Λ Λ')) = .ok ⟨Λ', st⟩)
    (hr : ∀ st, r = .ok st → st.ohneLocks = true) : st.ohneLocks = true := by
  cases hx : r with
  | error e => rw [hx] at h; cases h
  | ok s =>
    rw [hx] at h
    cases h
    exact hr s hx

/-- **A carried single statement lowers without `locks`.** -/
theorem lowStmtL_einzeln_ohne {l : Bool} (hT : TabEindeutig u) {Γ : Ctx} {fn : UFn}
    {Λ Λ' : List (Res (declOf u))} {s : UStmt} {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ'}
    (hs : LeseEinzeln s) (h : lowStmtL (l := l) u c Γ fn Λ s = .ok ⟨Λ', st⟩) :
    st.ohneLocks = true := by
  cases s
  case setVar x v => exact ohne_map h (fun _ h => lowSetVarL_ohne h)
  case setVarB x v => exact ohne_map h (fun _ h => lowSetVarBL_ohne h)
  case setVarOpt x num v => exact ohne_map h (fun _ h => lowSetVarOptL_ohne h)
  case assign b f i v =>
    rw [lowStmtL_assign hT] at h
    exact ohne_map h (fun _ h => lowAssignDurchL_ohne h)
  case assignTab b f i v =>
    rw [lowStmtL_assignTab hT] at h
    exact ohne_map h (fun _ h => lowAssignTabL_ohne h)
  case assignOpt b f i v => exact ohne_map h (fun _ h => lowAssignDurchOL_ohne h)
  case assignTabOpt b f i v => exact ohne_map h (fun _ h => lowAssignTabOL_ohne h)
  case assignGlob n v => exact ohne_map h (fun _ h => lowAssignGlobL_ohne h)
  case assignGlobB n v => exact ohne_map h (fun _ h => lowAssignGlobBL_ohne h)
  case call cname args => exact lowCallL_ohne h
  all_goals exact hs.elim

/-- A return at the top of a body (no lexically held lock) is not a scoped return. -/
theorem lowRetStmt_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {r : URet}
    {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowRetStmt (l := l) u c Γ fn Λ [] r = .ok st) : st.ohneLocks = true := by
  simp only [lowRetStmt] at h
  split at h
  · ohne_blatt h
  · cases he : lowErg u c Γ Λ fn _ with
    | error e => rw [he] at h; cases h
    | ok e =>
      rw [he] at h
      simp only [Except.bind] at h
      ohne_blatt h

theorem lowRetEnd_ohne {l : Bool} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {r : URet}
    {st : Endblock (declOf u) (verOf u c) l Γ Λ}
    (h : lowRetEnd (l := l) u c Γ fn Λ [] r = .ok st) : st.ohneLocks = true := by
  simp only [lowRetEnd] at h
  split at h
  · ohne_blatt h
  · cases he : lowErg u c Γ Λ fn _ with
    | error e => rw [he] at h; cases h
    | ok e =>
      rw [he] at h
      simp only [Except.bind] at h
      ohne_blatt h

theorem lowEnd_ohne {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {r : URet}
    {st : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEnd u c Γ Λ fn r = .ok st) : st.ohneLocks = true := by
  unfold lowEnd at h
  cases r
  all_goals (try (generalize (keinsWert (fnAt u c).ergTy).getD URet.keins = r' at h; cases r'))
  all_goals (try simp only at h)
  all_goals ohne_blatt h

theorem controlStmt_ohne {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (leave : Bool) (hl : l = true) : (controlStmt (V := V) (Γ := Γ) (Λ := Λ) leave hl).ohneLocks = true := by
  cases leave <;> rfl

theorem controlEnd_ohne {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (leave : Bool) (hl : l = true) : (controlEnd (V := V) (Γ := Γ) (Λ := Λ) leave hl).ohneLocks = true := by
  cases leave <;> rfl

theorem BareArms.ohne {loopMode : Bool} {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    {cs : List (Option Ty)} {arms : Arms D V loopMode Γ Λ Λ cs}
    {reasons : GrundArms D V loopMode Γ Λ Λ cs.length} (h : BareArms arms reasons)
    (hr : reasons.ohneLocks = true) : arms.ohneLocks = true := by
  induction h with
  | nil => rfl
  | cons _ ih =>
    simp only [GrundArms.ohneLocks, Bool.and_eq_true] at hr
    simp only [Arms.ohneLocks, ih hr.2, Bool.and_true]
    exact hr.1

end Gabbro.Bruecke
