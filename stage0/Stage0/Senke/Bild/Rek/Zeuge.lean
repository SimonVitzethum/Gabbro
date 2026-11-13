/-
  File:      stage0/Stage0/Senke/Bild/Rek/Zeuge.lean
  Subject:   Witnesses of package P4 (boundaries inside a callee) on the call fixture `t4` of `RufAdaequatRufG`, the
             fixture of the P3 witness (`Bild/Ruf/Zeuge.lean`): the plain caller `t4F` (`g(); konto[1] := 7;
             return 9`, frame at depth 1) calls the callee `t4G` (`konto[0] := 5; return 3`), contracts `true`, no
             locks, the read-blind fixture oracle.
             * `bild_rek_zeuge`: from the start machine at the caller's boundary in front of the call (up to read
               events), thread `0` takes the step `ruf` (`randGL_ruf_eintritt`) and stands at the first body
               boundary of `t4G`, with `t4F`'s frame waiting on its stack, up to read events against the world in
               which the image's handler runs the callee's body (`rufWelt`); the callee's decomposed prefix in its
               frame at depth 0 takes the callee's write as one step, and machine G realises that step INSIDE the
               callee (`randGL_schritt` with the callee's call obligation at depth 0), to the boundary in front of
               the callee's `return`. All premises of `korrespondenz_rek` other than the image's memory hold jointly.
             * `tief_rang_zeuge`: ranked by their number, the fixture's bodies admit callers that do call
               (`t4F` at depth 2, the loop caller `t4L` at depth 4) by `tief_rang`.
             Kernel work: one run of the callee's write under `rufAt 0` (`rfl`); no image, no memory, no compiler.
-/
module
public import Stage0.Senke.Bild.Rek.Tief
public import Stage0.Senke.Bild.Rek.Lauf
public import Stage0.Senke.Bild.Ruf.Zeuge
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8a
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR

/-! ## The callee, split at its write -/

/-- The callee's write: `konto[0] := 5`. -/
def t4GSchreib : Stmt t4D (vertragVon t4D t4G) false [] [] [] :=
  .assignSlot () () t4Idx0 (t4Lit 5 (by decide) (by decide)) rfl t4Darf

/-- What remains of the callee behind its write: `return 3`. -/
def t4GRest : Endblock t4D (vertragVon t4D t4G) false [] [] :=
  .ret (.val (t4Lit 3 (by decide) (by decide))) List.Perm.nil

theorem t4GRumpf_eq : t4P.rumpf t4G = .cons t4GSchreib t4GRest := rfl

/-- The call's (empty) arguments. -/
abbrev zeugeArgs : Args t4D [] [] (t4D.params t4G) := .nil

/-- The world the image's handler runs the callee's body in: the caller's read world, then the `requires` read. -/
abbrev zeugeRufWelt : World t4D := rufWelt t4P t4G zeugeWeltL [] zeugeArgs

/-- The callee's parameters. -/
abbrev zeugeRufEnv : Env t4D (t4D.params t4G) := rufEnv t4G zeugeWeltL [] zeugeArgs Env.nil

/-- The caller frame waiting below the callee: `t4F` behind its call. -/
abbrev zeugeAufrufer : RufRahmenG t4D :=
  rufRahmenNach (f := t4F) Env.nil (t4Sp.welt []) Env.nil t4FRest

variable [Kern]

/-! ## The witness of the descent -/

/-- **P4 witness: boundaries inside the callee correspond.** Jointly: the callee's call obligation up to read events
    at depth 0 (for the empty callee set of depth 0); the callee's decomposed prefix, in its frame at depth 0 below
    the caller's frame at depth 1 (`zeugeRahmen`), taking the callee's write as one step from the handler's body
    world `zeugeRufWelt`; machine G, from the start machine, taking the step `ruf` to the callee's first body boundary
    (the caller frame `t4F` waiting on the stack, the machine's entry world `≈` to the sequential world after the
    argument reads); and machine G realising the callee's write to the boundary in front of the callee's `return`,
    at a world `≈` to the sequential one. -/
theorem bild_rek_zeuge :
    RufOkGleich t4P t4O 0 0 (fun _ => False) (rufAt t4P t4O 0 0) (Tief t4P (fun _ => False) 0) ∧
    ∃ (σ2 σm : World t4D) (M1 M2 : RufMaschineG t4D),
      Zerlegung (rufZRahmen zeugeLay t4O 0 t4P (fun _ => 0) 0 t4G zeugeRufWelt zeugeRufEnv) (fun _ => False)
        (Tief t4P (fun _ => False) 0) (t4P.rumpf t4G) zeugeRufWelt zeugeRufEnv t4GRest σ2 zeugeRufEnv ∧
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInit) M1 ∧ WeltGleich (zeugeWeltL.lese [] zeugeArgs.orte) σm ∧
      RandGL 0 [zeugeAufrufer] t4G zeugeRufEnv σm (fun _ => False) (t4P.rumpf t4G) M1 zeugeRufWelt zeugeRufEnv ∧
      RufLaufG t4P t4O 0 0 M1 M2 ∧
      RandGL 0 [zeugeAufrufer] t4G zeugeRufEnv σm (fun _ => False) t4GRest M2 σ2 zeugeRufEnv := by
  have hRuf0 : RufOkGleich t4P t4O 0 0 (fun _ => False) (rufAt t4P t4O 0 0) (Tief t4P (fun _ => False) 0) :=
    rufOk_gleich_tief leseblind_t4O 0 (fun _ => False) 0
  -- the caller's boundary in front of the call, as in `bild_ruf_zeuge`
  have hG : RandG 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) (.cons t4Ruf t4FRest)
      (RufStartG t4P t4Sp zeugeInit) zeugeWelt Env.nil :=
    randG_start t4P t4Sp (init := zeugeInit) (thr := 0) (f := t4F) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  have hw : WeltGleich zeugeWeltL zeugeWelt := (weltGleich_lese zeugeWelt [] [.inl ()]).symm
  have hGL : RandGL 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False)
      (.cons (.call t4G zeugeArgs (t4Hp t4F) rfl) t4FRest) (RufStartG t4P t4Sp zeugeInit) zeugeWeltL Env.nil :=
    ⟨zeugeWelt, hw, hG⟩
  -- the descent: the step `ruf`
  obtain ⟨M1, σm, hl1, hw1, hG1⟩ := randGL_ruf_eintritt (P := t4P) (O := t4O) (passes := 0) hGL
  -- inside the callee: its write, sequentially (the one kernel run) and on machine G
  obtain ⟨σ2, hex2⟩ : ∃ σ2 : World t4D,
      execStmt t4O 0 (rufAt t4P t4O 0 0) t4GSchreib zeugeRufWelt zeugeRufEnv = .ok σ2 zeugeRufEnv := ⟨_, rfl⟩
  have hs : StmtR (fun _ => False) (Tief t4P (fun _ => False) 0) true t4GSchreib :=
    StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)
  have hk : Zerlegung (rufZRahmen zeugeLay t4O 0 t4P (fun _ => 0) 0 t4G zeugeRufWelt zeugeRufEnv)
      (fun _ => False) (Tief t4P (fun _ => False) 0) (t4P.rumpf t4G) zeugeRufWelt zeugeRufEnv t4GRest σ2
      zeugeRufEnv := by
    rw [t4GRumpf_eq]
    exact Zerlegung.schritt t4GSchreib t4GRest t4GRest zeugeRufWelt σ2 σ2 zeugeRufEnv zeugeRufEnv zeugeRufEnv
      hs hex2 (Zerlegung.halt t4GRest σ2 zeugeRufEnv)
  have hG1' : RandGL 0 [zeugeAufrufer] t4G zeugeRufEnv σm (fun _ => False) (.cons t4GSchreib t4GRest) M1
      zeugeRufWelt zeugeRufEnv :=
    hG1
  obtain ⟨M2, hl2, hG2⟩ := randGL_schritt leseblind_t4O hRuf0 hs hex2 hG1'
  exact ⟨hRuf0, σ2, σm, M1, M2, hk, hl1, hw1, hG1, hl2, hG2⟩

/-! ## The witness of the rank discharge -/

/-- The rank of the fixture's functions: their number (the callee `t4G` has rank 0, every caller a larger one). -/
def t4Rang (g : t4D.Fn) : Nat := (show Fin 4 from g).val

/-- Every body of the fixture is in the call fragment with callees of smaller rank. -/
theorem t4_rang (A : t4D.Lock → Prop) :
    ∀ g : Fin 4, EndR A (fun g' => t4Rang g' < t4Rang g) (t4P.rumpf g)
  | ⟨0, _⟩ => EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)
  | ⟨1, _⟩ => EndR.cons _ _ (StmtR.call _ t4G rfl (Nat.succ_pos 0))
      (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))
  | ⟨2, _⟩ => EndR.cons _ _
      (StmtR.ite _ _ _
        (BlockR.bindCall _ _ _ _ _ _ (Nat.succ_pos 1)
          (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
        BlockR.nil)
      (EndR.ret _ _)
  | ⟨3, _⟩ => EndR.cons _ _
      (StmtR.traverse _ _ _ (BlockR.cons _ _ (StmtR.call _ t4G rfl (Nat.succ_pos 2)) BlockR.nil))
      (EndR.cons _ _
        (StmtR.retry _ _ _ _
          (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil)
          (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
        (EndR.ret _ _))
  | ⟨n + 4, h⟩ => absurd h (by omega)

/-- **Witness of `tief_rang`**: the ranked fixture admits callers that do call -- the plain caller at depth 2 and the
    loop caller at depth 4 -- not only the leaf callee. -/
theorem tief_rang_zeuge : Tief t4P (fun _ => False) 2 t4F ∧ Tief t4P (fun _ => False) 4 t4L :=
  ⟨tief_rang t4P _ t4Rang (fun g => t4_rang _ g) 2 t4F (Nat.lt_succ_self 1),
    tief_rang t4P _ t4Rang (fun g => t4_rang _ g) 4 t4L (Nat.lt_succ_self 3)⟩

#print axioms bild_rek_zeuge
#print axioms tief_rang_zeuge

end Gabbro.Stage0.Senke.BildLauf
