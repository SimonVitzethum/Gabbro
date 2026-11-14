/-
  File:      stage0/Stage0/Senke/Bild/Rek/ZeugeRueck.lean
  Subject:   Witnesses of package P5 (returns and recursion) on a RECURSIVE variant of the call fixture `t4`: the same
             declaration `t4D` (one table `konto`, no locks, contracts `true`, the read-blind oracle `t4O`), with
             the program `rkP`:

                 fn 0 (the callee `t4G`):   if false { g() } else { }; return 3      -- calls ITSELF
                 fn 1 (the caller `t4F`):   g(); return 9
                 fn 2, fn 3:                return 9

             * `rkG_tiefAlle`/`rkG_nicht_tief`: the recursive callee is admitted at every depth by `TiefAlle`
               (`tiefAlle_frag`, no rank), and at NO depth by P4's `Tief` -- P5 is strictly stronger;
             * `bild_rueck_zeuge`: all premises jointly, reusing a symbolic return of `g()` under `rufAt 1`:
               the call obligation for the recursive callee at depth 1 (`rufOk_gleich_tiefAlle`); the caller's
               decomposed prefix taking the call to the recursive callee as one step; machine G realising that step
               from the start machine (`randGL_schritt`); machine G descending into the callee (`randGL_ruf_eintritt`,
               the caller waiting on the stack); and machine G RETURNING from the callee's boundary to the caller's
               boundary behind the call (`randGL_rueck`, with the callee's trivial decomposed prefix), at a world `≈`
               to the sequential world behind the call. No image, no memory, no compiler.
-/
module
public import Stage0.Senke.Bild.Rek.Fenster
public import Stage0.Senke.Bild.Rek.Zeuge
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke

/-! ## The recursive fixture -/

/-- The recursive callee: `if false { g() } else { }; return 3`. -/
def rkGRumpf : Endblock t4D (vertragVon t4D t4G) false [] [] :=
  .cons (.ite .fls (.cons (.call t4G .nil (t4Hp t4G) rfl) .nil) .nil)
    (.ret (.val (t4Lit 3 (by decide) (by decide))) List.Perm.nil)

/-- The caller's call: `g();`. -/
def rkRuf : Stmt t4D (vertragVon t4D t4F) false [] [] (nach t4D t4G []) :=
  .call t4G .nil (t4Hp t4F) rfl

/-- What remains of the caller behind the call: `return 9`. -/
def rkFRest : Endblock t4D (vertragVon t4D t4F) false [] (nach t4D t4G []) :=
  .ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil

/-- The caller: `g(); return 9`. -/
def rkFRumpf : Endblock t4D (vertragVon t4D t4F) false [] [] :=
  .cons rkRuf rkFRest

/-- The other bodies: `return 9`. -/
def rkLeer (f : t4D.Fn) : Endblock t4D (vertragVon t4D f) false [] [] :=
  .ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil

/-- The recursive program over `t4D`. -/
def rkP : Programm t4D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun (f : Fin 4) => match f with
    | 0 => rkGRumpf
    | 1 => rkFRumpf
    | 2 => rkLeer _
    | 3 => rkLeer _

theorem rkFRumpf_eq : rkP.rumpf t4F = .cons rkRuf rkFRest := rfl

/-- The untaken recursive branch does not run: simplify the branch and return with a symbolic world. -/
theorem rkG_ruf_kehrt (σ : World t4D) : ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
    rufAt rkP t4O 0 1 t4G σ Env.nil = .ok σ' v := by
  obtain ⟨σ', v, hb⟩ : ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
      execEnd (V := vertragVon t4D t4G) t4O 0 (rufAt rkP t4O 0 0) (rkP.rumpf t4G) σ Env.nil =
        .zurueck σ' v := by
    change ∃ σ' v, execEnd (V := vertragVon t4D t4G) t4O 0 (rufAt rkP t4O 0 0)
      rkGRumpf σ Env.nil = .zurueck σ' v
    simp only [rkGRumpf, execEnd, execStmt, eval, wahr?, Bool.false_eq_true, ↓reduceIte, execBlock]
    exact ⟨_, _, rfl⟩
  exact ⟨σ', v, rufAt_t4D_ok_of_body rfl rfl hb⟩

/-! ## `TiefAlle` admits the recursive callee, `Tief` does not -/

/-- Every body of the recursive fixture is in the call fragment with every callee admitted. -/
theorem rk_frag (A : t4D.Lock → Prop) : ∀ g : Fin 4, EndR A (fun _ => True) (rkP.rumpf g)
  | ⟨0, _⟩ => EndR.cons _ _
      (StmtR.ite _ _ _ (BlockR.cons _ _ (StmtR.call _ t4G rfl trivial) BlockR.nil) BlockR.nil) (EndR.ret _ _)
  | ⟨1, _⟩ => EndR.cons _ _ (StmtR.call _ t4G rfl trivial) (EndR.ret _ _)
  | ⟨2, _⟩ => EndR.ret _ _
  | ⟨3, _⟩ => EndR.ret _ _
  | ⟨n + 4, h⟩ => absurd h (by omega)

/-- **The recursive callee is admitted at every depth** (`tiefAlle_frag`). -/
theorem rkG_tiefAlle (A : t4D.Lock → Prop) (n : Nat) : TiefAlle rkP A n t4G :=
  tiefAlle_frag rkP A (fun g => rk_frag A g) n t4G

/-- **P4 admits the recursive callee at no depth**: its body calls itself, so `Tief` bottoms out in `False`. -/
theorem rkG_nicht_tief (A : t4D.Lock → Prop) : ∀ n, ¬ Tief rkP A n t4G
  | 0 => fun h => h
  | n + 1 => fun h => by
    have h' : EndR A (Tief rkP A n)
        (.cons (.ite .fls (.cons (.call t4G .nil (t4Hp t4G) rfl) .nil) .nil)
          (.ret (.val (t4Lit 3 (by decide) (by decide))) List.Perm.nil) :
          Endblock t4D (vertragVon t4D t4G) false [] []) := h
    cases h' with
    | cons _ _ hs _ =>
      cases hs with
      | blatt _ hb => cases hb
      | call _ g' hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
      | ite _ _ _ ht _ =>
        cases ht with
        | cons _ _ hc _ =>
          cases hc with
          | blatt _ hb => cases hb
          | call _ g' hg hC =>
            have hgg : g' = t4G := (Option.some.inj hg).symm
            subst hgg
            exact rkG_nicht_tief A n hC

variable [Runner.IR.Kern]

/-! ## In and out of the recursive callee, machine G -/

/-- The frame of the caller's body at depth 2 (callees run as `rufAt 1`). -/
abbrev zeugeRahmenRk : BodyFrame t4D :=
  rumpfRahmen zeugeLay t4O 0 rkP (fun _ => 0) (fun _ => []) 0 1 t4F 0 0 0 0 0 (t4Sp.welt []) Env.nil [] ([], 0)

/-- **P5 witness, all premises jointly, with a symbolic call return.** For the recursive callee `t4G` (admitted by `TiefAlle`,
    not by `Tief`): the call obligation up to read events at depth 1; the caller's decomposed prefix taking the call
    `g()` as one step under `rufAt 1`; machine G, from the start machine, realising that step (`M'`); machine G
    descending into the callee (`M1`, the caller waiting on the stack); and machine G returning from the callee's
    first body boundary (its trivial decomposed prefix) to the caller's boundary in front of `return 9` (`M3`), at a
    world `≈` to the sequential world behind the call. -/
theorem bild_rueck_zeuge :
    TiefAlle rkP (fun _ => False) 1 t4G ∧ ¬ Tief rkP (fun _ => False) 1 t4G ∧
    RufOkGleich rkP t4O 0 0 (fun _ => False) (rufAt rkP t4O 0 1) (TiefAlle rkP (fun _ => False) 1) ∧
    ∃ (σ1 : World t4D) (M' M1 M3 : RufMaschineG t4D),
      Zerlegung zeugeRahmenRk (fun _ => False) (TiefAlle rkP (fun _ => False) 1) (rkP.rumpf t4F) zeugeWeltL
        Env.nil rkFRest σ1 Env.nil ∧
      RufLaufG rkP t4O 0 0 (RufStartG rkP t4Sp zeugeInit) M' ∧
      RandGL 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) rkFRest M' σ1 Env.nil ∧
      RufLaufG rkP t4O 0 0 (RufStartG rkP t4Sp zeugeInit) M1 ∧
      RufLaufG rkP t4O 0 0 M1 M3 ∧
      RandGL 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) rkFRest M3 σ1 Env.nil := by
  have hRuf : RufOkGleich rkP t4O 0 0 (fun _ => False) (rufAt rkP t4O 0 1) (TiefAlle rkP (fun _ => False) 1) :=
    rufOk_gleich_tiefAlle (leseblind_t4O.toP _) 0 (fun _ => False) 1
  obtain ⟨σ1, v, hG⟩ := rkG_ruf_kehrt zeugeWeltL
  have hex : execStmt t4O 0 (rufAt rkP t4O 0 1) rkRuf zeugeWeltL Env.nil = .ok σ1 Env.nil := by
    -- Keep the read world folded so the symbolic handler return matches.
    simp only [rkRuf, execStmt, Args.orte, lese_nil, evalArgs, hG]
  have hs : StmtR (fun _ => False) (TiefAlle rkP (fun _ => False) 1) false rkRuf :=
    StmtR.call rkRuf t4G rfl (rkG_tiefAlle _ 1)
  have hk : Zerlegung zeugeRahmenRk (fun _ => False) (TiefAlle rkP (fun _ => False) 1) (rkP.rumpf t4F) zeugeWeltL
      Env.nil rkFRest σ1 Env.nil := by
    rw [rkFRumpf_eq]
    exact Zerlegung.schritt rkRuf rkFRest rkFRest zeugeWeltL σ1 σ1 Env.nil Env.nil Env.nil hs hex
      (Zerlegung.halt rkFRest σ1 Env.nil)
  -- the caller's boundary in front of the call, up to read events
  have hG : RandG 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) (.cons rkRuf rkFRest)
      (RufStartG rkP t4Sp zeugeInit) zeugeWelt Env.nil :=
    randG_start rkP t4Sp (init := zeugeInit) (thr := 0) (f := t4F) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  have hw : WeltGleich zeugeWeltL zeugeWelt := (weltGleich_lese zeugeWelt [] [.inl ()]).symm
  have hGL : RandGL 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False)
      (.cons (.call t4G zeugeArgs (t4Hp t4F) rfl) rkFRest) (RufStartG rkP t4Sp zeugeInit) zeugeWeltL Env.nil :=
    ⟨zeugeWelt, hw, hG⟩
  -- the call as one step of the caller
  obtain ⟨M', hl, hG'⟩ := randGL_schritt leseblind_t4O.rs hRuf hs hex hGL
  -- into the callee
  obtain ⟨M1, σm, hl1, _, hG1⟩ := randGL_ruf_eintritt (P := rkP) (O := t4O) (passes := 0) hGL
  -- the callee's trivial decomposed prefix, and back to the caller
  have hkC : Zerlegung (rufZRahmen zeugeLay t4O 0 rkP (fun _ => 0) 0 t4G
        (rufWelt rkP t4G zeugeWeltL [] zeugeArgs) (rufEnv t4G zeugeWeltL [] zeugeArgs Env.nil))
      (fun _ => False) (TiefAlle rkP (fun _ => False) 0) (rkP.rumpf t4G)
      (rufWelt rkP t4G zeugeWeltL [] zeugeArgs) (rufEnv t4G zeugeWeltL [] zeugeArgs Env.nil) (rkP.rumpf t4G)
      (rufWelt rkP t4G zeugeWeltL [] zeugeArgs) (rufEnv t4G zeugeWeltL [] zeugeArgs Env.nil) :=
    Zerlegung.halt _ _ _
  obtain ⟨M3, hl3, hG3⟩ := randGL_rueck (j := 0) (leseblind_t4O.toP rkP) (rkG_tiefAlle _ 1) hGL hex hkC hG1
  exact ⟨rkG_tiefAlle _ 1, rkG_nicht_tief _ 1, hRuf, σ1, M', M1, M3, hk, hl, hG', hl1, hl3, hG3⟩

#print axioms rkG_nicht_tief
#print axioms bild_rueck_zeuge

end Gabbro.Stage0.Senke.BildLauf
