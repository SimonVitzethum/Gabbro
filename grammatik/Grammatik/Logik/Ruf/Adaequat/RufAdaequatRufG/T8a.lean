module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
@[expose] public section


namespace Gabbro.Grammatik

/-- The callee body is covered with no further calls: depth 1 admits it. -/
theorem t4G_tief (A : t4D.Lock → Prop) : Tief t4P A 1 t4G :=
  show EndR A (Tief t4P A 0) t4GRumpf from EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)

theorem t4FRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4FRumpf :=
  EndR.cons _ _ (StmtR.call _ t4G rfl (t4G_tief A))
    (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))

theorem t4BRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCall _ _ _ _ _ _ (t4G_tief A)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

theorem t4LRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4LRumpf :=
  EndR.cons _ _
    (StmtR.traverse _ _ _ (BlockR.cons _ _ (StmtR.call _ t4G rfl (t4G_tief A)) BlockR.nil))
    (EndR.cons _ _
      (StmtR.retry _ _ _ _
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      (EndR.ret _ _))

theorem t4_frei (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) :
    ∀ L : t4D.Lock, (fun _ => False) L → RufFreiG (t4M fn b) 0 L := fun L => nomatch L

theorem t4_held : HeldGenau ([] : List (Res t4D)) (offen ([] : List (Ereignis t4D))) :=
  fun L => nomatch L

/-- The sequential run of the plain caller with the body-running handler:
    the callee writes slot 0, the caller then writes slot 1 and returns 9. -/
theorem t4F_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- The sequential run of the bind caller: the callee writes slot 0 and
    returns 3, the caller binds it and writes it to slot 1, then returns 9. -/
theorem t4B_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 3 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat_ruf`** (plain call at `ende` position).
    Every premise is instantiated jointly on the non-degenerate program
    above at depth `1`: the caller's body calls a callee that WRITES the
    table, and after the call the caller writes a second slot and returns
    a value. The sequential semantics with the body-running handler ends
    with slot 0 moved `0 -> 5` (the callee), slot 1 moved `0 -> 7` (the
    caller, AFTER the call) and value `9`; the machine, by steps of thread 0
    alone, pops the caller's frame logging that same `9` and that same
    world, and its memory holds both moved slots. The old `ruf` rule could
    never reach the write to slot 1. -/
theorem rufG_adaequat_ruf_zeuge :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (((t4M t4F t4FRumpf).weltVon 0).slots () 0 ()).n = 0 ∧
      (((t4M t4F t4FRumpf).weltVon 0).slots () 1 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4F t4FRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4F Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        M'.speicher = σ'.speicher ∧ (M'.speicher.slots () 0 ()).n = 5 ∧
        (M'.speicher.slots () 1 ()).n = 7 ∧
        (∀ g, g ≠ 0 → M'.faeden g = (t4M t4F t4FRumpf).faeden g) := by
  obtain ⟨σ', v, hex, h5, h7, h9⟩ := t4F_exec
  obtain ⟨M', ext, hl, hf, hsp, hfr⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4F t4FRumpf) 0 t4F
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4FRumpf (fun _ => False)
    (t4FRumpf_R _) rfl rfl t4_held (t4_frei t4F t4FRumpf) σ' v hex
  refine ⟨σ', v, hex, rfl, rfl, h5, h7, h9, M', ext, hl, hf, hsp, ?_, ?_, hfr⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h7

/-- **Witness for `rufG_adaequat_ruf`** (bind-call in block position, under
    an `if`): the callee writes slot 0 and returns `3`; the caller binds
    `x = 3` and writes it to slot 1. The machine pops the caller's frame
    with the same value `9` and a memory holding `5` and `3` -- the bound
    value travelled through the machine's `rueckBind`. -/
theorem rufG_adaequat_ruf_zeuge_bind :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 3 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 5 ∧ (M'.speicher.slots () 1 ()).n = 3 := by
  obtain ⟨σ', v, hex, h5, h3, h9⟩ := t4B_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4B t4BRumpf) 0 t4B
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf (fun _ => False)
    (t4BRumpf_R _) rfl rfl t4_held (t4_frei t4B t4BRumpf) σ' v hex
  refine ⟨σ', v, hex, h5, h3, h9, M', ext, hl, hf, ?_, ?_⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h3


/-- The sequential run of the loop caller: three calls inside the
    `traverse` (slot 0 moved to 5), the `retry` body once (slot 1 to 8),
    its overflow block (slot 2 to 6), value 9. -/
theorem t4L_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4L).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4LRumpf ((t4M t4L t4LRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 8 ∧ (σ'.slots () 2 ()).n = 6 ∧
    (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat_ruf` with loops**: a `traverse` whose body
    CALLS the writing callee (three iterations, the invariant read before
    each and after the last), then a bounded `retry` whose body runs once
    and whose overflow block runs at the bound. The machine pops the frame
    with the value `9` and the memory the sequential semantics computes:
    all three slots moved. -/
theorem rufG_adaequat_ruf_zeuge_schleife :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4L).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4LRumpf ((t4M t4L t4LRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4L t4LRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4L Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 5 ∧ (M'.speicher.slots () 1 ()).n = 8 ∧
        (M'.speicher.slots () 2 ()).n = 6 := by
  obtain ⟨σ', v, hex, h5, h8, h6, h9⟩ := t4L_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4L t4LRumpf) 0 t4L
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4LRumpf (fun _ => False)
    (t4LRumpf_R _) rfl rfl t4_held (t4_frei t4L t4LRumpf) σ' v hex
  refine ⟨σ', v, hex, h9, M', ext, hl, hf, ?_, ?_, ?_⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h8
  · rw [hsp]; exact h6


/-! ## 11b. Witnesses: a loop left by `leave` after writing, `next`, and both
    paths of `let … else`

    `t5D` is `t4D` with five functions over two signatures: `sig 0` (no
    reason, returns `.int 0 100`) and `sig 1` (ONE reason, returns
    `.int 0 100`). `sigNr n` has `n` reasons.

        fn 0 (G, sig 0):  konto[0] := 5; return 3
        fn 1 (E, sig 1):  konto[0] := 4; return reason 0          -- fails
        fn 2 (L, sig 0):  forever progress () invariant true {
                            konto[1] := 8; if true { leave } else { } };
                          traverse konto invariant true {
                            if true { next } else { }; konto[2] := 6 };
                          return 9
        fn 3 (B, sig 0):  if true {
                            let x = H() else { return 1 };
                            let y = E() else { konto[2] := x; return 5 }
                          } else { };
                          return 9
        fn 4 (H, sig 1):  konto[1] := 2; return 6

    `L` writes before its `leave` (the `if` layer is peeled), and every
    `next` skips the write after it. `B` takes the NORMAL path of the first
    `let … else` (`H` returns `6`) and the ERROR path of the second (`E`
    answers reason `0`, the else block writes the bound `x` and returns). -/

def t5Sig (g : Nat) : Signatur Unit Empty Empty Empty where
  params := []
  erg := some (.int 0 100)
  gruende := g
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []


end Gabbro.Grammatik
