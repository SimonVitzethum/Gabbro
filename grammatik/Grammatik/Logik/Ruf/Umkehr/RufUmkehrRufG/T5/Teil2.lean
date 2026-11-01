module

public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T4
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T5.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Every run of thread `f` that ends with a stack no longer than `lo`
    passes through a FIRST such machine: its prefix up to there keeps the
    stack longer than `lo` in every state that steps. -/
theorem rufLaufG_erster {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} (lo : Nat)
    {M M'' : RufMaschineG D} (hl : RufLaufG P O passes f M M'')
    (hpop : (M''.faeden f).stapel.length ≤ lo) :
    ∃ M1, RufLaufUeber P O passes f lo M M1 ∧ (M1.faeden f).stapel.length ≤ lo ∧
      RufLaufG P O passes f M1 M'' := by
  induction hl with
  | refl M => exact ⟨M, RufLaufUeber.refl M, hpop, RufLaufG.refl M⟩
  | @schritt M M' M2 hs hr ih =>
    by_cases hM : (M.faeden f).stapel.length ≤ lo
    · exact ⟨M, RufLaufUeber.refl M, hM, RufLaufG.schritt hs hr⟩
    · obtain ⟨M1, h1, h2, h3⟩ := ih hpop
      exact ⟨M1, RufLaufUeber.schritt (by omega) hs h1, h2, h3⟩

/-- The callee of the bind witness is covered by the converse at depth 1. -/
theorem t4G_tiefK (A : t4D.Lock → Prop) : TiefK t4P A 1 t4G :=
  ⟨show EndR A (TiefK t4P A 0) t4GRumpf from
    EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _), rfl⟩

/-- The bind caller is covered by the converse at depth 1. -/
theorem t4BRumpf_K (A : t4D.Lock → Prop) : EndR A (TiefK t4P A 1) t4BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCall _ _ _ _ _ _ (t4G_tiefK A)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

theorem t4BRumpf_kOk : t4BRumpf.kOk = true := by rfl

/-- **Witness for `rufG_adaequat_ruf_umkehr`.** All premises jointly, on the
    bind-caller program at depth 1: the machine `t4M t4B t4BRumpf`, the
    covered body (a bind-call of the writing callee under an `if`, the
    bound value written), and the run `rufG_adaequat_ruf` produces, cut at
    its FIRST pop of the caller's frame (`rufLaufG_erster`) -- a real run
    of the machine through the push, the callee's writing leaf, the binding
    pop, the caller's writing leaf and the final pop. From the MACHINE's
    log alone the converse recovers that the sequential semantics returns
    the logged value `9`, in a world with the logged memory (slot 0 moved
    to 5 by the callee, slot 1 to 3 by the caller). -/
theorem rufG_adaequat_ruf_umkehr_zeuge :
    ∃ (M1 : RufMaschineG t4D) (v : ErgVal t4D (t4D.erg t4B)) (s1 : World t4D)
      (ext : List (RufEreignisF t4D)),
      RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M1 ∧ (M1.faeden 0).stapel = [] ∧
      (M1.faeden 0).log = RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) s1 :: (ext ++ []) ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 3 ∧
      ∃ σ', execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0)
          Env.nil = .zurueck σ' v ∧
        σ'.speicher = s1.speicher ∧ (show Zahl 0 100 from v).n = 9 := by
  obtain ⟨σ', v, hex, h5, h3, h9, M', ext', hl, hf, _, _⟩ := rufG_adaequat_ruf_zeuge_bind
  have hpop' : (M'.faeden 0).stapel.length ≤ ([] : List (RufRahmenG t4D)).length := by
    rw [hf]
    exact Nat.le_refl 0
  obtain ⟨M1, hu, hpop1, _⟩ := rufLaufG_erster 0 hl hpop'
  obtain ⟨v1, s1, ext, σ1, hlog, hex1, hsp⟩ := rufG_adaequat_ruf_umkehr t4P t4O 0 1
    (t4M t4B t4BRumpf) 0 t4B Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf
    (fun _ => False) (t4BRumpf_K _) t4BRumpf_kOk rfl M1 hu hpop1
  cases hex.symm.trans hex1
  have hst : (M1.faeden 0).stapel = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hs1 : s1.slots = σ'.slots := by
    have := congrArg Speicher.slots hsp
    exact this.symm
  refine ⟨M1, v, s1, ext, hu, hst, hlog, ?_, ?_, σ', hex, hsp, h9⟩
  · rw [hs1]; exact h5
  · rw [hs1]; exact h3


end Gabbro.Grammatik
