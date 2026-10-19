/-
  File:      Grammatik/Gen/Erzeuger/BlockVollst.lean
  Subject:   COMPLETENESS of the block and end-block generators, one step each (see `AnweisungVollst.lean`).
-/
import Grammatik.Gen.Erzeuger.AnweisungVollst

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] {V : Vertrag D}

/-- Close `x ∈ blockS ...` from `hc : x ∈ clause`. -/
macro "blk_fin " h:ident : tactic =>
  `(tactic| (unfold blockS; simp only [List.mem_append]; simp only [$h:ident, or_true, true_or]))

/-- Close `x ∈ endS ...` from `hc : x ∈ clause`. -/
macro "end_fin " h:ident : tactic =>
  `(tactic| (unfold endS; simp only [List.mem_append]; simp only [$h:ident, or_true, true_or]))

set_option maxHeartbeats 8000000 in
theorem block_schritt {m : Nat} (ih : Vollst V m) :
    ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'),
      groesseBlock b ≤ m + 1 → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ (genRek V (m + 1)).bl l Γ Λ := by
  obtain ⟨ihS, ihB, ihE⟩ := ih
  intro l Γ Λ Λ' b h
  show _ ∈ blockS m (genRek V m) l Γ Λ
  have hexa : ∀ {Γ : Ctx} {Λ : List (Res D)} (τs : List Ty) (a : Args D Γ Λ τs), groesseArgs a ≤ m + 1 →
      a ∈ genArgs (genExpr m Γ Λ) τs := fun τs a ha => mem_genArgs (fun τ e he => hx_aus m e he) τs a ha
  cases b with
  | nil =>
    have hc : (⟨_, .nil⟩ : SB D V l Γ Λ) ∈ bNil l Γ Λ := by simp [bNil]
    blk_fin hc
  | cons s rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .cons s rest⟩ : SB D V l Γ Λ) ∈ bCons (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨⟨_, s⟩, ihS _ _ _ _ s (by omega),
        List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩
    blk_fin hc
  | bind e rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .bind e rest⟩ : SB D V l Γ Λ) ∈ bBind m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨⟨_, e⟩, hx_aus m e (by omega),
        List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩
    blk_fin hc
  | bindCall f args he hp hr rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .bindCall f args he hp hr rest⟩ : SB D V l Γ Λ) ∈ bBindCall m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨f, Aufz.fn_mem f, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hp, dif_pos hr]
          exact List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩)⟩⟩
    blk_fin hc
  | bindCallInd p args he hp hr rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .bindCallInd p args he hp hr rest⟩ : SB D V l Γ Λ) ∈ bBindCallInd m (genRek V m) l Γ Λ :=
      mem_mitFnptrR (hx_aus m p (by omega)) (List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hp, dif_pos hr]
          exact List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩)⟩)
    blk_fin hc
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .bindCallElse f args he hp hr err rest⟩ : SB D V l Γ Λ) ∈ bBindCallElse m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨f, Aufz.fn_mem f, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hp, dif_pos hr]
          exact List.mem_flatMap.2 ⟨err, ihE _ _ _ err (by omega),
            List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩)⟩⟩
    blk_fin hc
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .bindAxiom a args he hw hg hd hgd rest⟩ : SB D V l Γ Λ) ∈ bBindAxiom m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨a, Aufz.ax_mem a, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hw, dif_pos hg, dif_pos hd, dif_pos hgd]
          exact List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩)⟩⟩
    blk_fin hc
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .bindAxiomElse a args he hr hw hg hd hgd err rest⟩ : SB D V l Γ Λ) ∈
        bBindAxiomElse m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨a, Aufz.ax_mem a, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hr, dif_pos hw, dif_pos hg, dif_pos hd, dif_pos hgd]
          exact List.mem_flatMap.2 ⟨err, ihE _ _ _ err (by omega),
            List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩)⟩⟩
    blk_fin hc
  | regRead r hk rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .regRead r hk rest⟩ : SB D V l Γ Λ) ∈ bRegRead (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨r, Aufz.reg_mem r, by
        rw [dif_pos hk]
        exact List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩
    blk_fin hc
  | regReadElse r hk z sonst rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .regReadElse r hk z sonst rest⟩ : SB D V l Γ Λ) ∈ bRegReadElse m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨r, Aufz.reg_mem r, by
        rw [dif_pos hk]
        exact List.mem_flatMap.2 ⟨z, mem_ofTy (hx_aus m z (by omega)),
          List.mem_flatMap.2 ⟨sonst, ihE _ _ _ sonst (by omega),
            List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩⟩
    blk_fin hc
  | awaits g payload hp hL rest =>
    simp only [groesseBlock] at h
    subst hp
    have hc : (⟨_, .awaits g (D.nutzlast g) rfl hL rest⟩ : SB D V l Γ Λ) ∈ bAwaits (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, by
        rw [dif_pos hL]
        exact List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩
    blk_fin hc
  | exchange g neu hw hL rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .exchange g neu hw hL rest⟩ : SB D V l Γ Λ) ∈ bExchange m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, List.mem_flatMap.2 ⟨neu, mem_ofTy (hx_aus m neu (by omega)), by
        rw [dif_pos hw, dif_pos hL]
        exact List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩
    blk_fin hc
  | narrow e lo' hi' sonst rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .narrow e lo' hi' sonst rest⟩ : SB D V l Γ Λ) ∈ bNarrow m (genRek V m) l Γ Λ :=
      mem_mitIntR (hx_aus m e (by omega)) (List.mem_flatMap.2 ⟨lo', mem_ints (by omega),
        List.mem_flatMap.2 ⟨hi', mem_ints (by omega), List.mem_flatMap.2 ⟨sonst, ihE _ _ _ sonst (by omega),
          List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩⟩)
    blk_fin hc
  | check c sonst rest =>
    simp only [groesseBlock] at h
    have hc : (⟨_, .check c sonst rest⟩ : SB D V l Γ Λ) ∈ bCheck m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨c, mem_ofTy (hx_aus m c (by omega)), List.mem_flatMap.2 ⟨sonst,
        ihE _ _ _ sonst (by omega), List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩
    blk_fin hc
  | float op a b lo hi rest =>
    simp only [groesseBlock, groessePaar] at h
    have hc : (⟨_, .float op a b lo hi rest⟩ : SB D V l Γ Λ) ∈ bFloat m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨op, mem_gleitOps op, mem_mitFl2R (hx_aus m a (by omega)) (hx_aus m b (by omega))
        (List.mem_flatMap.2 ⟨lo, mem_paare (by omega) (by omega), List.mem_flatMap.2 ⟨hi,
          mem_paare (by omega) (by omega),
          List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩)⟩
    blk_fin hc
  | floatLit q lo hi rest =>
    simp only [groesseBlock, groessePaar] at h
    have hc : (⟨_, .floatLit q lo hi rest⟩ : SB D V l Γ Λ) ∈ bFloatLit m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨q, mem_paare (by omega) (by omega), List.mem_flatMap.2 ⟨lo,
        mem_paare (by omega) (by omega), List.mem_flatMap.2 ⟨hi, mem_paare (by omega) (by omega),
          List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩⟩
    blk_fin hc
  | floatOf e lo hi rest =>
    simp only [groesseBlock, groessePaar] at h
    have hc : (⟨_, .floatOf e lo hi rest⟩ : SB D V l Γ Λ) ∈ bFloatOf m (genRek V m) l Γ Λ :=
      mem_mitIntR (hx_aus m e (by omega)) (List.mem_flatMap.2 ⟨lo, mem_paare (by omega) (by omega),
        List.mem_flatMap.2 ⟨hi, mem_paare (by omega) (by omega),
          List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩)
    blk_fin hc
  | floatNarrow e lo hi sonst rest =>
    simp only [groesseBlock, groessePaar] at h
    have hc : (⟨_, .floatNarrow e lo hi sonst rest⟩ : SB D V l Γ Λ) ∈ bFloatNarrow m (genRek V m) l Γ Λ :=
      mem_mitFlR (hx_aus m e (by omega)) (List.mem_flatMap.2 ⟨lo, mem_paare (by omega) (by omega),
        List.mem_flatMap.2 ⟨hi, mem_paare (by omega) (by omega), List.mem_flatMap.2 ⟨sonst,
          ihE _ _ _ sonst (by omega), List.mem_map.2 ⟨⟨_, rest⟩, ihB _ _ _ _ rest (by omega), rfl⟩⟩⟩⟩)
    blk_fin hc

set_option maxHeartbeats 8000000 in
theorem end_schritt {m : Nat} (ih : Vollst V m) :
    ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Endblock D V l Γ Λ),
      groesseEnd e ≤ m + 1 → e ∈ (genRek V (m + 1)).en l Γ Λ := by
  obtain ⟨ihS, ihB, ihE⟩ := ih
  intro l Γ Λ e h
  show _ ∈ endS m (genRek V m) l Γ Λ
  have hexa : ∀ {Γ : Ctx} {Λ : List (Res D)} (τs : List Ty) (a : Args D Γ Λ τs), groesseArgs a ≤ m + 1 →
      a ∈ genArgs (genExpr m Γ Λ) τs := fun τs a ha => mem_genArgs (fun τ e he => hx_aus m e he) τs a ha
  cases e with
  | ret e hΛ =>
    simp only [groesseEnd] at h
    have hc : (Endblock.ret e hΛ : Endblock D V l Γ Λ) ∈ eRet m l Γ Λ :=
      List.mem_flatMap.2 ⟨e, mem_genErg (fun τ e he => hx_aus m e he) _ e (by omega), by
        rw [dif_pos hΛ]; simp⟩
    end_fin hc
  | retWhy r hΛ =>
    have hc : (Endblock.retWhy r hΛ : Endblock D V l Γ Λ) ∈ eRetWhy l Γ Λ :=
      List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp⟩
    end_fin hc
  | leave hl =>
    have hc : (Endblock.leave hl : Endblock D V l Γ Λ) ∈ eLeave l Γ Λ := by
      unfold eLeave; rw [dif_pos hl]; simp
    end_fin hc
  | next hl =>
    have hc : (Endblock.next hl : Endblock D V l Γ Λ) ∈ eNext l Γ Λ := by
      unfold eNext; rw [dif_pos hl]; simp
    end_fin hc
  | cons s rest =>
    simp only [groesseEnd] at h
    have hc : (Endblock.cons s rest : Endblock D V l Γ Λ) ∈ eCons (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨⟨_, s⟩, ihS _ _ _ _ s (by omega),
        List.mem_map.2 ⟨rest, ihE _ _ _ rest (by omega), rfl⟩⟩
    end_fin hc
  | bind e rest =>
    simp only [groesseEnd] at h
    have hc : (Endblock.bind e rest : Endblock D V l Γ Λ) ∈ eBind m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨⟨_, e⟩, hx_aus m e (by omega),
        List.mem_map.2 ⟨rest, ihE _ _ _ rest (by omega), rfl⟩⟩
    end_fin hc
  | bindCall f args he hp hr rest =>
    simp only [groesseEnd] at h
    have hc : (Endblock.bindCall f args he hp hr rest : Endblock D V l Γ Λ) ∈ eBindCall m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨f, Aufz.fn_mem f, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hp, dif_pos hr]
          exact List.mem_map.2 ⟨rest, ihE _ _ _ rest (by omega), rfl⟩)⟩⟩
    end_fin hc
  | bindCallElse f args he hp hr err rest =>
    simp only [groesseEnd] at h
    have hc : (Endblock.bindCallElse f args he hp hr err rest : Endblock D V l Γ Λ) ∈
        eBindCallElse m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨f, Aufz.fn_mem f, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hp, dif_pos hr]
          exact List.mem_flatMap.2 ⟨err, ihE _ _ _ err (by omega),
            List.mem_map.2 ⟨rest, ihE _ _ _ rest (by omega), rfl⟩⟩)⟩⟩
    end_fin hc
  | bindAxiom a args he hw hg hd hgd rest =>
    simp only [groesseEnd] at h
    have hc : (Endblock.bindAxiom a args he hw hg hd hgd rest : Endblock D V l Γ Λ) ∈
        eBindAxiom m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨a, Aufz.ax_mem a, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hw, dif_pos hg, dif_pos hd, dif_pos hgd]
          exact List.mem_map.2 ⟨rest, ihE _ _ _ rest (by omega), rfl⟩)⟩⟩
    end_fin hc
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
    simp only [groesseEnd] at h
    have hc : (Endblock.bindAxiomElse a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) ∈
        eBindAxiomElse m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨a, Aufz.ax_mem a, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        mem_mitSome he (by
          rw [dif_pos hr, dif_pos hw, dif_pos hg, dif_pos hd, dif_pos hgd]
          exact List.mem_flatMap.2 ⟨err, ihE _ _ _ err (by omega),
            List.mem_map.2 ⟨rest, ihE _ _ _ rest (by omega), rfl⟩⟩)⟩⟩
    end_fin hc

/-- **Completeness of the statement, block and end-block generators**: everything of size at most `m` is
    generated at fuel `m`. -/
theorem genRek_vollst (V : Vertrag D) : ∀ m, Vollst V m := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro l Γ Λ Λ' s h
      cases s <;> (simp only [groesseStmt] at h; omega)
    · intro l Γ Λ Λ' b h
      cases b <;> (simp only [groesseBlock] at h; omega)
    · intro l Γ Λ e h
      cases e <;> (simp only [groesseEnd] at h; omega)
  | succ m ih =>
    exact ⟨stmt_schritt ih, block_schritt ih, end_schritt ih⟩

end Gabbro.Grammatik.Gen
