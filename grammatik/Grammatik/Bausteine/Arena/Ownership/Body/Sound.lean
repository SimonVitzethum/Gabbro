import Grammatik.Bausteine.Arena.Ownership.Body.Forms

/-! **Soundness of the general ownership body judgment.** For every
derivation, every world and environment in which the invariant holds, the
actual G outcome of the statement, block, end block or case arms keeps its
promise. The call handler `R` is arbitrary up to `Respects` for the
interface contracts; foreign bodies are framed by the existing hardware
assumption `GutO`. One induction over the derivation. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

theorem dropContext_isOwner {A : FreiForm D} (c : Context) {erg : Option Ty} (out : Flow.Output A erg) :
    dropContext c out = dropContextB c (Flow.Output.isOwner out) := by
  cases out <;> rfl

section Arms

variable {A : FreiForm D} {fr : Frame} {s0 : State} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem Holds.arm {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (ca : Option (Int × Int)) (nutz : Nutzlast ca) : Holds A fr s0 (armBind c ca) σ (armEnv nutz ρ) := by
  match ca, nutz with
  | none, _ => exact h
  | some (_, _), v => exact h.bindNone (τ := .int _ _) v

theorem BPost.schrumpfArm {k c1 : Context} {l : Bool} {Γ : Ctx} (hk : k.references.length ≤ Γ.length)
    (ca : Option (Int × Int)) (o : Ausgang V l (ArmCtx Γ ca)) (h : BPost A fr s0 out k c1 o) :
    BPost A fr s0 out k (armDrop c1 ca) (o.schrumpfArm ca) := by
  match ca, o, h with
  | none, o, h => exact h
  | some (_, _), o, h => exact BPost.schrumpf hk o h

theorem armCtx_length (Γ : Ctx) : ∀ ca : Option (Int × Int), Γ.length ≤ (ArmCtx Γ ca).length
  | none => Nat.le_refl _
  | some (_, _) => Nat.le_succ _

theorem axiomAntwort_fst (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    (axiomAntwort O a σ ρ).1 = (O.wirkt a (σ.fragt (.inl a)) ρ).1 := rfl

end Arms

section Sound

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}
  {O : Orakel D} {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
  {fr : Frame} {s0 : State}

mutual

theorem os_sound (hR : Respects A I.contracts R) (hO : GutO O) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c' : Context} {st : Stmt D V l Γ Λ Λ'},
      OS A I out k c st c' → ∀ (σ : World D) (ρ : Env D Γ), k.references.length ≤ Γ.length →
        Holds A fr s0 c σ ρ → BPost A fr s0 out k c' (execStmt O passes R st σ ρ)
  | _, _, _, _, _, _, _, _, .assignSlot t f i e hw hL hn _ _ _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).meta (MetaSame.writeSlot A _ t _ _ f _ hn)
  | _, _, _, _, _, _, _, _, .assignThru p t ht f i e hw hL hn _ _ _ _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).meta (MetaSame.writeSlot A _ t _ _ f _ hn)
  | _, _, _, _, _, _, _, _, .assignGlob g e hw hL hg _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).meta (MetaSame.writeGlob A _ g _ _ hg)
  | _, _, _, _, _, _, _, _, .putBytes t f hf n i hlo hhi e hw hL ht _ _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).meta
      (MetaSame.writeBytes A t f hf _ (fun he => absurd he.symm ht) _ _ _)
  | _, _, _, _, _, _, _, _, .assignSlotRef r t _ _ f e _ _ htA _ _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).meta (MetaSame.writeSlot A _ t _ _ f _ (fun he => absurd he.symm htA))
  | _, _, _, _, _, _, _, _, .assignVar x e _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).assign x e _ _
  | _, _, _, _, _, _, _, _, .shift t f hτ i von nach hn he hw hL hl _ _, σ, ρ, _, h => by
    simp only [execStmt]
    split
    · exact (h.reads _ _).meta (MetaSame.writeSlot A _ t _ _ f _ hl)
    · trivial
  | _, _, _, _, _, _, _, _, .ite cond t e _ ht he, σ, ρ, hk, h => by
    simp only [execStmt]
    split
    · exact ob_sound hR hO ht _ ρ hk (h.reads _ _)
    · exact ob_sound hR hO he _ ρ hk (h.reads _ _)
  | _, _, _, _, _, _, _, _, .onOption o p a _ hp hw ha, σ, ρ, hk, h => by
    simp only [execStmt]
    split
    · rename_i v _
      exact BPost.weaken _ hw (BPost.schrumpf hk _
        (ob_sound hR hO hp _ _ (by simp; omega) ((h.reads _ _).bindNone (τ := .index _) v)))
    · exact ob_sound hR hO ha _ ρ hk (h.reads _ _)
  | _, _, _, _, _, _, _, _, .onTag v arms _ ha, σ, ρ, hk, h => by
    simp only [execStmt]
    exact oarms_sound hR hO ha _ _ ρ hk (h.reads _ _)
  | _, _, _, _, _, _, _, _, .onWhy r arms _ ha, σ, ρ, hk, h => by
    simp only [execStmt]
    exact ogrund_sound hR hO ha _ _ ρ hk (h.reads _ _)
  | _, _, _, _, _, _, _, _, .call f args hp hr _ hplan, σ, ρ, _, h => by
    simp only [execStmt]
    split
    · rename_i σ' v heq
      exact ValueBound.discard _ _ (call_value I R hR f args (h.reads _ _) hplan heq)
    · rename_i r _
      exact (Fin.cast hr r).elim0
    · trivial
    · trivial
  | _, _, _, _, _, _, _, _, .callInd p args hp hr J owner hJ _ _ hplan, σ, ρ, _, h => by
    simp only [execStmt]
    split
    rename_i f hf _
    split
    · rename_i σ' v heq
      rw [← (hJ f hf).2, ← dropContext_isOwner]
      exact ValueBound.discard _ _ (callInd_value I R hR J owner hJ args (h.reads _ _) hplan f hf heq)
    · rename_i r _
      exact (Fin.cast ((D.passt_sig hf).gruende.trans hr) r).elim0
    · trivial
    · trivial
  | _, _, _, _, _, _, _, _, .locks L hr body hb, σ, ρ, hk, h => by
    simp only [execStmt]
    exact BPost.mapMeta _ _ (fun σ => MetaSame.gives A σ L)
      (ob_sound hR hO hb _ ρ hk (h.meta (MetaSame.takes A σ L)))
  | _, _, _, _, _, _, _, _, .breaking i body hb, σ, ρ, hk, h => by
    simp only [execStmt]
    exact ob_sound hR hO hb σ ρ hk h
  | _, _, _, _, _, _, _, _, .traverse t inv body hentry _ hb hback, σ, ρ, _, h => by
    simp only [execStmt]
    have hlen : _ = _ := (h.weaken hentry).length
    exact traverse_post _ _ (fun σ ρ => MetaSame.reads A σ _ _)
      (fun σ ρ h' => ob_sound hR hO hb σ ρ (by simp; omega) h') hback hlen _ σ ρ (h.weaken hentry)
  | _, _, _, _, _, _, _, _, .retry n bis body ueberlauf hentry _ hb hback hu, σ, ρ, _, h => by
    simp only [execStmt]
    have hlen : _ = _ := (h.weaken hentry).length
    exact retry_post _ _ _ (fun σ ρ => MetaSame.reads A σ _ _)
      (fun σ ρ h' => BPost.weaken _ hback (ob_sound hR hO hb σ ρ (by omega) h'))
      (fun σ ρ h' => ob_sound hR hO hu σ ρ (by omega) h') hlen n σ ρ (h.weaken hentry)
  | _, _, _, _, _, _, _, _, .forever a inv body hentry _ hb hback, σ, ρ, _, h => by
    simp only [execStmt]
    have hlen : _ = _ := (h.weaken hentry).length
    exact forever_post a _ _ (fun σ ρ => MetaSame.reads A σ _ _)
      (fun σ ρ h' => BPost.weaken _ hback (ob_sound hR hO hb σ ρ (by omega) h')) hlen passes σ ρ
      (h.weaken hentry)
  | _, _, _, _, _, _, _, _, .axiomCall a args hres hw hg hd hgd hfree _, σ, ρ, _, h => by
    simp only [execStmt]
    split
    · rename_i σ' v heq
      have hσ : σ' = (axiomAntwort O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwort_fst] at hσ
      rw [hσ]
      exact ((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)
    · trivial
  | _, _, _, _, _, _, _, _, .regWrite r hk' e _, σ, ρ, _, h => by
    simp only [execStmt]
    exact h.reads _ _
  | _, _, _, _, _, _, _, _, .transition r hk' m hm hl maske bits, σ, ρ, _, h => by
    simp only [execStmt]
    exact h.fragt _
  | _, _, _, _, _, _, _, _, .publish g e payload hp hw hL hg _, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).meta (MetaSame.writeGlob A _ g _ _ hg)
  | _, _, _, _, _, _, _, _, .advances m a hm hs, σ, ρ, _, h => by
    simp only [execStmt]
    exact h
  | _, _, _, _, _, _, _, _, .retires m st hm a, σ, ρ, _, h => by
    simp only [execStmt]
    exact h
  | _, _, _, _, _, _, _, _, .ret e hΛ he, σ, ρ, _, h => by
    simp only [execStmt]
    exact (h.reads _ _).doneValue e he _ _
  | _, _, _, _, _, _, _, _, .retWhy r hΛ hf, σ, ρ, _, h => by
    simp only [execStmt]
    exact h.doneReason hf
  | _, _, _, _, _, _, _, _, .leave hl hx, σ, ρ, _, h => by
    simp only [execStmt]
    exact ⟨_, hx, h⟩
  | _, _, _, _, _, _, _, _, .next hl hx, σ, ρ, _, h => by
    simp only [execStmt]
    exact ⟨_, hx, h⟩

theorem ob_sound (hR : Respects A I.contracts R) (hO : GutO O) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c' : Context} {b : Block D V l Γ Λ Λ'},
      OB A I out k c b c' → ∀ (σ : World D) (ρ : Env D Γ), k.references.length ≤ Γ.length →
        Holds A fr s0 c σ ρ → BPost A fr s0 out k c' (execBlock O passes R b σ ρ)
  | _, _, _, _, _, _, _, _, .nil, σ, ρ, _, h => by
    simp only [execBlock]
    exact h
  | _, _, _, _, _, _, _, _, .cons s rest hs hr, σ, ρ, hk, h => by
    simp only [execBlock]
    have h1 := os_sound hR hO hs σ ρ hk h
    generalize execStmt O passes R s σ ρ = o at h1 ⊢
    cases o with
    | ok σ' ρ' => exact ob_sound hR hO hr σ' ρ' hk h1
    | _ => exact h1
  | _, _, _, _, _, _, _, _, .weaken b hb hw, σ, ρ, hk, h =>
    BPost.weaken _ hw (ob_sound hR hO hb σ ρ hk h)
  | _, Γ, _, _, _, _, _, _, .dead s rest hs, σ, ρ, hk, h => by
    simp only [execBlock]
    have h1 := os_sound hR hO (hs ⟨List.replicate (Γ.length + 1) none, fun _ => none, 0⟩
      ⟨fun _ _ => rfl, fun ref hm i he => by
        simp only [List.mem_replicate] at hm; rw [hm.2] at he; cases he⟩) σ ρ hk h
    generalize execStmt O passes R s σ ρ = o at h1 ⊢
    cases o with
    | ok σ' ρ' => have := h1.length; simp at this
    | _ => exact h1
  | _, _, _, _, _, _, _, _, .bind e rest _ hr, σ, ρ, hk, h => by
    simp only [execBlock]
    exact BPost.schrumpf hk _ (ob_sound hR hO hr _ _ (by simp; omega) ((h.reads _ _).bindExpr e _ _))
  | _, _, _, _, _, _, _, _, .bindCall f args he hp hr rest _ hplan hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i σ' v heq
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        (ValueBound.bind _ he v (call_value I R hR f args (h.reads _ _) hplan heq)))
    · rename_i r _
      exact (Fin.cast hr r).elim0
    · trivial
    · trivial
  | _, _, _, _, _, _, _, _, .bindCallInd p args he hp hr rest J owner hJ _ _ hplan hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    rename_i f hf _
    split
    · rename_i σ' v heq
      have hb := ValueBound.bind _ (ergSig hf he) v
        (callInd_value I R hR J owner hJ args (h.reads _ _) hplan f hf heq)
      rw [resultContext_isOwner, (hJ f hf).2] at hb
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega) hb)
    · rename_i r _
      exact (Fin.cast ((D.passt_sig hf).gruende.trans hr) r).elim0
    · trivial
    · trivial
  | _, _, _, _, _, _, _, _, .bindCallElse f args he hp hr err rest _ hplan herr hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i σ' v heq
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        (ValueBound.bind _ he v (call_value I R hR f args (h.reads _ _) hplan heq)))
    · rename_i σ' r heq
      exact EPost.toB _ (EPost.schrumpf hk _ (oe_sound hR hO herr _ _ (by simp; omega)
        ((call_reason I R hR f args (h.reads _ _) hplan heq).bindNone (τ := .why _) r)))
    · trivial
    · trivial
  | _, _, _, _, _, _, _, _, .bindAxiom a args he hw hg hd hgd rest hfree _ hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i σ' v heq
      have hσ : σ' = (axiomAntwort O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwort_fst] at hσ
      subst hσ
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        ((((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)).bindNone _))
    · trivial
  | _, _, _, _, _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest hfree _ herr hrest,
      σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i σ' v heq
      have hσ : σ' = (axiomAntwortSonst O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwortSonst_fst, axiomAntwort_fst] at hσ
      subst hσ
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        ((((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)).bindNone _))
    · rename_i σ' r heq
      have hσ : σ' = (axiomAntwortSonst O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwortSonst_fst, axiomAntwort_fst] at hσ
      subst hσ
      exact EPost.toB _ (EPost.schrumpf hk _ (oe_sound hR hO herr _ _ (by simp; omega)
        ((((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)).bindNone _)))
    · trivial
  | _, _, _, _, _, _, _, _, .regRead r hk' rest hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i v _
      split
      · exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega) ((h.fragt _).bindNone v))
      · trivial
    · trivial
  | _, _, _, _, _, _, _, _, .regReadElse r hk' zusage sonst rest _ hs hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i v _
      split
      · exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega) (((h.fragt _).reads _ _).bindNone v))
      · exact EPost.toB _ (oe_sound hR hO hs _ _ hk ((h.fragt _).reads _ _))
    · trivial
  | _, _, _, _, _, _, _, _, .awaits g payload hp hL ha rest hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega) (((h.fragt _).reads _ _).bindNone _))
    · trivial
  | _, _, _, _, _, _, _, _, .exchange g neu hw hL rest hg _ hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
      (((h.reads _ _).meta (MetaSame.writeGlob A _ g _ _ hg)).bindNone _))
  | _, _, _, _, _, _, _, _, .narrow e lo' hi' sonst rest _ hs hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i hn
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        ((h.reads _ _).bindNarrow e _ _ lo' hi' hn))
    · exact EPost.toB _ (oe_sound hR hO hs _ _ hk (h.reads _ _))
  | _, _, _, _, _, _, _, _, .check cond sonst rest _ hs hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · exact ob_sound hR hO hrest _ _ hk (h.reads _ _)
    · exact EPost.toB _ (oe_sound hR hO hs _ _ hk (h.reads _ _))
  | _, _, _, _, _, _, _, _, .float op a b lo hi rest _ _ hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i v _
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        ((h.reads _ _).bindNone (τ := .fl lo hi) v))
    · trivial
  | _, _, _, _, _, _, _, _, .floatLit q lo hi rest hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i v _
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega) (h.bindNone (τ := .fl lo hi) v))
    · trivial
  | _, _, _, _, _, _, _, _, .floatOf e lo hi rest _ hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i v _
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        ((h.reads _ _).bindNone (τ := .fl lo hi) v))
    · trivial
  | _, _, _, _, _, _, _, _, .floatNarrow e lo hi sonst rest _ hs hrest, σ, ρ, hk, h => by
    simp only [execBlock]
    split
    · rename_i v _
      exact BPost.schrumpf hk _ (ob_sound hR hO hrest _ _ (by simp; omega)
        ((h.reads _ _).bindNone (τ := .fl lo hi) v))
    · exact EPost.toB _ (oe_sound hR hO hs _ _ hk (h.reads _ _))
  | _, _, _, _, _, _, _, _, .allocList e lo' hi' voll g e2 hwK hLK t f i ev hw hL rest he hhi hg he2 hn _ _ _
      hvoll hrest, σ, ρ, hk, h =>
    allocList_post O passes R e lo' hi' voll g e2 hwK hLK t f i ev hw hL rest he hhi hg he2 hn hk h
      (fun σ' h' => oe_sound hR hO hvoll σ' ρ hk h')
      (fun σ' ρ' h' => ob_sound hR hO hrest σ' ρ' (by simp; omega) h')
  | _, _, _, _, _, _, _, _, .allocCounter e lo' hi' voll t f i ev hw hL g e2 hwG hLG rest he hhi hn hg he2 _ _ _
      hvoll hrest, σ, ρ, hk, h =>
    allocCounter_post O passes R e lo' hi' voll t f i ev hw hL g e2 hwG hLG rest he hhi hn hg he2 hk h
      (fun σ' h' => oe_sound hR hO hvoll σ' ρ hk h')
      (fun σ' ρ' h' => ob_sound hR hO hrest σ' ρ' (by simp; omega) h')
  | _, _, _, _, _, _, _, _, .release t f i e hw hL g e2 hwK hLK rest ht hf hip he hg he2 hc hrest, σ, ρ, hk, h =>
    release_post O passes R t f i e hw hL g e2 hwK hLK rest ht hf hip he hg he2 hc h
      (fun σ' ρ' h' => ob_sound hR hO hrest σ' ρ' hk h')

theorem oe_sound (hR : Respects A I.contracts R) (hO : GutO O) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {eb : Endblock D V l Γ Λ},
      OE A I out k c eb → ∀ (σ : World D) (ρ : Env D Γ), k.references.length ≤ Γ.length →
        Holds A fr s0 c σ ρ → EPost A fr s0 out k (execEnd O passes R eb σ ρ)
  | _, _, _, _, _, _, .ret e hΛ he, σ, ρ, _, h => by
    simp only [execEnd]
    exact (h.reads _ _).doneValue e he _ _
  | _, _, _, _, _, _, .retWhy r hΛ hf, σ, ρ, _, h => by
    simp only [execEnd]
    exact h.doneReason hf
  | _, _, _, _, _, _, .leave hl hx, σ, ρ, _, h => by
    simp only [execEnd]
    exact ⟨_, hx, h⟩
  | _, _, _, _, _, _, .next hl hx, σ, ρ, _, h => by
    simp only [execEnd]
    exact ⟨_, hx, h⟩
  | _, _, _, _, _, _, .cons s rest hs hr, σ, ρ, hk, h => by
    simp only [execEnd]
    have h1 := os_sound hR hO hs σ ρ hk h
    generalize execStmt O passes R s σ ρ = o at h1 ⊢
    cases o with
    | ok σ' ρ' => exact oe_sound hR hO hr σ' ρ' hk h1
    | _ => exact h1
  | _, Γ, _, _, _, _, .dead s rest hs, σ, ρ, hk, h => by
    simp only [execEnd]
    have h1 := os_sound hR hO (hs ⟨List.replicate (Γ.length + 1) none, fun _ => none, 0⟩
      ⟨fun _ _ => rfl, fun ref hm i he => by
        simp only [List.mem_replicate] at hm; rw [hm.2] at he; cases he⟩) σ ρ hk h
    generalize execStmt O passes R s σ ρ = o at h1 ⊢
    cases o with
    | ok σ' ρ' => have := h1.length; simp at this
    | _ => exact h1
  | _, _, _, _, _, _, .bind e rest _ hr, σ, ρ, hk, h => by
    simp only [execEnd]
    exact EPost.schrumpf hk _ (oe_sound hR hO hr _ _ (by simp; omega) ((h.reads _ _).bindExpr e _ _))
  | _, _, _, _, _, _, .bindCall f args he hp hr rest _ hplan hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · rename_i σ' v heq
      exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega)
        (ValueBound.bind _ he v (call_value I R hR f args (h.reads _ _) hplan heq)))
    · rename_i r _
      exact (Fin.cast hr r).elim0
    · trivial
    · trivial
  | _, _, _, _, _, _, .bindCallElse f args he hp hr err rest _ hplan herr hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · rename_i σ' v heq
      exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega)
        (ValueBound.bind _ he v (call_value I R hR f args (h.reads _ _) hplan heq)))
    · rename_i σ' r heq
      exact EPost.schrumpf hk _ (oe_sound hR hO herr _ _ (by simp; omega)
        ((call_reason I R hR f args (h.reads _ _) hplan heq).bindNone (τ := .why _) r))
    · trivial
    · trivial
  | _, _, _, _, _, _, .bindAxiom a args he hw hg hd hgd rest hfree _ hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · rename_i σ' v heq
      have hσ : σ' = (axiomAntwort O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwort_fst] at hσ
      subst hσ
      exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega)
        ((((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)).bindNone _))
    · trivial
  | _, _, _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest hfree _ herr hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · rename_i σ' v heq
      have hσ : σ' = (axiomAntwortSonst O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwortSonst_fst, axiomAntwort_fst] at hσ
      subst hσ
      exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega)
        ((((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)).bindNone _))
    · rename_i σ' r heq
      have hσ : σ' = (axiomAntwortSonst O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwortSonst_fst, axiomAntwort_fst] at hσ
      subst hσ
      exact EPost.schrumpf hk _ (oe_sound hR hO herr _ _ (by simp; omega)
        ((((h.reads _ _).fragt _).meta (MetaSame.axiom hO hfree _ _)).bindNone _))
    · trivial
  | _, _, _, _, _, _, .regRead r hk' rest hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · rename_i v _
      split
      · exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega) ((h.fragt _).bindNone v))
      · trivial
    · trivial
  | _, _, _, _, _, _, .regReadElse r hk' zusage sonst rest _ hs hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · rename_i v _
      split
      · exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega) (((h.fragt _).reads _ _).bindNone v))
      · exact oe_sound hR hO hs _ _ hk ((h.fragt _).reads _ _)
    · trivial
  | _, _, _, _, _, _, .awaits g payload hp hL ha rest hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    · exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega) (((h.fragt _).reads _ _).bindNone _))
    · trivial
  | _, _, _, _, _, _, .bindCallInd p args he hp hr rest J owner hJ _ _ hplan hrest, σ, ρ, hk, h => by
    simp only [execEnd]
    split
    rename_i f hf _
    split
    · rename_i σ' v heq
      have hb := ValueBound.bind _ (ergSig hf he) v
        (callInd_value I R hR J owner hJ args (h.reads _ _) hplan f hf heq)
      rw [resultContext_isOwner, (hJ f hf).2] at hb
      exact EPost.schrumpf hk _ (oe_sound hR hO hrest _ _ (by simp; omega) hb)
    · rename_i r _
      exact (Fin.cast ((D.passt_sig hf).gruende.trans hr) r).elim0
    · trivial
    · trivial

theorem oarms_sound (hR : Respects A I.contracts R) (hO : GutO O) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} {k c c' : Context}
      {arms : Arms D V l Γ Λ Λ' cs}, OArms A I out k c arms c' →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ), k.references.length ≤ Γ.length →
        Holds A fr s0 c σ ρ → BPost A fr s0 out k c' (execArms O passes R arms v σ ρ)
  | _, _, _, _, _, _, _, _, _, .nil, ⟨i, _⟩, _, _, _, _ => i.elim0
  | _, _, _, _, _, _, _, _, _, .cons (ca := ca) b rest hb hw hr, ⟨⟨0, _⟩, nutz⟩, σ, ρ, hk, h => by
    simp only [execArms]
    exact BPost.weaken _ hw (BPost.schrumpfArm hk ca _
      (ob_sound hR hO hb _ _ (Nat.le_trans hk (armCtx_length _ ca)) (h.arm ca nutz)))
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨⟨i + 1, hi⟩, nutz⟩, σ, ρ, hk, h => by
    simp only [execArms]
    exact oarms_sound hR hO hr _ σ ρ hk h

theorem ogrund_sound (hR : Respects A I.contracts R) (hO : GutO O) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {k c c' : Context}
      {arms : GrundArms D V l Γ Λ Λ' n}, OGrund A I out k c arms c' →
      ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ), k.references.length ≤ Γ.length →
        Holds A fr s0 c σ ρ → BPost A fr s0 out k c' (execGrund O passes R arms r σ ρ)
  | _, _, _, _, _, _, _, _, _, .nil, r, _, _, _, _ => r.elim0
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨0, _⟩, σ, ρ, hk, h => by
    simp only [execGrund]
    exact BPost.weaken _ hw (ob_sound hR hO hb σ ρ hk h)
  | _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, ⟨i + 1, hi⟩, σ, ρ, hk, h => by
    simp only [execGrund]
    exact ogrund_sound hR hO hr _ σ ρ hk h

end

end Sound

#print axioms ob_sound
#print axioms oe_sound

end Gabbro.Grammatik.ArenaOwnership.Body
