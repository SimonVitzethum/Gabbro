/-
  File:      Grammatik/ArenaHashForm.lean
  Subject:   THE EXECUTED FORMS OF A HASH TABLE WITH CHAINING, BUCKET HEADS IN A TABLE FIELD (PLAN-DYNAMIC.md section
             8a.1, third pass). `ArenaHash.lean` proves the abstract moves over an abstract head function `hd`; here the
             head function is the field `hf` of a SECOND table `bt` (one slot per bucket, a field of type
             `int 0 count` where `count` is the arena's), and the moves are `Block`s over the existing statements.

    `Block.hashPush L H b x rest`  =  `lnk[x] = B[b].hd;  B[b].hd = x;  rest`
    `Block.hashPop L H b voll rest` =  `let i = B[b].hd (narrow, else voll);  B[b].hd = lnk[i];  rest`
    `Block.hashKopf H b voll rest`  =  `let i = B[b].hd (narrow, else voll);  rest`

  The unlink inside one chain is the list form `Block.linkUnlink` (it moves no bucket head). The invariant on a world is
  `HashOk A L H σ := HashOkF count (L.wert σ) (H.wert σ) (count bt) (A.Lebt σ)`; `hash_push_zug`, `hash_pop_zug` and
  `hash_unlink_zug` keep it on the executed forms, for every continuation.
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaLinkForm
import Grammatik.Bausteine.Arena.Struktur.ArenaHash

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-- **The bucket heads, in a table field:** the table `bt` has one slot per bucket; its field `hf` holds the head of the
    chain (an index of the arena, `count` for the empty chain). A table of its own, so no arena store moves a head. -/
structure BucketKopf (A : FreiForm D) where
  bt : D.Tab
  hf : D.Feld bt
  hty : D.typ bt hf = Ty.int 0 (D.count A.tab)
  hbt : bt ≠ A.tab

namespace BucketKopf
variable {A : FreiForm D}

/-- The head of bucket `b`, read out of a world. -/
def wert (H : BucketKopf A) (σ : World D) (b : Int) : Int := (Wert.umTyp H.hty (σ.slots H.bt b H.hf)).n

@[simp] theorem wert_lese (H : BucketKopf A) (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) (b : Int) :
    H.wert (σ.lese Λ o) b = H.wert σ b := rfl

@[simp] theorem wert_schreibGlob (H : BucketKopf A) (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) (b : Int) : H.wert (σ.schreibGlob g Λ v) b = H.wert σ b := rfl

/-- A store into the ARENA table leaves every bucket head. -/
theorem wert_schreibSlot_arena (H : BucketKopf A) (σ : World D) (Λ : List (Res D)) (k : Int) (f : D.Feld A.tab)
    (v : Wert D (D.typ A.tab f)) (b : Int) : H.wert (σ.schreibSlot A.tab Λ k f v) b = H.wert σ b := by
  simp only [wert, World.schreibSlot, World.merke, World.storeSlot, dif_neg H.hbt]

/-- A store into the head of bucket `b` puts the written value there ... -/
theorem wert_schreibSlot_selbst (H : BucketKopf A) (σ : World D) (Λ : List (Res D)) (b : Int)
    (v : Wert D (D.typ H.bt H.hf)) : H.wert (σ.schreibSlot H.bt Λ b H.hf v) b = (Wert.umTyp H.hty v).n := by
  simp only [wert, World.slots_schreibSlot_selbst]

/-- ... and leaves the head of every other bucket. -/
theorem wert_schreibSlot_anderer (H : BucketKopf A) (σ : World D) (Λ : List (Res D)) (b : Int)
    (v : Wert D (D.typ H.bt H.hf)) (b' : Int) (h : b' ≠ b) :
    H.wert (σ.schreibSlot H.bt Λ b H.hf v) b' = H.wert σ b' := by
  simp only [wert, World.slots_schreibSlot_anderer _ _ _ _ _ _ _ _ h]

end BucketKopf

/-- A store into the bucket table leaves every link of the arena. -/
theorem LinkFeld.wert_schreibSlot_bucket {A : FreiForm D} (L : LinkFeld A) (H : BucketKopf A) (σ : World D)
    (Λ : List (Res D)) (b : Int) (v : Wert D (D.typ H.bt H.hf)) :
    L.wert (σ.schreibSlot H.bt Λ b H.hf v) = L.wert σ :=
  funext fun j => by
    simp only [LinkFeld.wert, World.slots_schreibSlot_andere_tabelle _ _ _ _ _ _ _ _ _ H.hbt.symm]

theorem FreiForm.naechst_schreibSlot_bucket (A : FreiForm D) (H : BucketKopf A) (σ : World D) (Λ : List (Res D))
    (b : Int) (v : Wert D (D.typ H.bt H.hf)) (j : Int) :
    A.naechst (σ.schreibSlot H.bt Λ b H.hf v) j = A.naechst σ j := by
  simp only [FreiForm.naechst, World.slots_schreibSlot_andere_tabelle _ _ _ _ _ _ _ _ _ H.hbt.symm]

/-- **The invariant of a hash table with chaining on a world.** -/
def HashOk {A : FreiForm D} (L : LinkFeld A) (H : BucketKopf A) (σ : World D) : Prop :=
  HashOkF (D.count A.tab) (L.wert σ) (H.wert σ) (D.count H.bt) (A.Lebt σ)

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {A : FreiForm D}

/-- The arena index `x`, at the bucket head field's declared type. -/
def idxAlsBucket (H : BucketKopf A) (x : Var Γ (Ty.index (D.count A.tab))) : Expr D Γ Λ (D.typ H.bt H.hf) :=
  Expr.umTyp H.hty.symm
    (Expr.widen (lo := 0) (hi := D.count A.tab - 1) (lo' := 0) (hi' := D.count A.tab) (by omega) (by omega)
      (Expr.var x))

/-- **`lnk[x] = B[b].hd;  B[b].hd = x;  rest`** -- link the slot `x` in at the head of bucket `b`. -/
def hashPush (L : LinkFeld A) (H : BucketKopf A) (b : Var Γ (Ty.index (D.count H.bt)))
    (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwB : V.schreibt H.bt = true) (hLB : darf D H.bt Λ) (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .cons (.assignSlot A.tab L.f (Expr.var x)
      (Expr.umTyp (H.hty.trans L.hf.symm) (Expr.slot H.bt H.hf (Expr.var b) hLB)) hwT hLT)
    (.cons (.assignSlot H.bt H.hf (Expr.var b) (idxAlsBucket H x) hwB hLB) rest)

/-- **`let i = B[b].hd else voll;  B[b].hd = lnk[i];  rest`** -- take the head off bucket `b`. -/
def hashPop (L : LinkFeld A) (H : BucketKopf A) (b : Var Γ (Ty.index (D.count H.bt)))
    (hLT : darf D A.tab Λ) (hwB : V.schreibt H.bt = true) (hLB : darf D H.bt Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp H.hty (Expr.slot H.bt H.hf (Expr.var b) hLB)) 0 (D.count A.tab - 1) voll
    (.cons (.assignSlot H.bt H.hf (Expr.var (.there b))
      (Expr.umTyp (L.hf.trans H.hty.symm) (Expr.slot A.tab L.f (Expr.var .here) hLT)) hwB hLB) rest)

/-- **`let i = B[b].hd else voll;  rest`** -- read the head of bucket `b` without moving anything. -/
def hashKopf (H : BucketKopf A) (b : Var Γ (Ty.index (D.count H.bt))) (hLB : darf D H.bt Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp H.hty (Expr.slot H.bt H.hf (Expr.var b) hLB)) 0 (D.count A.tab - 1) voll rest

end Block

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (L : LinkFeld A) (H : BucketKopf A)

/-- **`hashPush` leaves:** the head of bucket `b` is `x`, the link of `x` is the old head, every other head and link stays,
    and the allocator's views stay. Valid for every continuation `rest`. -/
theorem hashPush_ausfuehren (b : Var Γ (Ty.index (D.count H.bt))) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwB : V.schreibt H.bt = true)
    (hLB : darf D H.bt Λ) (rest : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.hashPush L H b x hwT hLT hwB hLB rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [L.f] [] σ σ' ∧
      H.wert σ' (ρ.get b).n = (ρ.get x).n ∧ L.wert σ' (ρ.get x).n = H.wert σ (ρ.get b).n ∧
      (∀ b', b' ≠ (ρ.get b).n → H.wert σ' b' = H.wert σ b') ∧
      (∀ j, j ≠ (ρ.get x).n → L.wert σ' j = L.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  refine ⟨_, rfl, ?_, ?_⟩
  · refine ⟨fun C hC => funext fun j => ?_, fun G' _ => rfl⟩
    have hne : C.f ≠ L.f := fun e => hC (by simp only [e, List.mem_cons, List.not_mem_nil, or_false])
    simp only [LinkFeld.wert, orte_umTyp, eval_umTyp,
  World.slots_schreibSlot_andere_tabelle _ _ _ _ _ _ _ _ _ H.hbt.symm, World.slots_lese,
  World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ hne]
  simp only [eval, Block.idxAlsBucket, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
    LinkKopf.st_schreibSlot, LinkKopf.st_lese, FreiForm.kopfSt_schreibSlot, FreiForm.kopfSt_lese,
    ArenaForm.stand_lese, ArenaForm.stand_schreibSlot, FreiForm.naechst_lese, BucketKopf.wert_lese]
  refine ⟨?_, ?_, fun b' hb' => ?_, fun j hj => ?_, ?_, fun j => ?_, ?_⟩
  · rw [BucketKopf.wert_schreibSlot_selbst]
    exact umTyp_rund_n H.hty _
  · rw [LinkFeld.wert_schreibSlot_bucket]
    simp only [LinkFeld.wert_lese]
    exact (L.wert_schreibSlot_selbst _ _ _ _).trans (umTyp_trans_n _ _ _)
  · rw [H.wert_schreibSlot_anderer _ _ _ _ _ hb']
    simp only [BucketKopf.wert_lese, BucketKopf.wert_schreibSlot_arena]
  · rw [LinkFeld.wert_schreibSlot_bucket]
    simp only [LinkFeld.wert_lese]
    exact L.wert_schreibSlot_anderer _ _ _ _ _ hj
  · trivial
  · rw [FreiForm.naechst_schreibSlot_bucket]
    simp only [FreiForm.naechst_lese]
    exact A.naechst_schreibSlot_ne _ _ _ _ _ L.h2 _
  · trivial

/-- **`hashPop` leaves:** the binder holds the old head `i` of bucket `b`, the head of bucket `b` is the link of `i`, no other
    head and no link moves, and the allocator's views stay. The bucket must be non-empty. Valid for every continuation. -/
theorem hashPop_ausfuehren (b : Var Γ (Ty.index (D.count H.bt)))
    (hLT : darf D A.tab Λ) (hwB : V.schreibt H.bt = true) (hLB : darf D H.bt Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hne : H.wert σ (ρ.get b).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.hashPop L H b hLT hwB hLB voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = H.wert σ (ρ.get b).n ∧ H.wert σ' (ρ.get b).n = L.wert σ (H.wert σ (ρ.get b).n) ∧
      (∀ b', b' ≠ (ρ.get b).n → H.wert σ' b' = H.wert σ b') ∧ (∀ j, L.wert σ' j = L.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ H.wert σ (ρ.get b).n ∧ H.wert σ (ρ.get b).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp H.hty (σ.slots H.bt (ρ.get b).n H.hf)).lo_le, by omega⟩
  simp only [Block.hashPop, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  refine ⟨?s, ?k, ?e, ?n, ?r⟩
  case e => rfl
  case n => rfl
  case r =>
    simp only [eval, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append, List.cons_append, List.append_nil,
      LinkKopf.st_schreibSlot, LinkKopf.st_lese, FreiForm.kopfSt_schreibSlot, FreiForm.kopfSt_lese,
      ArenaForm.stand_lese, ArenaForm.stand_schreibSlot, FreiForm.naechst_lese, BucketKopf.wert_lese,
      Env.get]
    refine ⟨?_, fun b' hb' => ?_, fun j => ?_, trivial, fun j => ?_, trivial⟩
    · exact (H.wert_schreibSlot_selbst _ _ _ _).trans (umTyp_trans_n _ _ _)
    · exact H.wert_schreibSlot_anderer _ _ _ _ _ hb'
    · rw [LinkFeld.wert_schreibSlot_bucket]
      simp only [LinkFeld.wert_lese]
    · rw [FreiForm.naechst_schreibSlot_bucket]
      simp only [FreiForm.naechst_lese]

/-- **`hashPop` on an empty bucket takes its `else`:** nothing moves but the recorded read. -/
theorem hashPop_voll (b : Var Γ (Ty.index (D.count H.bt)))
    (hLT : darf D A.tab Λ) (hwB : V.schreibt H.bt = true) (hLB : darf D H.bt Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hn : ¬ H.wert σ (ρ.get b).n < D.count A.tab) :
    execBlock (V := V) O passes R (Block.hashPop L H b hLT hwB hLB voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inl H.bt]) ρ).zuAusgang := by
  have hn' : ¬ ((0 : Int) ≤ H.wert σ (ρ.get b).n ∧ H.wert σ (ρ.get b).n ≤ D.count A.tab - 1) := by
    intro h; exact hn (by omega)
  simp only [Block.hashPop, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_neg (by exact hn')]

/-- **Reading the head of bucket `b` binds it when the bucket is non-empty.** -/
theorem hashKopf_ausfuehren (b : Var Γ (Ty.index (D.count H.bt))) (hLB : darf D H.bt Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D)
    (ρ : Env D Γ) (hne : H.wert σ (ρ.get b).n < D.count A.tab) :
    ∃ k : Wert D (Ty.index (D.count A.tab)),
      execBlock (V := V) O passes R (Block.hashKopf H b hLB voll rest) σ ρ
        = (execBlock (V := V) O passes R rest (σ.lese Λ [Sum.inl H.bt]) (.cons k ρ)).schrumpf ∧
      k.n = H.wert σ (ρ.get b).n := by
  have hk : (0 : Int) ≤ H.wert σ (ρ.get b).n ∧ H.wert σ (ρ.get b).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp H.hty (σ.slots H.bt (ρ.get b).n H.hf)).lo_le, by omega⟩
  simp only [Block.hashKopf, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  exact ⟨_, rfl, rfl⟩

/-- **`linkUnlink` inside a bucket leaves:** the binder holds `i = lnk[p]`, the link of `p` is the link of `i`, no other link
    and no bucket head moves, and the allocator's views stay. `i` must be a slot. Valid for every continuation. -/
theorem hashUnlink_ausfuehren (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true)
    (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hi : L.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.linkUnlink L p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = L.wert σ (ρ.get p).n ∧ L.wert σ' (ρ.get p).n = L.wert σ (L.wert σ (ρ.get p).n) ∧
      (∀ j, j ≠ (ρ.get p).n → L.wert σ' j = L.wert σ j) ∧ (∀ b, H.wert σ' b = H.wert σ b) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ L.wert σ (ρ.get p).n ∧ L.wert σ (ρ.get p).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp L.hf (σ.slots A.tab (ρ.get p).n L.f)).lo_le, by omega⟩
  simp only [Block.linkUnlink, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  refine ⟨?s, ?k, ?e, ?n, ?r⟩
  case e => rfl
  case n => rfl
  case r =>
    simp only [eval, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append, List.cons_append, List.append_nil,
      LinkFeld.wert_lese, A.kopfSt_schreibSlot, FreiForm.naechst_lese, FreiForm.kopfSt_lese,
      ArenaForm.stand_lese, ArenaForm.stand_schreibSlot, A.naechst_schreibSlot_ne _ _ _ _ _ L.h2,
      Env.get_cons_there, Env.get_cons_here, BucketKopf.wert_lese]
    refine ⟨?_, fun j hj => ?_, fun b => ?_, trivial, fun _ => trivial, trivial⟩
    · exact L.wert_schreibSlot_selbst _ _ _ _
    · exact L.wert_schreibSlot_anderer _ _ _ _ _ hj
    · rw [BucketKopf.wert_schreibSlot_arena]
      simp only [BucketKopf.wert_lese]

end Bedeutung

end Gabbro.Grammatik
