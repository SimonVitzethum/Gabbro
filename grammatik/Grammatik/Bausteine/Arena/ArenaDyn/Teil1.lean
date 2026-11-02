module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Arena.ArenaZucker

@[expose] public section



public import Grammatik.Bausteine.Arena.ArenaDyn.Teil1Basis

namespace Gabbro.Grammatik.ArenaDyn

  Everything above is arithmetic on a `Nat` record: it says what a commit
  sequence does, and it says it about numbers. This section puts the same
  discipline where `ArenaZucker.lean` put the static one -- on the EXISTING
  `Block`, as sugar, so that `theorem gabbro_ziel` covers a dynamic arena
  program with no new constructor, no new machine arm and no re-proof.

  The shape (the plan fixes it, this section builds exactly it):

  * the table spans the CEILING -- `count tab = M`, the reserved virtual
    region, never touched implicitly;
  * beside the `used` counter of `ArenaForm` stands a SECOND word over the
    same range, the committed prefix `c`, read through a `stand`-style
    accessor (`komSt`);
  * `grow A by n else B;` is `Block.narrow` of `c + n` into `0 .. M` with a
    store into that word -- it fits, or `B` runs;
  * `let i = alloc A (v) else B;` on a dynamic arena is ONE test more than
    the static form: `Block.pruefung` on `used < committed`, and then the
    static `Block.arenaAlloc` unchanged underneath.

  The prefix property (no fragmentation, no holes) is not an assumption
  here: commit only ever extends the word, and the only form that writes it
  is `dynGrowB`. -/

section Form

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **What a declaration must carry for `arena A capacity lo .. hi max M of T`.**
    An `ArenaForm` whose table spans the ceiling, plus the committed word.
    `lo` is not here for the same reason it is not in `ArenaForm`: it is a
    static count the Rust checker keeps (`N212`). -/
structure DynForm (D : Deklaration) extends ArenaForm D where
  /-- The committed-prefix word: how much of the reservation is usable. -/
  komm : D.Glob
  /-- It ranges over `0 .. M` -- `M` inclusive, because a fully committed
      arena is a state the word must be able to name. -/
  hk : D.gtyp komm = Ty.int 0 (D.count tab)
  /-- TWO words, not one. Every frame lemma below rests on this: a store
      into the committed word leaves the used counter where it stood. -/
  hzwei : komm ≠ zaehl

namespace DynForm

/-- **The committed prefix, read out of a world** -- the counterpart of
    `ArenaForm.stand`, and the number every statement below speaks in. -/
def komSt (A : DynForm D) (σ : World D) : Int := (Wert.umTyp A.hk (σ.globs A.komm)).n

theorem komSt_le (A : DynForm D) (σ : World D) : A.komSt σ ≤ D.count A.tab :=
  (Wert.umTyp A.hk (σ.globs A.komm)).le_hi

theorem komSt_nonneg (A : DynForm D) (σ : World D) : 0 ≤ A.komSt σ :=
  (Wert.umTyp A.hk (σ.globs A.komm)).lo_le

/-- Recording a read does not move the committed word. -/
@[simp] theorem komSt_lese (A : DynForm D) (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) : A.komSt (σ.lese Λ o) = A.komSt σ := by rfl

/-- A slot store does not move the committed word. -/
@[simp] theorem komSt_schreibSlot (A : DynForm D) (σ : World D) (Λ : List (Res D))
    (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    A.komSt (σ.schreibSlot t Λ k f v) = A.komSt σ := by rfl

/-- A store into the committed word puts exactly the written value there. -/
@[simp] theorem komSt_schreibGlob (A : DynForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.komm)) :
    A.komSt (σ.schreibGlob A.komm Λ v) = (Wert.umTyp A.hk v).n := by
  simp only [komSt, World.schreibGlob, World.merke, World.storeGlob, dif_pos]

/-- **THE FRAME, one half:** a store into the committed word leaves the used
    counter where it stood. This is `hzwei` doing its work -- `storeGlob`
    moves one global, and the two words are two. -/
@[simp] theorem stand_schreibGlob_komm (A : DynForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.komm)) :
    A.stand (σ.schreibGlob A.komm Λ v) = A.stand σ := by
  simp only [ArenaForm.stand, World.schreibGlob, World.merke, World.storeGlob,
    dif_neg (fun h : A.zaehl = A.komm => A.hzwei h.symm)]

/-- **THE FRAME, the other half:** a store into the committed word touches no
    slot. Together with the line above: `grow` moves the one word and nothing
    else in memory. -/
@[simp] theorem slots_schreibGlob_komm (A : DynForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.komm)) :
    (σ.schreibGlob A.komm Λ v).slots = σ.slots := by rfl

end DynForm

/-! #### The two forms -/

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- `committed + n`, at the committed word's range shifted by `n`. -/
def dynSumme (A : DynForm D) (n : Int) (hLK : gdarf D A.komm Λ) :
    Expr D Γ Λ (.int (0 + n) (D.count A.tab + n)) :=
  Expr.add (Expr.umTyp A.hk (Expr.glob A.komm hLK)) (Expr.lit n)

/-- **`grow A by n else B;`** -- `Block.narrow` of `committed + n` into
    `0 .. M`, and the store of what it narrowed to. It fits, and the
    committed word takes it; or it does not, and `B` runs -- `narrow`'s
    `else` does not fall through, the same promise the surface `else`
    carries. Past `M` there is no other branch, which is the form's whole
    content: the ceiling is a refusal, never a runtime surprise. -/
def dynGrowB (A : DynForm D) (n : Int)
    (hwK : V.gschreibt A.komm = true) (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l Γ Λ Λ' :=
  .narrow (dynSumme A n hLK) 0 (D.count A.tab) voll
    (.cons (.assignGlob A.komm (Expr.umTyp A.hk.symm (Expr.var .here)) hwK hLK) rest)

/-- The guard of a dynamic allocation: `used < committed`. This is the
    R-commit test, and it is the ONE thing a dynamic `alloc` does that the
    static one does not. -/
def dynUnterKomm (A : DynForm D) (hLG : gdarf D A.zaehl Λ) (hLK : gdarf D A.komm Λ) :
    Expr D Γ Λ .bool :=
  Expr.lt (Expr.umTyp A.hz (Expr.glob A.zaehl hLG)) (Expr.umTyp A.hk (Expr.glob A.komm hLK))

/-- **`let i = alloc A (v) else B;` on a DYNAMIC arena.** The committed test
    in front, the static form underneath -- `Block.arenaAlloc` is taken from
    `ArenaZucker.lean` unchanged, which is why every static theorem about it
    applies verbatim once the test has passed. Both branches name the same
    `else`: below the ceiling but past the committed prefix is a refusal for
    the same reason a full arena is. -/
def dynAlloc (A : DynForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l Γ Λ Λ' :=
  .check (dynUnterKomm A hLG hLK) voll
    (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest)

end Block

/-! #### What the two forms MEAN -/

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- Down to the committed word's declared type and back is nothing -- the
    one cast `dynGrowB` writes through, discharged once for every theorem
    below. -/
theorem komSt_hin_her (A : DynForm D) (x : Int) (h0 : 0 ≤ x) (h : x ≤ D.count A.tab) :
    (Wert.umTyp A.hk
      (Wert.umTyp (D := D) A.hk.symm (⟨x, h0, h⟩ : Wert D (Ty.int 0 (D.count A.tab))))).n = x :=
  congrArg (fun v : Wert D (Ty.int 0 (D.count A.tab)) => v.n)
    (Wert.umTyp_hin_her A.hk (⟨x, h0, h⟩ : Wert D (Ty.int 0 (D.count A.tab))))

/-- The world a successful `grow` leaves behind: the read it records, then
    the one store. Named, because three theorems speak about it. -/
def nachGrow (A : DynForm D) (n : Int) (Λ : List (Res D)) (σ : World D)
    (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab) : World D :=
  (σ.lese Λ [Sum.inr A.komm]).schreibGlob A.komm Λ
    (Wert.umTyp A.hk.symm ⟨A.komSt σ + n, h0, h⟩)

/-- **`grow` bumps the committed word by `n`, and moves nothing else.** The
    first conjunct is the run, the last three are the frame: the used
    counter stands where it stood, the slots are the slots, and the ceiling
    is the ceiling. -/
theorem dynGrow_commit (A : DynForm D) (n : Int)
    (hwK : V.gschreibt A.komm = true) (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab) :
    execBlock (V := V) O passes R (Block.dynGrowB A n hwK hLK voll rest) σ ρ
        = (execBlock O passes R rest (nachGrow A n Λ σ h0 h)
            (.cons ⟨A.komSt σ + n, h0, h⟩ ρ)).schrumpf ∧
      A.komSt (nachGrow A n Λ σ h0 h) = A.komSt σ + n ∧
      A.stand (nachGrow A n Λ σ h0 h) = A.stand σ ∧
      (nachGrow A n Λ σ h0 h).slots = σ.slots := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · have hb : (0 : Int) ≤ (Wert.umTyp A.hk (σ.globs A.komm)).n + n ∧
        (Wert.umTyp A.hk (σ.globs A.komm)).n + n ≤ D.count A.tab := ⟨h0, h⟩
    simp only [Block.dynGrowB, Block.dynSumme, execBlock, eval_umTyp, orte_umTyp, eval,
      Expr.orte, World.globs_lese, Zahl.add]
    rw [dif_pos hb]
    simp only [execStmt, nachGrow, eval_umTyp, Expr.orte, orte_umTyp, List.append_nil]
    rfl
  · rw [nachGrow, DynForm.komSt_schreibGlob]
    exact komSt_hin_her A _ h0 h
  · rw [nachGrow, DynForm.stand_schreibGlob_komm]
    rfl

/-- **Commit never shrinks, on the form** -- `dynGrow_monoton` where the
    numbers live in a world. A `grow by n` with `n` at least zero leaves the
    committed word at least where it was; the surface demands `n >= 1`
    (`R-grow-const`), and the model does not need that to say this. -/
theorem dynCommit_monoton (A : DynForm D) (n : Int) (Λ : List (Res D)) (σ : World D)
    (h0 : 0 ≤ A.komSt σ + n) (h : A.komSt σ + n ≤ D.count A.tab) (hn : 0 ≤ n) :
    A.komSt σ ≤ A.komSt (nachGrow A n Λ σ h0 h) := by
  rw [nachGrow, DynForm.komSt_schreibGlob, komSt_hin_her A _ h0 h]
  omega

end Bedeutung
end Form
end Gabbro.Grammatik.ArenaDyn
