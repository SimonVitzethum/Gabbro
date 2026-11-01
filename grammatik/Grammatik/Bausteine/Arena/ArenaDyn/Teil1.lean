module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Arena.ArenaZucker

@[expose] public section



namespace Gabbro.Grammatik.ArenaDyn

/-- A dynamic arena: ceiling `M`, commit floor `hi`, committed prefix `c`. -/
structure DynArena where
  M : Nat
  hi : Nat
  c : Nat
  hfloor : hi ≤ c
  hceil : c ≤ M
  hpos : 0 < M

/-- Explicit commit: `grow by n` bumps the prefix, capped refusal beyond `M`.
    Below `M` the runtime may still fail (out of memory is real); that `else`
    is the program's, not modelled here. Beyond `M` there is no branch. -/
def dynGrow (A : DynArena) (n : Nat) : Option DynArena :=
  if h : A.c + n ≤ A.M then
    some ⟨A.M, A.hi, A.c + n, Nat.le_trans A.hfloor (Nat.le_add_right _ _), h, A.hpos⟩
  else none

/-- Commit never shrinks: a successful `grow` keeps the old prefix. -/
theorem dynGrow_monoton (A : DynArena) (n : Nat) (B : DynArena)
    (h : dynGrow A n = some B) : A.c ≤ B.c := by
  unfold dynGrow at h
  split at h
  · cases h
    exact Nat.le_add_right _ _
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- The committed prefix is usable storage: every committed slot is reserved. -/
theorem dynCommit_innerhalb (A : DynArena) (i : Nat) (h : i < A.c) : i < A.M := by
  have := A.hceil
  omega

/-- Over-ceiling commit is a refusal: `grow` past `M` returns `none`. -/
theorem dynGrow_ueber_M (A : DynArena) (n : Nat) (h : A.M < A.c + n) :
    dynGrow A n = none := by
  unfold dynGrow
  split
  · omega
  · rfl

/-- Success is exactly the bound: `grow` answers iff the bump stays in `M`. -/
theorem dynGrow_isSome (A : DynArena) (n : Nat) :
    (dynGrow A n ≠ none) ↔ A.c + n ≤ A.M := by
  unfold dynGrow
  by_cases h : A.c + n ≤ A.M
  · rw [dif_pos h]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, h]
  · rw [dif_neg h]
    simp only [ne_eq, not_true_eq_false, h]

/-- The model arena: `used` is the committed prefix, the bound is the
    ceiling. This is the anchor lane 244's simulation builds on: one
    `grow by 1` is one `Arena.alloc` on `Kap ⟨hi, M⟩`. -/
def arenaModell (A : DynArena) : Arena.Arena ⟨A.hi, A.M⟩ 0 :=
  ⟨A.c, A.hceil⟩

/-- One-slot commit succeeds exactly when the monotone model allocates:
    `dynGrow A 1` and `Arena.alloc` on `Kap ⟨hi, M⟩` agree. Proved from
    `dynGrow_isSome` and the `alloc_erfolg` / `alloc_fehlschlag` pair --
    the `ArenaZucker` transfer target in miniature. -/
theorem dynGrow1_gdw_alloc (A : DynArena) :
    (dynGrow A 1 ≠ none) ↔ Arena.alloc (arenaModell A) ≠ none := by
  rw [dynGrow_isSome]
  constructor
  · intro h
    have hlt : (arenaModell A).used < (⟨A.hi, A.M⟩ : Arena.Kap).hi := by
      show A.c < A.M
      omega
    have he := Arena.alloc_erfolg (arenaModell A) hlt
    rw [he]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · intro h
    by_cases hlt : A.c < A.M
    · omega
    · have hnn : ¬ (arenaModell A).used < (⟨A.hi, A.M⟩ : Arena.Kap).hi := hlt
      exact absurd (Arena.alloc_fehlschlag (arenaModell A) hnn) h

/-- The planted-defect probe: a full `max 64` arena asked to grow fails red.
    An unchecked variant (no `M` guard) would return `some` here; the guard
    is what makes this `none`. Evaluated by `rfl`: the failure line is this
    theorem's statement. -/
def arena64volle : DynArena := ⟨64, 8, 64, by decide, by decide, by decide⟩

theorem planted_ueber_M : dynGrow arena64volle 1 = none := by rfl

/-- Unchecked commit: bumps without consulting `M` (the defect), as raw data. -/
structure DynRoh where
  M : Nat
  hi : Nat
  c : Nat

def dynGrowFalsch (A : DynArena) (n : Nat) : DynRoh := ⟨A.M, A.hi, A.c + n⟩

/-- The defect is visible: the unchecked bump reaches 65 past `M = 64`. -/
theorem planted_defekt_sichtbar : (dynGrowFalsch arena64volle 1).c = 65 := by rfl

/-- Grow cost: `1 + n * faultKosten`. The per-slot commit cost is READ from
    the named hardware assumption (Spec premise (c) latency entry), never
    justified here: it is a function argument, not a proved bound. -/
def growKosten (n faultKosten : Nat) : Nat := 1 + n * faultKosten

theorem growKosten_pos (n faultKosten : Nat) : 0 < growKosten n faultKosten := by
  unfold growKosten
  omega

/-! ### The commit sequence of a run (fix lane F2, review G08 F1/F4)

  The runtime never gives a committed page back (`reset` leaves `committed`
  alone), so over one load the `grow`s of the whole run form ONE sequence of
  amounts, folded through `dynGrow`; a `none` anywhere in the fold is the
  runtime's past-ceiling stop (`abort` in `laufzeit/arena_dyn.c`). The two
  theorems below are the model half of the checker rule `N426` since fix
  lane F2: the stop is avoided on EVERY run exactly when the upper bound of
  the total commit stays within `M - c` -- and a per-path LOWER bound (the
  reading before the fix) is not enough, as the witness shows with two
  commits that each fit alone. -/

/-- Fold a run's commit sequence through `dynGrow`: `none` is the stop. -/
def dynGrowListe (A : DynArena) : List Nat → Option DynArena
  | [] => some A
  | n :: ns =>
    match dynGrow A n with
    | none => none
    | some B => dynGrowListe B ns

/-- One commit inside the ceiling succeeds and moves the prefix by `n`. -/
theorem dynGrow_some (A : DynArena) (n : Nat) (h : A.c + n ≤ A.M) :
    ∃ B, dynGrow A n = some B ∧ B.c = A.c + n ∧ B.M = A.M := by
  refine ⟨⟨A.M, A.hi, A.c + n, Nat.le_trans A.hfloor (Nat.le_add_right _ _), h, A.hpos⟩,
    ?_, rfl, rfl⟩
  unfold dynGrow
  rw [dif_pos h]

/-- **The upper bound suffices:** a commit sequence whose total stays within
    the room above the prefix never reaches the stop, and ends at the prefix
    plus the total. -/
theorem dynGrowListe_gelingt :
    ∀ (ns : List Nat) (A : DynArena), A.c + ns.sum ≤ A.M →
      ∃ B, dynGrowListe A ns = some B ∧ B.c = A.c + ns.sum := by
  intro ns
  induction ns with
  | nil =>
    intro A _
    exact ⟨A, rfl, by simp only [List.sum_nil, Nat.add_zero]⟩
  | cons n ns ih =>
    intro A h
    rw [List.sum_cons] at h
    obtain ⟨B, hB, hc, hM⟩ := dynGrow_some A n (by omega)
    obtain ⟨C, hC, hcC⟩ := ih B (by omega)
    refine ⟨C, ?_, ?_⟩
    · show (match dynGrow A n with
            | none => none
            | some B => dynGrowListe B ns) = some C
      rw [hB]
      exact hC
    · rw [List.sum_cons]
      omega

/-- **And it is necessary:** a commit sequence whose total passes the room
    above the prefix reaches the stop, whatever its order. -/
theorem dynGrowListe_scheitert :
    ∀ (ns : List Nat) (A : DynArena), A.M < A.c + ns.sum →
      dynGrowListe A ns = none := by
  intro ns
  induction ns with
  | nil =>
    intro A h
    have := A.hceil
    simp only [List.sum_nil, Nat.add_zero] at h
    omega
  | cons n ns ih =>
    intro A h
    rw [List.sum_cons] at h
    show (match dynGrow A n with
          | none => none
          | some B => dynGrowListe B ns) = none
    by_cases hn : A.c + n ≤ A.M
    · obtain ⟨B, hB, hc, hM⟩ := dynGrow_some A n hn
      rw [hB]
      exact ih B (by omega)
    · rw [dynGrow_ueber_M A n (by omega)]

/-- The floor-`8` arena under `max 16`: the shape of `beispiele/gift/1133`
    and `/1135`. -/
def Az16 : DynArena := ⟨16, 8, 8, by decide, by decide, by decide⟩

/-- The same floor under `max 24`: the positive twins in `paesse.rs`. -/
def Az24 : DynArena := ⟨24, 8, 8, by decide, by decide, by decide⟩

/-- Witness for `dynGrowListe_gelingt`, non-degenerate: a real two-commit
    sequence (`8, 8`, total `16 > 0`) under `max 24` reaches `24`. -/
theorem dynGrowListe_gelingt_zeuge :
    ∃ (A : DynArena) (ns : List Nat) (B : DynArena),
      0 < ns.sum ∧ A.c + ns.sum ≤ A.M ∧
      dynGrowListe A ns = some B ∧ B.c = A.c + ns.sum :=
  let ⟨B, hB, hc⟩ := dynGrowListe_gelingt [8, 8] Az24 (by decide)
  ⟨Az24, [8, 8], B, by decide, by decide, hB, hc⟩

/-- Witness for `dynGrowListe_scheitert`, and the reason the lower-bound
    reading was wrong: under `max 16` EACH of the two commits fits the room
    alone (`8 + 8 <= 16`, what a per-path check of one `grow` saw), yet the
    run reaches the stop. -/
theorem dynGrowListe_scheitert_zeuge :
    ∃ (A : DynArena) (ns : List Nat),
      (∀ n, n ∈ ns → A.c + n ≤ A.M) ∧ A.M < A.c + ns.sum ∧
      dynGrowListe A ns = none :=
  ⟨Az16, [8, 8], by decide, by decide, dynGrowListe_scheitert [8, 8] Az16 (by decide)⟩

/-- Both directions evaluated on the fixtures (`rfl`, no lemma between). -/
theorem dynGrowListe_zwilling :
    (dynGrowListe Az24 [8, 8]).isSome = true ∧ dynGrowListe Az16 [8, 8] = none :=
  ⟨rfl, rfl⟩

/-! ### The dynamic arena AS A FORM (PLAN-DYNAMIC section 9, server lane 2026-09-28)

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
