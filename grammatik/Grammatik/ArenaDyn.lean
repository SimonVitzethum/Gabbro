/-
  File:      Grammatik/ArenaDyn.lean
  Subject:   Dynamic arenas: virtual reservation, committed prefix, and the
             past-ceiling stop over a run's commit sequence
             (PLAN-DYNAMISCH.md section 9, lane 241; reworked by fix lane F2
             after review G08 F4, 2026-09-21; the section-9 FORM -- `DynForm`,
             the four Block-form theorems and the simulation -- added by the
             server lane 2026-09-28, section `Form` at the end).

  A dynamic arena declares a static ceiling `M` (address reserved, never
  touched implicitly) and a committed prefix `c` (`hi <= c <= M`) grown
  explicitly by `grow`. Commit is monotone within a run; growth beyond `M`
  is a refusal, never a runtime surprise. Fault latency/cost arrives as a
  NAMED hardware assumption read as data (`faultKosten`), never justified
  here. The C plug-in point is `CSpeicher.lean` (read-only): the virtual
  region is the arena block's `Fin M` index set, the committed prefix the
  `Fin c` usable part; nothing here edits that file.
-/
import Grammatik.ReferenzB
import Grammatik.ArenaZucker

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
  · exact absurd h (by simp)

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
    simp [h]
  · rw [dif_neg h]
    simp [h]

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
    simp
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

theorem planted_ueber_M : dynGrow arena64volle 1 = none := rfl

/-- Unchecked commit: bumps without consulting `M` (the defect), as raw data. -/
structure DynRoh where
  M : Nat
  hi : Nat
  c : Nat

def dynGrowFalsch (A : DynArena) (n : Nat) : DynRoh := ⟨A.M, A.hi, A.c + n⟩

/-- The defect is visible: the unchecked bump reaches 65 past `M = 64`. -/
theorem planted_defekt_sichtbar : (dynGrowFalsch arena64volle 1).c = 65 := rfl

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
    exact ⟨A, rfl, by simp⟩
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
    simp at h
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

/-! ### The dynamic arena AS A FORM (PLAN-DYNAMISCH section 9, server lane 2026-09-28)

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
    (o : List (D.Tab ⊕ D.Glob)) : A.komSt (σ.lese Λ o) = A.komSt σ := rfl

/-- A slot store does not move the committed word. -/
@[simp] theorem komSt_schreibSlot (A : DynForm D) (σ : World D) (Λ : List (Res D))
    (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    A.komSt (σ.schreibSlot t Λ k f v) = A.komSt σ := rfl

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
    (σ.schreibGlob A.komm Λ v).slots = σ.slots := rfl

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
    (.cons (.assignGlob A.komm (Expr.umTyp A.hk.symm (Expr.var .hier)) hwK hLK) rest)

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
  .pruefung (dynUnterKomm A hLG hLK) voll
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

/-- **Below the committed prefix, `alloc` does not take its `else`** -- the
    model half of the R-commit rule. The body is `ArenaZucker`'s
    `arenaRumpf`, unchanged: past the test, a dynamic arena IS a static one.
    The index bound is the OLD used counter, as there. -/
theorem dynAlloc_unter_commit (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < A.komSt σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = (execBlock O passes R (Block.arenaRumpf A.toArenaForm v hwT hLT hwG hLG rest)
          (((σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm])).lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ,
            by have := A.komSt_le σ; omega⟩ ρ)).schrumpf := by
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · exact arenaAlloc_unter_schranke O passes R A.toArenaForm v hwT hLT hwG hLG voll rest _ ρ
      (by have := A.komSt_le σ
          show A.stand σ < D.count A.tab
          omega)
  · next hno =>
      refine absurd ?_ hno
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      exact h

/-- **At or above the committed prefix, `alloc` takes its `else`** -- even
    with room to the ceiling. That is the whole difference between a
    reservation and storage: the arena is not full and the allocation is
    refused all the same, because the slot is not committed yet. -/
theorem dynAlloc_ueber_commit (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.komSt σ ≤ A.stand σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]) ρ).zuAusgang := by
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · next hja =>
      exfalso
      revert hja
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      unfold DynForm.komSt ArenaForm.stand at h
      omega
  · rfl

/-- **THE SIMULATION** (the shape PLAN-DYNAMISCH section 9 fixes): a dynamic
    allocation whose index stays under its path's committed prefix runs the
    STATIC-max form -- the very same `Block.arenaAlloc` over the very same
    `ArenaForm`, on a world that differs from the dynamic one only in the
    trace (the two recorded reads of the guard). The second and third
    conjuncts are that difference, measured: the storage is the same
    storage. Every static-arena theorem therefore transfers to the right
    hand side verbatim, and growth is an observable no-op -- `dynGrow_commit`
    is the frame that says the only thing a `grow` can change about this
    equation is the guard it passes. -/
theorem dynAlloc_simuliert (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < A.komSt σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = execBlock O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest)
          (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]) ρ ∧
      (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]).globs = σ.globs ∧
      (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]).slots = σ.slots := by
  refine ⟨?_, rfl, rfl⟩
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · rfl
  · next hno =>
      refine absurd ?_ hno
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      exact h

end Bedeutung

/-! #### THE WITNESS -- two words over one table, and both branches run

  Not decorative, and the non-degeneracy is the point of the whole section:
  the table holds FOUR slots (the ceiling `M = 4`) and the committed word
  stands at TWO. So the fixture has a state that the static form cannot
  even name -- an arena with room to the ceiling whose allocation is
  refused, because the slot is reserved and not committed. Both branches of
  `dynAlloc` are exercised below, and the one `grow` moves the committed
  word from 2 to the ceiling. -/

namespace DynZeuge

/-- One table of four slots holding a byte, and TWO globals over `0 .. 4`:
    the used counter (`false`) and the committed prefix (`true`). The two
    words are the whole difference to `ArenaZucker`'s `ZD`, which has one. -/
def DD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Bool
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun _ => true
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

/-- `arena Halde capacity 2 .. 4 max 4 of u8` -- the ceiling is the table's
    `count`, the committed prefix is the second word. -/
def Halde : DynForm DD where
  tab := ()
  feld := ()
  zaehl := false
  hz := rfl
  hpos := by decide
  komm := true
  hk := rfl
  hzwei := by
    intro h
    exact Bool.noConfusion (show (true : Bool) = false from h)

/-- The ceiling is four: a committed prefix strictly under it is a state. -/
theorem Halde_vier : DD.count Halde.tab = 4 := rfl

/-- The contract of the witness body: it writes the table and both words. -/
def DV : Vertrag DD where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem zeuge_darf : darf DD () ([] : List (Res DD)) := by
  intro w hw; cases hw

theorem zeuge_gdarf (g : DD.Glob) : gdarf DD g ([] : List (Res DD)) := by
  intro w hw; cases hw

/-- A world whose used counter stands at `u` and whose committed word at
    `k`; every slot at zero. -/
def welt (u k : Int) (hu0 : 0 ≤ u) (hu4 : u ≤ 4) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) : World DD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => cond g ⟨k, hk0, hk4⟩ ⟨u, hu0, hu4⟩
  spur := []

theorem welt_stand (u k : Int) (hu0 : 0 ≤ u) (hu4 : u ≤ 4) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) :
    Halde.stand (welt u k hu0 hu4 hk0 hk4) = u := rfl

theorem welt_komSt (u k : Int) (hu0 : 0 ≤ u) (hu4 : u ≤ 4) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) :
    Halde.komSt (welt u k hu0 hu4 hk0 hk4) = k := rfl

/-- The world the witness runs in: nothing used, TWO of four slots
    committed. -/
def halb : World DD := welt 0 2 (by decide) (by decide) (by decide) (by decide)

/-- The same arena with its used counter AT the committed prefix -- and the
    committed prefix strictly under the ceiling. **This state is the reason
    the fixture is not degenerate:** there is room, and the allocation is
    refused all the same. -/
def gespannt : World DD := welt 2 2 (by decide) (by decide) (by decide) (by decide)

theorem halb_stand : Halde.stand halb = 0 := rfl

theorem halb_komSt : Halde.komSt halb = 2 := rfl

theorem zeuge_raum_ueber_dem_stand : Halde.stand halb < Halde.komSt halb := by decide

theorem zeuge_raum_unter_der_decke : Halde.komSt gespannt < DD.count Halde.tab := by decide

theorem zeuge_stand_an_der_verpflichtung : Halde.komSt gespannt ≤ Halde.stand gespannt := by
  decide

/-- The value an `alloc` stores in the witness. -/
def sieben : Expr DD [] [] (DD.typ Halde.tab Halde.feld) :=
  Expr.weiter (by decide) (by decide) (Expr.lit 7)

/-- **`grow Halde by 2`, run:** the committed word moves from 2 to the
    ceiling 4, the used counter does not move, and no slot does. A real
    commit (`n = 2 > 0`) that ends exactly at `M`. -/
theorem zeuge_grow (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.int 0 (DD.count Halde.tab)] [] []) :
    ∃ σ' : World DD,
      execBlock (V := DV) O passes R
          (Block.dynGrowB Halde 2 rfl (zeuge_gdarf Halde.komm) voll rest) halb .nil
        = (execBlock O passes R rest σ'
            (.cons ⟨Halde.komSt halb + 2, by rw [halb_komSt]; decide,
              by rw [halb_komSt]; decide⟩ .nil)).schrumpf ∧
      Halde.komSt σ' = 4 ∧ Halde.stand σ' = 0 ∧ σ'.slots = halb.slots := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    dynGrow_commit (V := DV) (l := false) O passes R Halde 2 rfl (zeuge_gdarf Halde.komm)
      voll rest halb .nil (by decide) (by decide)
  exact ⟨_, h1, by rw [h2]; decide, by rw [h3]; decide, h4⟩

/-- **Under the committed prefix the `else` is not taken**, and the index is
    the old used counter -- the body is `ArenaZucker`'s, unchanged. -/
theorem zeuge_alloc_unter (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.index (DD.count Halde.tab)] [] []) :
    execBlock (V := DV) O passes R
        (Block.dynAlloc Halde sieben rfl zeuge_darf rfl (zeuge_gdarf Halde.zaehl)
          (zeuge_gdarf Halde.komm) voll rest) halb .nil
      = (execBlock O passes R (Block.arenaRumpf Halde.toArenaForm sieben rfl zeuge_darf rfl
            (zeuge_gdarf Halde.zaehl) rest)
          ((halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]).lese []
            [Sum.inr Halde.zaehl])
          (.cons ⟨Halde.stand halb, Halde.stand_nonneg halb, by decide⟩ .nil)).schrumpf :=
  dynAlloc_unter_commit (V := DV) (l := false) O passes R Halde sieben rfl zeuge_darf rfl
    (zeuge_gdarf Halde.zaehl) (zeuge_gdarf Halde.komm) voll rest halb .nil (by decide)

/-- **And AT the committed prefix it IS taken, with the ceiling still two
    slots away.** This is the one line the static form cannot produce. -/
theorem zeuge_alloc_ueber (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.index (DD.count Halde.tab)] [] []) :
    execBlock (V := DV) O passes R
        (Block.dynAlloc Halde sieben rfl zeuge_darf rfl (zeuge_gdarf Halde.zaehl)
          (zeuge_gdarf Halde.komm) voll rest) gespannt .nil
      = (execEnd O passes R voll
          (gespannt.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]) .nil).zuAusgang :=
  dynAlloc_ueber_commit (V := DV) (l := false) O passes R Halde sieben rfl zeuge_darf rfl
    (zeuge_gdarf Halde.zaehl) (zeuge_gdarf Halde.komm) voll rest gespannt .nil (by decide)

/-- **The simulation, run:** under the committed prefix the dynamic form IS
    the static one, on a world that differs only in the trace. -/
theorem zeuge_simuliert (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.index (DD.count Halde.tab)] [] []) :
    execBlock (V := DV) O passes R
        (Block.dynAlloc Halde sieben rfl zeuge_darf rfl (zeuge_gdarf Halde.zaehl)
          (zeuge_gdarf Halde.komm) voll rest) halb .nil
      = execBlock O passes R
          (Block.arenaAlloc Halde.toArenaForm sieben rfl zeuge_darf rfl
            (zeuge_gdarf Halde.zaehl) voll rest)
          (halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]) .nil ∧
      (halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]).globs = halb.globs ∧
      (halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]).slots = halb.slots :=
  dynAlloc_simuliert (V := DV) (l := false) O passes R Halde sieben rfl zeuge_darf rfl
    (zeuge_gdarf Halde.zaehl) (zeuge_gdarf Halde.komm) voll rest halb .nil (by decide)

end DynZeuge

end Form

#print axioms dynGrowListe_gelingt
#print axioms dynGrowListe_scheitert
#print axioms dynGrowListe_gelingt_zeuge
#print axioms dynGrowListe_scheitert_zeuge
#print axioms dynGrowListe_zwilling
#print axioms dynGrow_monoton
#print axioms dynGrow_ueber_M
#print axioms dynGrow_isSome
#print axioms dynGrow1_gdw_alloc
#print axioms planted_ueber_M
#print axioms planted_defekt_sichtbar
#print axioms growKosten_pos
#print axioms DynForm.stand_schreibGlob_komm
#print axioms DynForm.komSt_schreibGlob
#print axioms dynGrow_commit
#print axioms dynCommit_monoton
#print axioms dynAlloc_unter_commit
#print axioms dynAlloc_ueber_commit
#print axioms dynAlloc_simuliert
#print axioms DynZeuge.zeuge_grow
#print axioms DynZeuge.zeuge_alloc_unter
#print axioms DynZeuge.zeuge_alloc_ueber
#print axioms DynZeuge.zeuge_simuliert
#print axioms DynZeuge.zeuge_raum_ueber_dem_stand
#print axioms DynZeuge.zeuge_raum_unter_der_decke
#print axioms DynZeuge.zeuge_stand_an_der_verpflichtung

end Gabbro.Grammatik.ArenaDyn

/-! CUTS -- what this file does NOT claim.

  * No checker rule is built here: R-max / R-commit / R-grow-else /
    R-grow-const / R-grow-form (PLAN-DYNAMISCH section 4) are lane 240/241
    Rust work; this file is the Lean model half (section 9) only.
  * No emitter or runtime is built: the descriptor (`base`, `committed`),
    `gabbro_arena_reserve` / `gabbro_arena_grow`, and the OS-token guardian
    are lane 242 work; the `_Static_assert` pins are not stated here.
  * No cost arm is built: `growKosten` reads the per-slot commit cost as
    DATA from the named hardware assumption (Spec premise (c) latency
    entry); the `K003` wiring and the `K002`-falls probe are lane 243 work.
  * **No refinement is claimed** (review G08 F4, fix lane F2). `DynArena` is
    a Nat record that carries `c <= M` as a field; a membership fact over it
    (the former `dynVerfein`, "committed slots are reserved slots") restates
    that field, and the former `region_verpflichtet` tied it to a run only
    through a premise its witness discharged without looking at the run
    (the lane-147 pattern). Both are REMOVED, not renamed. What stands in
    their place is a statement about the one runtime fact this record does
    model -- the past-ceiling stop -- over a whole commit sequence
    (`dynGrowListe_gelingt` / `_scheitert`, with non-degenerate witnesses):
    the model half of `N426`'s upper-bound rule. Nothing links `DynArena` to
    the Rust checker's per-path accounting or to the C runtime by proof; the
    link is by name (`N426`, `gabbro_arena_grow`'s ceiling test) only.
    Proved as the linkage anchor to the static model: `dynGrow_isSome`
    (success is exactly the bound) and `dynGrow1_gdw_alloc` (one-slot commit
    agrees with `Arena.alloc` on `Kap ⟨hi, M⟩` via `arenaModell`, from the
    `alloc_erfolg` / `alloc_fehlschlag` pair).
  * **Section `Form` closes the section-9 residue** (server lane,
    2026-09-28): `DynForm` over `ArenaForm D` (the table spans `M`, the
    committed prefix is a second `stand`-style word `komSt`), the four
    theorems in `Block` form (`dynGrow_commit` with the frame conjuncts,
    `dynCommit_monoton`, `dynAlloc_unter_commit`, `dynAlloc_ueber_commit`)
    and the simulation `dynAlloc_simuliert`, each with a witness on `DD`
    (two globals over one four-slot table, committed prefix at 2). The
    estimated 40-80 lines of narrow-on-committed plumbing were NOT needed:
    the guard is `Block.pruefung` on `used < committed` -- no binder, an
    `else` that does not fall through -- with `Block.arenaAlloc` taken from
    `ArenaZucker.lean` UNCHANGED underneath, so the static theorems apply
    past the guard instead of being restated.
  * **The residue of the simulation is the TRACE, and it is named.**
    `dynAlloc_simuliert` equates the dynamic form with the static-max form
    run on `σ.lese Λ [used, committed]`, and measures the difference:
    `globs` and `slots` are equal (proved), the trace carries two more
    recorded reads (the guard's). A run-level bisimulation that erases
    those reads over an arbitrary `rest` is NOT proved and is not claimed;
    what is claimed is one step, exactly.
  * **The simulation is about `alloc`, not about `grow` as a step.**
    "Growth is an observable no-op" is carried here by the frame conjuncts
    of `dynGrow_commit` (a `grow` moves the committed word and no slot and
    not the used counter) plus the guard -- not by a theorem that quantifies
    over programs containing a `grow`.
  * **One arena, one thread** (OFFEN O20, unchanged here). The committed
    prefix is a SECOND carrier, so two threads growing one arena race on it
    exactly as they would on the used counter. Nothing in this section
    relaxes O20's restriction -- no `reset` concurrent with a reader, no
    arena shared across threads without the strict option -- and no
    `Spec.lean` diff naming a weaker run model was made. The goal's own
    footprint rule refuses such a program in any case: an unguarded global
    two threads write is not thread-local and not lock-guarded.
  * **The EXPORTER does not produce these terms** (measured 2026-09-28):
    `lean_g.rs` refuses `grow` by name (`LG005`) and builds the STATIC
    `ArenaForm` over `hi`, not over the ceiling `M`. So the forms here are
    covered by `gabbro_ziel` -- they are ordinary `Block` terms -- but no
    dynamic-arena PROGRAM is certified, and a green build says nothing about
    one. Same status `ArenaZucker.lean` had before O14 closed; the form
    existing is the precondition for that work, not a substitute for it.
  * The `Spec.lean` header diff (the two (d) assumption texts) is made in
    that file and not here, as a COMMENT-only diff with its own review
    (`messung/SERVER-0E-SPEC-DIFF.md`): no field of `Laufzeit` is added, and
    the reason is written there -- a new premise would weaken the statement,
    and the reservation is already carried by `Laufzeit.lader`.
  * `planted_ueber_M` is the planted-defect check: `dynGrow` on the full
    `max 64` arena returns `none` (by `rfl`); the unchecked `dynGrowFalsch`
     reaches `65`, past the ceiling (`planted_defekt_sichtbar`).
-/
