/-
  File:      Grammatik/SchablonenT5Sem.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md), the
             SEMANTICS-TIED half.

  What this file is: soundness lemmas for the most-used templates of
  `crates/gabbro-check/src/schablonen.rs`, stated over the project's
  actual semantics -- the declaration `D`, the sequential semantics
  (`eval`, `execStmt` in `Semantik.lean`), the memory (`World`,
  `Ereignis`, `offen`), and the emitter layout (`EmitLay`,
  `EmitLay.trec_count` in `CSpeicher.lean`). Each template's premises
  are the shape the generator emits for a program; each conclusion is
  the obligation the template discharges for that program. Each
  `NAME_zeuge` instantiates the premises on a REAL program (`refD` /
  `refP`) by `decide` / computation, with the conclusion about that
  program's run. Modelled on the `Bewiesen` Isabelle theories in
  `beweise/*.thy`.

  Covered (corpus order): `table.indexschranke`, `table.absenkung`,
  `gruppe.sperrabdruck`, `option.sonderwert`, and the model-facing
  half of `device.konstruktor`. Precisely skipped (no counterpart in
  the Lean model): the layout arithmetic of `device.konstruktor`
  (`World` has no address cells; registers live behind the oracle)
  and `entry.abdruck` (no entry-path syntax, no register file in
  `World`, no preserves/clobbers sets in `Deklaration`).
-/

import Grammatik.ReferenzB
import Grammatik.CSpeicher

namespace Gabbro.Grammatik

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- A concrete start world over `refD`: both `konto` slots read `0`,
    empty trace. -/
def semW0 : World refD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-! ## 1. `table.indexschranke` -- every generated index is in type.

The generator types every slot index as `Expr Γ Λ (.index
(D.count t))` (`M103`); the semantics evaluates it to a value of
exactly that type. That is the whole carrying half
(`schreibstellen_im_typ`, `kette_bleibt_im_typ`): there is no other
way to name a slot -- `assignSlot`, `slot`, `durch`, `traverse`,
`forallSlots` all take their index in this type. Modelled on
`beweise/Table_Indexschranke.thy` (M-2). The occupancy half
(`belegt_liegt_im_indextyp`) has no counterpart: `World.slots` is
total, slots are never unoccupied. -/

/-- Soundness of `table.indexschranke`, over the real expression
    semantics: an index expression of the generated type evaluates
    inside `0 ..< n`. No premises besides the expression itself. -/
theorem indexschranke_eval (n : Int) (e : Expr D Γ Λ (.index n))
    (σ₀ σ : World D) (ρ : Env D Γ) :
    0 ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ n - 1 :=
  ⟨(eval σ₀ e σ ρ).lo_le, (eval σ₀ e σ ρ).le_hi⟩

/-- Witness for `indexschranke_eval`: `refP`'s real index expression
    `refIdxEin` (the index of the write site `refWriteSt`, fired by
    the run at `refSchrittBF`) evaluates to `0`, inside
    `0 ..< count`; and the run that fires it reaches `MB` with slot
    `0` moved (`refB_erreicht`, `refB_schreibt`). Premise (the
    expression) by computation; conclusion about that program's run. -/
theorem indexschranke_zeuge :
    (eval semW0 refIdxEin semW0 refRho7).n = 0 ∧
    0 ≤ (eval semW0 refIdxEin semW0 refRho7).n ∧
    (eval semW0 refIdxEin semW0 refRho7).n ≤ refD.count () - 1 ∧
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
    MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h0 : (eval semW0 refIdxEin semW0 refRho7).n = 0 := rfl
  have hC : refD.count () = 2 := rfl
  refine ⟨h0, by rw [h0]; exact Int.le_refl _, by rw [h0, hC]; decide,
    refB_erreicht, refB_schreibt⟩

/-! ## 2. `table.absenkung` -- every in-range index names a laid-out cell.

The emitter lays table `t` out as `(trec t).count` cells
(`EmitLay.trec_count : ((trec t).count : Int) = D.count t` -- the `m
= N` agreement the certificate carries for a `C001`-checked layout).
With the index bound (`indexschranke_eval`, §1) every index of a
generated access names a cell: `kein_zugriff_laeuft_aus_dem_feld`.
Modelled on `beweise/Table_Absenkung.thy`, including both failure
directions (`zu_kurz_laesst_einen_index_ohne_speicher`,
`zu_lang_laesst_speicher_ohne_index`). -/

/-- Soundness of `table.absenkung`: layout/count agreement plus an
    in-range index give a laid-out cell. `trec_count` and both index
    bounds are consumed. -/
theorem absenkung_index_im_feld (EL : EmitLay D) (t : D.Tab)
    (i : Int) (h0 : 0 ≤ i) (hN : i < D.count t) :
    i.toNat < (EL.trec t).count := by
  have hc := EL.trec_count t
  omega

/-- Too short a layout leaves an index homeless. -/
theorem absenkung_zu_kurz (EL : EmitLay D) (t : D.Tab)
    (hm : ((EL.trec t).count : Int) < D.count t) :
    ∃ i : Int, 0 ≤ i ∧ i < D.count t ∧ ¬ i.toNat < (EL.trec t).count := by
  refine ⟨((EL.trec t).count : Int), Int.natCast_nonneg _, hm, ?_⟩
  intro hcon
  have e : (((EL.trec t).count : Int)).toNat = (EL.trec t).count :=
    Int.toNat_natCast _
  omega

/-- Too long a layout leaves a cell indexless (for nonnegative counts). -/
theorem absenkung_zu_lang (EL : EmitLay D) (t : D.Tab)
    (hnn : 0 ≤ D.count t) (hm : D.count t < ((EL.trec t).count : Int)) :
    ∃ j : Nat, j < (EL.trec t).count ∧
      ¬ (0 ≤ (j : Int) ∧ (j : Int) < D.count t) := by
  refine ⟨(D.count t).toNat, ?_, ?_⟩
  · have e : (((D.count t).toNat : Nat) : Int) = D.count t :=
      Int.toNat_of_nonneg hnn
    omega
  · intro hcon
    have e : (((D.count t).toNat : Nat) : Int) = D.count t :=
      Int.toNat_of_nonneg hnn
    omega

/-- Witness for `absenkung_index_im_feld`: `refP`'s index `refIdxEin`
    (fired by the run at `refSchrittBF`) names a cell of the emitted
    `konto` layout (`refEL.trec_count`, `m = N = 2` by `rfl`); the run
    reaches `MB` with slot `0` moved. -/
theorem absenkung_zeuge :
    (eval semW0 refIdxEin semW0 refRho7).n.toNat < (refEL.trec ()).count ∧
    (((refEL.trec ()).count : Int) = refD.count ()) ∧
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
    MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hb := indexschranke_eval (refD.count ()) refIdxEin semW0 semW0 refRho7
  have hC : refD.count () = 2 := rfl
  have hN : (eval semW0 refIdxEin semW0 refRho7).n < refD.count () := by
    have := hb.2
    omega
  have hidx := absenkung_index_im_feld refEL () _ hb.1 hN
  refine ⟨hidx, refEL.trec_count (), refB_erreicht, refB_schreibt⟩

/-! ## 3. `gruppe.sperrabdruck` -- rank order is acyclic, the footprint
    spans the move.

A wait edge `M -> L` over the model's own trace type (`Ereignis`)
means: `L` is taken while `M` is held. The `locks` statement carries
the rank hypothesis `hr` (`H006`); a trace in which every take
happens above everything held (`wohlgeordnet` -- establishing it per
program is the `U003`/`U005` checker duty) has all its wait edges in
`less_than`, hence no cycle (`rangordnung_azyklisch`, `Gruppe_Erhaltung`
part (a)). Executing `locks` takes `L`, holds it across the whole
body, and gives it back (`sperrabdruck_form` -- the semantic clause).
Parts (b)/(c) of the Isabelle locale (invariant at begin/end, no
intermediate exit) have no counterpart in `execStmt` -- see the skip
note in the header/CUTS. -/

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D}

/-- Wait edges of a trace: `M -> L` whenever `L` is taken while `M`
    is held. -/
def waitEdges : List (Ereignis D) → List (D.Lock × D.Lock)
  | [] => []
  | .nimmt L held :: rest => (held.map fun M => (M, L)) ++ waitEdges rest
  | _ :: rest => waitEdges rest

/-- A rank-ordered trace: every take happens strictly above everything
    held at that moment. -/
def wohlgeordnet (spur : List (Ereignis D)) : Prop :=
  ∀ L held, Ereignis.nimmt L held ∈ spur →
    ∀ M ∈ held, D.rang M < D.rang L

/-- A rank chain over an edge set. -/
def ketteR (e : List (D.Lock × D.Lock)) : List D.Lock → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (a, b) ∈ e ∧ ketteR e (b :: rest)

/-- Chains strictly rise in rank. -/
theorem kette_steigt (e : List (D.Lock × D.Lock))
    (hE : ∀ p ∈ e, D.rang p.1 < D.rang p.2) (x : D.Lock) :
    ∀ (xs : List D.Lock), ketteR e (x :: xs) →
      ∀ y ∈ xs, D.rang x < D.rang y := by
  intro xs
  induction xs generalizing x with
  | nil => intro _ y hy; simp at hy
  | cons a rest ih =>
    intro hc y hy
    have hmem : (x, a) ∈ e ∧ ketteR e (a :: rest) := hc
    have hxa : D.rang x < D.rang a := hE _ hmem.1
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy'
    · exact hxa
    · have hay := ih a hmem.2 y hy'
      omega

/-- No lock waits on itself along a chain: the deadlock-freedom half.
    The single premise `hc` is satisfiable (non-closed chains exist);
    closing it (`x ∈ xs`) is what falls. -/
theorem kein_wartezyklus (e : List (D.Lock × D.Lock))
    (hE : ∀ p ∈ e, D.rang p.1 < D.rang p.2)
    (x : D.Lock) (xs : List D.Lock) (hc : ketteR e (x :: xs)) :
    x ∉ xs := by
  intro hmem
  have hlt := kette_steigt e hE x xs hc x hmem
  omega

/-- The footprint shape, over the real statement semantics: `locks`
    takes `L`, runs the whole body under it, and gives it back. -/
theorem sperrabdruck_form (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (.locks L hr body) σ ρ =
      (execBlock O passes R body (σ.nimmt L) ρ).mapWelt (·.gibt L) :=
  rfl

/-! ### The footprint on a real fragment.

Taking the reference lock over empty holdings satisfies `H006`
vacuously; running `refP`'s write under it shows the whole footprint
-- take, write under the held lock, give back -- by computation. -/

/-- `H006` over empty holdings, by computation. -/
theorem fragHr : ∀ M : refD.Lock,
    Res.held M ∈ ([] : List (Res refD)) → refD.rang M < refD.rang () := by
  intro M hM
  simp at hM

/-- A real `locks` fragment over `refD`: take `()` holding nothing,
    run `refP`'s write site, give back. -/
def fragLocks : Stmt refD (vertragVon refD refEin) false [.int 0 10] [] [] :=
  .locks () fragHr (.cons refWriteStAt .nil)

/-- The trace an outcome carries. -/
def ausgangSpur {l : Bool} {Γ : Ctx} : Ausgang V l Γ → List (Ereignis D)
  | .ok σ _ => σ.spur
  | .zurueck σ _ => σ.spur
  | .grund σ _ => σ.spur
  | .leave _ σ _ => σ.spur
  | .next _ σ _ => σ.spur
  | .logik _ => []
  | .hardware _ => []

/-- The world an `ok` outcome carries. -/
def ausgangWelt {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Option (World D)
  | .ok σ _ => some σ
  | _ => none

/-- The fragment's run, computed: take (holding nothing), the write
    under the held lock, give back. -/
theorem fragLocks_spur :
    ausgangSpur (execStmt refO 0 keinRuf fragLocks semW0 refRho7) =
      [.gibt (), .zugriff () true [Res.held (D := refD) ()] [()],
        .nimmt () []] := by
  rfl

/-- The lock is closed again after the fragment. -/
theorem fragLocks_geschlossen :
    offen (ausgangSpur (execStmt refO 0 keinRuf fragLocks semW0 refRho7)) = [] := by
  rw [fragLocks_spur]
  rfl

/-- The write happened under the held lock. -/
theorem fragLocks_schreibt_bewacht :
    .zugriff () true [Res.held (D := refD) ()] [()] ∈
      ausgangSpur (execStmt refO 0 keinRuf fragLocks semW0 refRho7) := by
  rw [fragLocks_spur]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- The fragment's write moved memory: slot `0` reads `100`. -/
theorem fragLocks_schreibt :
    (ausgangWelt (execStmt refO 0 keinRuf fragLocks semW0 refRho7)).map
      (·.slots () 0 ()) = some refV100 := by
  rfl

/-- The fragment's trace is rank-ordered (the take holds nothing). -/
theorem fragLocks_wohlgeordnet :
    wohlgeordnet (ausgangSpur
      (execStmt refO 0 keinRuf fragLocks semW0 refRho7)) := by
  rw [fragLocks_spur]
  intro L held hM M hM'
  simp only [List.mem_cons, List.not_mem_nil] at hM
  rcases hM with h | h | h | hnil
  · cases h
  · cases h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hM' List.not_mem_nil
  · exact hnil.elim

/-- Witness for the `sperrabdruck` package: the fragment's trace has
    NO wait edge (nothing is held at the take), is rank-ordered,
    closes the lock, writes under it, moves memory -- and admits no
    wait cycle. The edge set and order facts hold by computation;
    every conclusion is about this program's run. -/
theorem sperrabdruck_zeuge :
    waitEdges (ausgangSpur
      (execStmt refO 0 keinRuf fragLocks semW0 refRho7)) = [] ∧
    wohlgeordnet (ausgangSpur
      (execStmt refO 0 keinRuf fragLocks semW0 refRho7)) ∧
    offen (ausgangSpur
      (execStmt refO 0 keinRuf fragLocks semW0 refRho7)) = [] ∧
    (ausgangWelt (execStmt refO 0 keinRuf fragLocks semW0 refRho7)).map
      (·.slots () 0 ()) = some refV100 ∧
    (∀ (x : refD.Lock) (xs : List refD.Lock),
      ketteR (waitEdges (ausgangSpur
        (execStmt refO 0 keinRuf fragLocks semW0 refRho7))) (x :: xs) →
        x ∉ xs) := by
  have hedges : waitEdges (ausgangSpur
      (execStmt refO 0 keinRuf fragLocks semW0 refRho7)) = [] := by
    rw [fragLocks_spur]
    rfl
  have hE : ∀ p ∈ waitEdges (ausgangSpur
      (execStmt refO 0 keinRuf fragLocks semW0 refRho7)),
      refD.rang p.1 < refD.rang p.2 := by
    intro p hp
    rw [hedges] at hp
    simp at hp
  refine ⟨hedges, fragLocks_wohlgeordnet, fragLocks_geschlossen,
    fragLocks_schreibt, ?_⟩
  intro x xs hc
  exact kein_wartezyklus _ hE x xs hc

/-! ## 4. `option.sonderwert` -- `Some` is never `None`, payloads are
    in range.

`option index into T` is `Expr.some (e : Expr Γ Λ (.index n))` and
`None` is `Expr.none n`; `eval` sends them to `Option.some` /
`Option.none` of the value world. So a `Some`-constructed value is
always distinguishable from `None` (the `kodiere_injektiv`
`None`/`Some` cases), and its payload is an in-range index by §1.
Modelled on `beweise/Option_Sonderwert.thy`, first half. The word
half (`N < 2^w`, collapse at `N = 2^w`) has NO counterpart: the model
has no machine-word lowering (`roh` maps `none` to `-1` with no
modulus) -- see the skip note. -/

/-- Soundness of `option.sonderwert`, disjointness: `Some` never
    evaluates to `None`. The expression is consumed by the `eval`
    computation. -/
theorem sonderwert_disjoint (e : Expr D Γ Λ (.index n))
    (σ₀ σ : World D) (ρ : Env D Γ) :
    eval σ₀ (.some e) σ ρ ≠
      eval σ₀ ((.none n) : Expr D Γ Λ (.opt n)) σ ρ := by
  have hsome : eval σ₀ (.some e) σ ρ =
      Option.some (eval σ₀ e σ ρ) := rfl
  have hnone : eval σ₀ ((.none n) : Expr D Γ Λ (.opt n)) σ ρ =
      Option.none := rfl
  rw [hsome, hnone]
  intro h
  cases h

/-- Soundness of `option.sonderwert`, payload bound: the payload of a
    `Some` is an in-range index, via §1. `h` is consumed by the
    injection, `e` by the bound. -/
theorem sonderwert_schranke (e : Expr D Γ Λ (.index n))
    (σ₀ σ : World D) (ρ : Env D Γ)
    (k : Zahl 0 (n - 1))
    (h : eval σ₀ (.some e) σ ρ = Option.some k) :
    0 ≤ k.n ∧ k.n ≤ n - 1 := by
  have he : eval σ₀ e σ ρ = k := Option.some_inj.mp h
  have hb := indexschranke_eval n e σ₀ σ ρ
  rw [he] at hb
  exact hb

/-- Witness for the `option.sonderwert` pair: `refP`'s index
    `refIdxEin` (fired by the run at `refSchrittBF`), wrapped in
    `some`, is apart from `none` with an in-range payload; the run
    reaches `MB` with slot `0` moved. -/
theorem sonderwert_zeuge :
    eval semW0 (.some refIdxEin) semW0 refRho7 ≠
      eval semW0 ((.none (refD.count ())) :
        Expr refD [.int 0 10] [Res.held (D := refD) ()]
          (.opt (refD.count ()))) semW0 refRho7 ∧
    (∀ k : Zahl 0 (refD.count () - 1),
      eval semW0 (.some refIdxEin) semW0 refRho7 = Option.some k →
      0 ≤ k.n ∧ k.n ≤ refD.count () - 1) ∧
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
    MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  refine ⟨sonderwert_disjoint refIdxEin semW0 semW0 refRho7,
    fun k h => sonderwert_schranke refIdxEin semW0 semW0 refRho7 k h,
    refB_erreicht, refB_schreibt⟩

/-! ## CUTS:
  - Skeleton only: `semW0` is defined; the five tied templates are open.
-/

#print axioms Gabbro.Grammatik.semW0

end Gabbro.Grammatik
