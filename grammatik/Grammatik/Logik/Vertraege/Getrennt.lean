/-
  File:      Grammatik/Logik/Vertraege/Getrennt.lean
  Subject:   **SEPARATION AT A CALL BOUNDARY** -- `own`/separation, slice 2 (Lean side of
             `dokumente/A1-OWN-PAPER.md`; slice 1 is the checker rule `R014`,
             `m3.rs::getrennte_wurzeln`).

  WHAT THE MODEL SAYS ABOUT A POINTER PARAMETER. `Ty.ptr n rw` (`Typen.lean` §1) names
  its carrier STATICALLY: the table `D.tabNr n`. A pointer value is `Unit` -- the
  capability to address that whole table. So in machine G the "argument-to-carrier
  substitution" of a call is not chosen by the caller: it is the map
  `i ↦ traegerVon D (params f)[i]`, fixed by the callee's SIGNATURE, the same at every
  call. A callee's declared frame (`effects { writes p }` over a parameter `p`) reaches
  the model through that map: the exporter writes `writes p` as "writes the table of
  `p`'s type" (`lean_g.rs`, the writes-clause arm of `param_ty`). `own` travels as
  read-write (`param_ty`: "ownership carries both rights"), so "writable or `own`" is
  `rw = true` here.

  WHAT IS PROVED (all generic: every declaration, every function, every world):

    * `ParamGetrennt D f` -- the parameter-to-carrier map is injective on the pairs where one
      side is writable (the paper's S-1, read at the model's granularity). Decided by the
      Bool `paramGetrenntB` (`paramGetrenntB_wahr`).
    * `getrennt_paarweise` / `getrennt_schreiben_trennt` -- under `ParamGetrennt`, two pointer
      parameters of which one is writable name DISJOINT carriers, and a slot write through
      the one leaves every slot of the other unchanged.
    * `getrennt_lesesicht_bleibt` -- under `ParamGetrennt` and a frame declared over the
      parameters (`RahmenUeberParams`), every call handler that keeps the frame
      (`TreuR`) leaves the carrier of every READ-ONLY pointer parameter unchanged: the
      per-parameter reading of the frame ("`w` is only read") is a theorem.
    * `getrennt_ruf_rahmen` -- the same at the model's own call `rufAt`, at every depth
      and every world (through `rufAt_treu`, `RahmenTreu.lean`, no lock premise).
    * `leihe_wurzel`, `leihe_nicht_getrennt` -- the borrow rule: the answer of a re-view
      at one pointer type has the root of its argument, and a callee taking two such
      (one writable) is not `ParamGetrennt`.

  THE CONVERSE (`GetrenntZeuge.lean`): a concrete declaration and program where
  `ParamGetrennt` fails, the frame is declared over the parameters, and one real `rufAt` run
  changes the carrier of the read-only parameter. Without `ParamGetrennt` the per-parameter
  frame is only a promise.

  WHAT THE MODEL CANNOT SAY (the obstructions, see the report and A1-OWN-PAPER.md §6):

    1. ROOTS ARE FINER THAN CARRIERS. `R014` separates ROOTS (each pointer parameter is
       its own root, S-2); the model separates TABLES. Two parameters of one table type
       with two different roots are one carrier here (`Ty.ptr`: "two names for ONE
       world"), so an S-1-clean callee `fn g(k : ptr rw T, q : ptr r T)` is NOT
       `ParamGetrennt` -- the counter-model is exactly that shape. The model has no object
       below a table that a pointer could name, so the checker's S-2 (an inherited
       precondition "the roots differ") has no model statement to discharge.
    2. RE-VIEWS ACROSS TYPES DO NOT REACH THE MODEL. The `R014` surface is a pointer to a
       RECORD and a foreign re-view `fn (ptr A) -> ptr B`; the exporter refuses both
       (record target: `LG005` "names unknown table"; a non-`impl` function: `LG001`;
       measured: `beispiele/1163` is `UNCERTIFIED LG001`). In the model a function
       answering `ptr m` names table `m` by its TYPE, whatever its argument: the borrow
       rule `root(answer) = root(argument)` is the model's reading only when the two types
       name one table (`leihe_wurzel`). Two different tables are disjoint by
       construction, which is sound only because no cross-type view is exported.
-/
import Grammatik.Logik.Vertraege.RahmenTreu

namespace Gabbro.Grammatik

/-! ## 1. The carrier a parameter type names, and whether it is writable -/

/-- The carrier a parameter type names: the table of a pointer type, nothing otherwise.
    This is the model's ROOT of a pointer: a pointer value is `Unit`, so the only thing
    that tells two pointers apart is the table their type names. -/
def traegerVon (D : Deklaration) : Ty → Option D.Tab
  | .ptr n _ => D.tabNr n
  | _ => none

/-- Separation matters for a parameter: a writable pointer (`rw`, `w`, and `own`, which
    the exporter carries as read-write). -/
def zaehltFuerTrennung : Ty → Bool
  | .ptr _ rw => rw
  | _ => false

theorem zaehlt_ptr {τ : Ty} (h : zaehltFuerTrennung τ = true) : ∃ n, τ = .ptr n true := by
  cases τ <;> simp only [zaehltFuerTrennung, Bool.false_eq_true] at h
  next n rw => subst h; exact ⟨n, rfl⟩

/-! ## 2. `ParamGetrennt` -- the predicate on a call frame -/

/-- **Separation of a parameter list**: for every pair of different positions where one
    side is writable, the carrier of the first is absent or differs from the carrier of
    the second. Equivalently: the parameter-to-carrier map is injective on the pairs a
    writable parameter takes part in (`getrennt_paarweise`). Two read-only parameters are
    free -- the paper's S-1. -/
def ParamGetrenntL (D : Deklaration) (ps : List Ty) : Prop :=
  ∀ i j : Fin ps.length, i ≠ j →
    (zaehltFuerTrennung (ps.get i) || zaehltFuerTrennung (ps.get j)) = true →
    traegerVon D (ps.get i) = none ∨ traegerVon D (ps.get i) ≠ traegerVon D (ps.get j)

/-- **`ParamGetrennt` on the call frame of `f`.** In machine G the argument-to-carrier map of a
    call to `f` is fixed by `f`'s signature (§ header), so this is a property of `f`,
    the same at every call site. -/
def ParamGetrennt (D : Deklaration) (f : D.Fn) : Prop := ParamGetrenntL D (D.params f)

/-- The decision procedure, as a Bool over all pairs of positions. -/
def paramGetrenntB (D : Deklaration) (ps : List Ty) : Bool :=
  (List.finRange ps.length).all fun i => (List.finRange ps.length).all fun j =>
    i == j || !(zaehltFuerTrennung (ps.get i) || zaehltFuerTrennung (ps.get j)) ||
    (traegerVon D (ps.get i)).isNone || traegerVon D (ps.get i) != traegerVon D (ps.get j)

/-- The Bool decides the predicate (soundness direction: a `true` is a proof). -/
theorem paramGetrenntB_wahr (D : Deklaration) (ps : List Ty) (h : paramGetrenntB D ps = true) :
    ParamGetrenntL D ps := by
  intro i j hij hz
  simp only [paramGetrenntB, List.all_eq_true] at h
  have h1 := h i (List.mem_finRange _) j (List.mem_finRange _)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq,
    Option.isNone_iff_eq_none] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact absurd h1 hij
  · rw [h1] at hz; cases hz
  · exact .inl h1
  · exact .inr h1

/-- And the other direction: the predicate makes the Bool true. -/
theorem paramGetrenntB_voll (D : Deklaration) (ps : List Ty) (h : ParamGetrenntL D ps) :
    paramGetrenntB D ps = true := by
  simp only [paramGetrenntB, List.all_eq_true]
  intro i _ j _
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq,
    Option.isNone_iff_eq_none]
  by_cases hij : i = j
  · exact .inl (.inl (.inl hij))
  · cases hz : (zaehltFuerTrennung (ps.get i) || zaehltFuerTrennung (ps.get j))
    · exact .inl (.inl (.inr rfl))
    · rcases h i j hij hz with h2 | h2
      · exact .inl (.inr h2)
      · exact .inr h2

theorem paramGetrennt_iff (D : Deklaration) (ps : List Ty) : ParamGetrenntL D ps ↔ paramGetrenntB D ps = true :=
  ⟨paramGetrenntB_voll D ps, paramGetrenntB_wahr D ps⟩

/-! ## 3. Disjoint carriers, and a write through the one leaves the other -/

variable {D : Deklaration}

/-- **Pairwise disjoint**: under `ParamGetrennt`, two different pointer parameters of which one
    is writable name two DIFFERENT carriers. -/
theorem getrennt_paarweise {ps : List Ty} (hG : ParamGetrenntL D ps) (i j : Fin ps.length)
    (hij : i ≠ j) (hz : (zaehltFuerTrennung (ps.get i) || zaehltFuerTrennung (ps.get j)) = true)
    {a b : D.Tab} (ha : traegerVon D (ps.get i) = some a) (hb : traegerVon D (ps.get j) = some b) :
    a ≠ b := by
  intro hab
  rcases hG i j hij hz with h | h
  · rw [ha] at h; cases h
  · exact h (by rw [ha, hb, hab])

/-- **A write through the one leaves every slot of the other**: under `ParamGetrennt`, a slot
    store into the carrier of parameter `i` does not change any slot of the carrier of
    parameter `j`. This is the single-step content of the frame at a separated call. -/
theorem getrennt_schreiben_trennt {ps : List Ty} (hG : ParamGetrenntL D ps) (i j : Fin ps.length)
    (hij : i ≠ j) (hz : (zaehltFuerTrennung (ps.get i) || zaehltFuerTrennung (ps.get j)) = true)
    {a b : D.Tab} (ha : traegerVon D (ps.get i) = some a) (hb : traegerVon D (ps.get j) = some b)
    (σ : World D) (k : Int) (fa : D.Feld a) (v : Wert D (D.typ a fa)) :
    ∀ k' (fb : D.Feld b), (σ.storeSlot a k fa v).slots b k' fb = σ.slots b k' fb := by
  intro k' fb
  exact storeSlot_andere σ a k fa v b (fun h => getrennt_paarweise hG i j hij hz ha hb h.symm) k' fb

/-! ## 4. The frame declared over the parameters, and what it gives at a call -/

/-- **The callee's declared frame is over its parameters**: every table `f` may write is
    the carrier of one of its WRITABLE pointer parameters. This is the scope of the paper's
    claim ("`effects` over its parameters"); a function that also writes a table by its
    declared name has a second root for that table (a static), which `R014` does not
    track and this file does not claim. -/
def RahmenUeberParams (D : Deklaration) (f : D.Fn) : Prop :=
  ∀ t, D.schreibt f t = true →
    ∃ i : Fin (D.params f).length,
      zaehltFuerTrennung ((D.params f).get i) = true ∧ traegerVon D ((D.params f).get i) = some t

/-- Under `ParamGetrennt` and a frame over the parameters, the carrier of a read-only pointer
    parameter is not in the callee's write set. -/
theorem getrennt_nicht_geschrieben {f : D.Fn} (hG : ParamGetrennt D f) (hW : RahmenUeberParams D f)
    (j : Fin (D.params f).length) (hj : zaehltFuerTrennung ((D.params f).get j) = false)
    {t : D.Tab} (ht : traegerVon D ((D.params f).get j) = some t) : D.schreibt f t = false := by
  cases hs : D.schreibt f t
  · rfl
  · obtain ⟨i, hi, hti⟩ := hW t hs
    have hij : i ≠ j := fun h => by subst h; rw [hi] at hj; cases hj
    exact absurd rfl (getrennt_paarweise hG i j hij (by rw [hi]; rfl) hti ht)

/-- **THE PER-PARAMETER FRAME AT A SEPARATED CALL.** For every call handler that keeps the
    declared frame (`TreuR` -- the model's own `rufAt` is one, `rufAt_treu`), every
    function `f` that is `ParamGetrennt` with its frame over its parameters, and every
    read-only pointer parameter `j`: the run leaves every slot of `j`'s carrier as it
    was. The reading "`w : ptr<…, r>` is only read" of `effects { writes k, reads w }` is
    a theorem exactly here. -/
theorem getrennt_lesesicht_bleibt (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : TreuR R) {f : D.Fn} (hG : ParamGetrennt D f) (hW : RahmenUeberParams D f)
    (j : Fin (D.params f).length) (hj : zaehltFuerTrennung ((D.params f).get j) = false)
    {t : D.Tab} (ht : traegerVon D ((D.params f).get j) = some t)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (h : (R f σ ρ).welt = some σ') :
    ∀ k (fld : D.Feld t), σ'.slots t k fld = σ.slots t k fld :=
  (hR f σ ρ σ' h).1.1 t (getrennt_nicht_geschrieben hG hW j hj ht)

/-- **The same at the model's call, `rufAt`, at every depth and every world** (no lock
    premise: `rufAt_treu`). -/
theorem getrennt_ruf_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : TreuO O)
    {f : D.Fn} (hG : ParamGetrennt D f) (hW : RahmenUeberParams D f)
    (j : Fin (D.params f).length) (hj : zaehltFuerTrennung ((D.params f).get j) = false)
    {t : D.Tab} (ht : traegerVon D ((D.params f).get j) = some t)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D)
    (h : (rufAt P O passes fuel f σ ρ).welt = some σ') :
    ∀ k (fld : D.Feld t), σ'.slots t k fld = σ.slots t k fld :=
  getrennt_lesesicht_bleibt _ (rufAt_treu P O passes hO fuel) hG hW j hj ht σ ρ σ' h

/-! ## 5. The borrow rule -/

/-- **A re-view borrows**: a function taking `ptr n` at position `i` and answering
    `ptr n` answers a pointer with the ROOT of its argument -- in the model the root is
    the table the type names, so this holds for every such signature, whatever the body.
    (A re-view across two pointer types does not reach the model; header, obstruction 2.) -/
theorem leihe_wurzel (S : Signatur D.Tab D.Glob D.Lock D.Marke) (i : Fin S.params.length)
    {n : Nat} {rw rw' : Bool} (hi : S.params.get i = .ptr n rw) (he : S.erg = some (.ptr n rw')) :
    ∃ τ, S.erg = some τ ∧ traegerVon D τ = traegerVon D (S.params.get i) := by
  exact ⟨.ptr n rw', he, by rw [hi]; rfl⟩

/-- **Two names of one root are not separated**: a callee with two different parameters of
    one pointer type index (a re-view passed with its source, or two plain parameters of one
    table), one of them writable, whose table exists, is NOT `ParamGetrennt`. -/
theorem leihe_nicht_getrennt {ps : List Ty} (i j : Fin ps.length) (hij : i ≠ j)
    {n : Nat} {rw rw' : Bool} (hi : ps.get i = .ptr n rw) (hj : ps.get j = .ptr n rw')
    (hz : (rw || rw') = true) {t : D.Tab} (ht : D.tabNr n = some t) : ¬ ParamGetrenntL D ps := by
  intro hG
  have hz' : (zaehltFuerTrennung (ps.get i) || zaehltFuerTrennung (ps.get j)) = true := by
    rw [hi, hj]; exact hz
  have ha : traegerVon D (ps.get i) = some t := by rw [hi]; exact ht
  have hb : traegerVon D (ps.get j) = some t := by rw [hj]; exact ht
  exact getrennt_paarweise hG i j hij hz' ha hb rfl

#print axioms Gabbro.Grammatik.paramGetrenntB_wahr
#print axioms Gabbro.Grammatik.paramGetrennt_iff
#print axioms Gabbro.Grammatik.getrennt_paarweise
#print axioms Gabbro.Grammatik.getrennt_schreiben_trennt
#print axioms Gabbro.Grammatik.getrennt_nicht_geschrieben
#print axioms Gabbro.Grammatik.getrennt_lesesicht_bleibt
#print axioms Gabbro.Grammatik.getrennt_ruf_rahmen
#print axioms Gabbro.Grammatik.leihe_wurzel
#print axioms Gabbro.Grammatik.leihe_nicht_getrennt

end Gabbro.Grammatik
