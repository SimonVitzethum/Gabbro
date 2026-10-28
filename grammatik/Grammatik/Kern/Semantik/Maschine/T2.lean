/- Part 2 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

theorem genFilterMap_eigen_fremd (f g : Faden) (hg : g ≠ f) (neu : List (Ereignis D)) :
    (genEigen f neu).filterMap (fun s => if s.faden = g then some s.ereignis else none) = [] := by
  unfold genEigen
  induction neu.reverse with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, Ne.symm hg, ↓reduceIte, List.filterMap_cons_none, ih]

theorem genFilterMap_eigen_take_fremd (f g : Faden) (hg : g ≠ f) (neu : List (Ereignis D))
    (i : Nat) :
    ((genEigen f neu).take i).filterMap (fun s => if s.faden = g then some s.ereignis else none) =
      [] := by
  unfold genEigen
  rw [← List.map_take]
  generalize neu.reverse.take i = xs
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, Ne.symm hg, ↓reduceIte, List.filterMap_cons_none, ih]

/-- After appending: the acting thread's projection grows by `neu`. -/
theorem gen_spur_append_eigen (l : Lauf D) (f : Faden) (neu : List (Ereignis D)) :
    (l ++ genEigen f neu).spur f (l ++ genEigen f neu).length = neu ++ l.spur f l.length := by
  rw [gen_spur_length, gen_spur_length, List.filterMap_append, List.reverse_append,
    genFilterMap_eigen, List.reverse_reverse]

/-- After appending: any other thread's projection is unchanged. -/
theorem gen_spur_append_fremd (l : Lauf D) (f g : Faden) (hg : g ≠ f) (neu : List (Ereignis D))
    (i : Nat) :
    (l ++ genEigen f neu).spur g (l.length + i) = l.spur g l.length := by
  unfold Lauf.spur
  rw [List.take_append, List.take_length, List.filterMap_append,
    show l.length + i - l.length = i by omega, genFilterMap_eigen_take_fremd f g hg,
    List.append_nil, List.take_of_length_le (Nat.le_add_right _ _)]

/-- After appending: any other thread's projection at any covered position. -/
theorem gen_spur_append_fremd_ge (l : Lauf D) (f g : Faden) (hg : g ≠ f)
    (neu : List (Ereignis D)) (j' : Nat) (hj : l.length ≤ j') :
    (l ++ genEigen f neu).spur g j' = l.spur g l.length := by
  unfold Lauf.spur
  rw [List.take_append, List.take_of_length_le hj, List.filterMap_append,
    genFilterMap_eigen_take_fremd f g hg, List.append_nil, List.take_length]

/-- A prefix of the run shows a suffix of the projection. -/
theorem gen_spur_suffix (l : Lauf D) (f : Faden) (j j' : Nat) (hj : j ≤ j') :
    ∃ pre, l.spur f j' = pre ++ l.spur f j := by
  unfold Lauf.spur
  have e : l.take j' = l.take j ++ (l.drop j).take (j' - j) := by
    rw [← List.take_add, Nat.add_sub_cancel' hj]
  rw [e, List.filterMap_append, List.reverse_append]
  exact ⟨_, rfl⟩

theorem gen_spur_ueber (l : Lauf D) (f : Faden) (j : Nat) (hj : l.length ≤ j) :
    l.spur f j = l.spur f l.length := by
  unfold Lauf.spur
  rw [List.take_of_length_le hj, List.take_length]

theorem gen_konsistent_suffix (pre s : List (Ereignis D)) (h : Konsistent (pre ++ s)) :
    Konsistent s := by
  induction pre with
  | nil => exact h
  | cons _ pre ih => exact ih (konsistent_tail h)

theorem gen_eigen_getElem (f : Faden) (neu : List (Ereignis D)) (i : Nat) (g : Faden)
    (e : Ereignis D)
    (h : (genEigen f neu)[i]? = some (Schritt.mk g e)) : g = f ∧ e ∈ neu := by
  unfold genEigen at h
  rw [List.getElem?_map] at h
  cases hx : neu.reverse[i]? with
  | none => rw [hx] at h; simp only [Option.map_none, reduceCtorEq] at h
  | some e' =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq, Schritt.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, List.mem_reverse.mp (List.mem_of_getElem? hx)⟩

theorem gen_getLast_append_singleton (l : List α) (x : α) : (l ++ [x]).getLast? = some x :=
  List.getLast?_concat

/-! ## 9. Writes move memory: `schreibt_wirkt`, and the probe shape as NEGATIVE

   The auditor's probe names the OLD event-to-world fold (§3): every world it
   produces carries the start world's memory (`maschinenWelten_speicher_gleich`
   below -- `merke` extends the trace and nothing else). That shape is kept
   here as the NEGATIVE example: it is what generated worlds escape. A write
   through `execStmt` stores the written value into the world
   (`schreibt_wirkt_slot/glob`), so a write whose value differs moves the
   memory (`schreibt_wirkt_slot_ne/glob_ne`), and a fireable write yields a
   one-step generated run whose memory differs (`gen_write_glob_moves`). -/

/-- The OLD fold preserves memory: every world it produces carries the start
    world's slots and globals. NEGATIVE example (auditor-measured): `merke`
    extends the trace and nothing else, so worlds folded from events alone can
    never be won from writing. Generated worlds (§§7, 10-11) escape exactly
    this shape. -/
theorem weltenFalte_speicher_gleich (σ : World D) (run : Lauf D) :
    ∀ W ∈ weltenFalte σ run, W.slots = σ.slots ∧ W.globs = σ.globs := by
  induction run generalizing σ with
  | nil =>
      intro W hW
      simp only [weltenFalte, List.mem_singleton] at hW
      subst hW
      exact ⟨rfl, rfl⟩
  | cons s rest ih =>
      intro W hW
      simp only [weltenFalte, List.mem_cons] at hW
      rcases hW with rfl | hW
      · exact ⟨rfl, rfl⟩
      · exact ih (σ.merke [s.ereignis]) W hW

theorem maschinenWelten_speicher_gleich (M : MaschinenLauf D) :
    ∀ W ∈ maschinenWelten M, W.slots = M.start.slots ∧ W.globs = M.start.globs :=
  weltenFalte_speicher_gleich M.start M.run

/-- A store hits: the slot carries the stored value afterwards. -/
theorem storeSlot_hit (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) :
    (σ.storeSlot t k f v).slots t k f = v := by
  simp only [World.storeSlot, ↓reduceDIte, ↓reduceIte]

/-- A store hits: the global carries the stored value afterwards. -/
theorem storeGlob_hit (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    (σ.storeGlob g v).globs g = v := by
  simp only [World.storeGlob, ↓reduceDIte]

/-- A write carries its value into the world, with its event. -/
theorem schreibt_wirkt_slot (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ) :
    let σ₁ := σ.lese Λ (i.orte ++ e.orte)
    let k := (eval σ₁ i σ₁ ρ).n
    let v := eval σ₁ e σ₁ ρ
    ((execStmt O passes keinRuf ((.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
      some (σ₁.schreibSlot t Λ k f v)) ∧ (σ₁.schreibSlot t Λ k f v).slots t k f = v := by
  refine ⟨rfl, ?_⟩
  show ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t _ f _).slots _ _ _ = _
  rw [storeSlot_hit]

/-- A write whose value differs moves the memory. -/
theorem schreibt_wirkt_slot_ne (σ₁ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (Λ : List (Res D)) (v : Wert D (D.typ t f)) (hv : v ≠ σ₁.slots t k f) :
    (σ₁.schreibSlot t Λ k f v).speicher ≠ σ₁.speicher := by
  intro hcon
  apply hv
  have h2 : ((σ₁.schreibSlot t Λ k f v).speicher).slots t k f =
      (σ₁.speicher).slots t k f :=
    congrArg (fun s : Speicher D => s.slots t k f) hcon
  have h3 : (σ₁.storeSlot t k f v).slots t k f = σ₁.slots t k f := h2
  rw [storeSlot_hit] at h3
  exact h3

/-- A write carries its value into the world, with its event. -/
theorem schreibt_wirkt_glob (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (σ : World D) (ρ : Env D Γ) :
    let σ₁ := σ.lese Λ e.orte
    let v := eval σ₁ e σ₁ ρ
    ((execStmt O passes keinRuf ((.assignGlob g e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
      some (σ₁.schreibGlob g Λ v)) ∧ (σ₁.schreibGlob g Λ v).globs g = v := by
  refine ⟨rfl, ?_⟩
  show ((σ.lese Λ e.orte).storeGlob g _).globs g = _
  rw [storeGlob_hit]

/-- A write whose value differs moves the memory. -/
theorem schreibt_wirkt_glob_ne (σ₁ : World D) (g : D.Glob)
    (Λ : List (Res D)) (v : Wert D (D.gtyp g)) (hv : v ≠ σ₁.globs g) :
    (σ₁.schreibGlob g Λ v).speicher ≠ σ₁.speicher := by
  intro hcon
  apply hv
  have h2 : ((σ₁.schreibGlob g Λ v).speicher).globs g =
      (σ₁.speicher).globs g :=
    congrArg (fun s : Speicher D => s.globs g) hcon
  have h3 : (σ₁.storeGlob g v).globs g = σ₁.globs g := h2
  rw [storeGlob_hit] at h3
  exact h3

/-- **A fireable write yields a one-step generated run whose memory differs.**
    The write's value comes from the thread's own world (any differing value
    fires: for a boolean global the literals `.tru`/`.fls` always supply
    one); the step is the `blatt` rule with the computed event list. -/
theorem gen_write_glob_moves (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (ρ : Env D Γ)
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (hv : eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ ≠
      ((M.weltVon f).lese Λ e.orte).globs g) :
    ∃ M', GenSchritt P O passes M f M' ∧ M'.speicher.globs g ≠ M.speicher.globs g := by
  have hleaf : ((Stmt.assignGlob (D := D) (V := V) g e hw hL : Stmt D V l Γ Λ Λ)).istBlatt = true := rfl
  have hneu : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
        (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)).spur =
      [Ereignis.gzugriff g true Λ ((M.weltVon f).lese Λ e.orte).haelt] ++
        (e.orte.map fun o => match o with
          | .inl t => Ereignis.zugriff t false Λ (M.weltVon f).haelt
          | .inr g' => Ereignis.gzugriff g' false Λ (M.weltVon f).haelt) ++ M.spuren f := rfl
  refine ⟨_, GenSchritt.blatt M f V l Γ Λ _ ((.assignGlob g e hw hL : Stmt D V l Γ Λ Λ)) ρ hleaf hΛ _ _ rfl hneu ?_, ?_⟩
  · intro L h hm
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hm
    rcases hm with hm | ⟨o, _, hm⟩
    · simp only [reduceCtorEq] at hm
    · cases o <;> simp only [reduceCtorEq] at hm
  · show ((((M.weltVon f).lese Λ e.orte).storeGlob g _).globs g) ≠ _
    rw [storeGlob_hit]
    exact hv

/-! ## 10. Reachable runs are generated, not handed

   From a start machine (shared memory, empty traces, empty run) every step of
   §7 extends reachability inductively (`GenErreichbar`). The invariant
   (`GenInv`) carries what the old structure assumed per thread -- consistency
   and goodness of every trace -- plus the projection link, the world history,
   the scheduler rule, and the step count; every step preserves it. -/

/-- The start machine: shared memory, empty traces, an empty run, and the
    start world with an empty trace. -/
def GenStart (sp : Speicher D) : GenMaschine D :=
  ⟨sp, fun _ => [], [], sp.welt [], [sp.welt []], 0⟩

/-- Reachable machines, generated from `M0` by the step relation. -/
inductive GenErreichbar (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : GenMaschine D) : GenMaschine D → Prop where
  | start : GenErreichbar P O passes M0 M0
  | schritt (M M' : GenMaschine D) (f : Faden)
      (h : GenErreichbar P O passes M0 M) (hs : GenSchritt P O passes M f M') :
      GenErreichbar P O passes M0 M'

/-- One leaf through `execStmt` keeps frame and trace (`stmt_gut`). -/
theorem blatt_brav (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren f))) (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ') :
    Brav (M.weltVon f) σ' :=
  ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ) σ' hstep).2

/-- Old positions of an extended run keep the scheduler rule. -/
theorem genAuss_append_old (l xs : Lauf D) (hA : ForeignExclusion l)
    (j' : Nat) (g : Faden) (L : D.Lock) (h : List D.Lock)
    (hj' : (l ++ xs)[j']? = some (Schritt.mk g (Ereignis.nimmt L h)))
    (hj : j' < l.length) :
    ∀ g', g' ≠ g → ¬ (l ++ xs).haelt g' L j' := by
  rw [List.getElem?_append_left hj] at hj'
  have hold := hA j' g L h hj'
  intro g' hgne
  show ¬ L ∈ offen ((l ++ xs).spur g' j')
  rw [gen_spur_append_le _ _ _ _ (Nat.le_of_lt hj)]
  exact hold g' hgne

/-- A leaf step's new positions: its events are never `nimmt`. -/
theorem genAuss_blatt (l : Lauf D) (f : Faden) (neu : List (Ereignis D))
    (hA : ForeignExclusion l)
    (hkein : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
    ForeignExclusion (l ++ genEigen f neu) := by
  intro j' g L h hj'
  by_cases hj : j' < l.length
  · exact genAuss_append_old l (genEigen f neu) hA j' g L h hj' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hj'
    obtain ⟨-, hmem⟩ := gen_eigen_getElem f neu _ _ _ hj'
    exact absurd hmem (hkein L h)

/-- A `nimmt` step's new position: nobody else held the lock. -/
theorem genAuss_nimmt (l : Lauf D) (sp : Faden → List (Ereignis D)) (f : Faden)
    (L : D.Lock)
    (hA : ForeignExclusion l)
    (hfrei : ∀ g, g ≠ f → L ∉ offen (sp g))
    (hproj : ∀ g, l.spur g l.length = sp g) :
    ForeignExclusion (l ++ genEigen f [Ereignis.nimmt L (offen (sp f))]) := by
  intro j' g L' h' hj'
  by_cases hj : j' < l.length
  · exact genAuss_append_old l _ hA j' g L' h' hj' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hj'
    obtain ⟨hgf, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hj'
    subst g
    simp only [List.mem_singleton] at hmem
    cases hmem
    intro g' hgne
    show ¬ L ∈ offen ((l ++ genEigen f [Ereignis.nimmt L (offen (sp f))]).spur g' j')
    rw [gen_spur_append_fremd_ge _ _ _ hgne _ _ (Nat.le_of_not_lt hj), hproj g']
    exact hfrei g' hgne

/-- A `gibt` step's new position: releasing is never taking. -/
theorem genAuss_gibt (l : Lauf D) (f : Faden) (L : D.Lock)
    (hA : ForeignExclusion l) :
    ForeignExclusion (l ++ genEigen f [Ereignis.gibt L]) := by
  intro j' g L' h' hj'
  by_cases hj : j' < l.length
  · exact genAuss_append_old l _ hA j' g L' h' hj' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hj'
    obtain ⟨-, hmem⟩ := gen_eigen_getElem f [_] _ _ _ hj'
    simp only [List.mem_singleton] at hmem
    cases hmem

/-- The projection after a step: the actor grows by `neu`, everyone else rests. -/
theorem genProj_blatt (l : Lauf D) (sp : Faden → List (Ereignis D)) (f : Faden)
    (neu : List (Ereignis D)) (sneu : List (Ereignis D))
    (hproj : ∀ f', l.spur f' l.length = sp f')
    (hneu : sneu = neu ++ sp f) :
    ∀ f', (l ++ genEigen f neu).spur f' (l ++ genEigen f neu).length =
      genUpdate sp f sneu f' := by
  intro f'
  by_cases hf : f' = f
  · subst f'
    rw [gen_spur_append_eigen, hproj f, ← hneu, genUpdate_self]
  · rw [List.length_append, gen_spur_append_fremd _ _ _ hf, hproj f',
      genUpdate_noteq _ _ _ hf]

/-- What every generated machine maintains. -/
structure GenInv (M : GenMaschine D) : Prop where
  konsistent : ∀ f, Konsistent (M.spuren f)
  spur_gut : ∀ f (e : Ereignis D), e ∈ M.spuren f → e.gut
  welt_gut : ∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut
  proj : ∀ f, M.lauf.spur f M.lauf.length = M.spuren f
  letzte : ∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f))
  auss : ForeignExclusion M.lauf
  tiefe_len : M.welten.length = M.tiefe + 1

theorem genStart_inv (sp : Speicher D) : GenInv (GenStart sp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    show Konsistent ([] : List (Ereignis D))
    exact konsistent_nil
  · intro f e he
    simp only [GenStart, List.not_mem_nil] at he
  · intro W hW e he
    simp only [GenStart, List.mem_singleton] at hW
    subst hW
    change e ∈ ([] : List (Ereignis D)) at he
    simp only [List.not_mem_nil] at he
  · intro f
    show Lauf.spur ([] : Lauf D) f 0 = []
    exact Lauf.spur_zero _ _
  · refine ⟨0, ?_⟩
    show ([sp.welt []]).getLast? = some (sp.welt [])
    exact List.getLast?_singleton
  · intro j g L h hj
    simp only [GenStart, List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hj
  · show (([sp.welt []] : List (World D))).length = (0 : Nat) + 1
    rfl

/-- A leaf step preserves the invariant. -/
theorem genInv_blatt (_P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (_hleaf : s.istBlatt = true)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (hM : GenInv M) :
    GenInv ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
      M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩ := by
  have hb : Brav (M.weltVon f) σ' := blatt_brav O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f'
    by_cases hf : f' = f
    · subst f'
      show Konsistent (genUpdate M.spuren f σ'.spur f)
      rw [genUpdate_self]
      exact hb.2.2 (hM.konsistent f)
    · show Konsistent (genUpdate M.spuren f σ'.spur f')
      rw [genUpdate_noteq _ _ _ hf]
      exact hM.konsistent f'
  · intro f' e he
    by_cases hf : f' = f
    · subst f'
      change e ∈ genUpdate M.spuren f σ'.spur f at he
      rw [genUpdate_self, hneu, List.mem_append] at he
      rcases he with he | he
      · have he' : e ∈ σ'.spur := by rw [hneu]; exact List.mem_append_left _ he
        rcases hb.2.1 e he' with hm | hg
        · exact hM.spur_gut f e hm
        · exact hg
      · exact hM.spur_gut f e he
    · change e ∈ genUpdate M.spuren f σ'.spur f' at he
      rw [genUpdate_noteq _ _ _ hf] at he
      exact hM.spur_gut f' e he
  · intro W hW e he
    have hW' : W ∈ M.welten ∨ W = σ' := by
      change W ∈ M.welten ++ [σ'] at hW
      rwa [List.mem_append, List.mem_singleton] at hW
    rcases hW' with hW' | hW'
    · exact hM.welt_gut W hW' e he
    · subst W
      rw [hneu, List.mem_append] at he
      rcases he with he | he
      · have he' : e ∈ σ'.spur := by rw [hneu]; exact List.mem_append_left _ he
        rcases hb.2.1 e he' with hm | hg
        · exact hM.spur_gut f e hm
        · exact hg
      · exact hM.spur_gut f e he
  · show ∀ f', (M.lauf ++ genEigen f neu).spur f' (M.lauf ++ genEigen f neu).length =
      genUpdate M.spuren f σ'.spur f'
    exact genProj_blatt M.lauf M.spuren f neu σ'.spur hM.proj hneu
  · refine ⟨f, ?_⟩
    show (M.welten ++ [σ']).getLast? =
      some ((σ'.speicher).welt (genUpdate M.spuren f σ'.spur f))
    rw [gen_getLast_append_singleton, genUpdate_self, Speicher.welt_speicher]
  · show ForeignExclusion (M.lauf ++ genEigen f neu)
    exact genAuss_blatt M.lauf f neu hM.auss hkein_nimmt
  · show (M.welten ++ [σ']).length = (M.tiefe + 1) + 1
    simp only [List.length_append, hM.tiefe_len, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.add_left_cancel_iff]

/-- A `nimmt` step preserves the invariant. -/
theorem genInv_nimmt (_P : Programm D) (_O : Orakel D) (_passes : Nat)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hself : L ∉ offen (M.spuren f))
    (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
    (hfrei : GenFrei M f L)
    (hM : GenInv M) :
    GenInv ⟨M.speicher,
      genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f),
      M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))],
      M.start,
      M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)],
      M.tiefe + 1⟩ := by
  have hgut : (Ereignis.nimmt L (offen (M.spuren f))).gut :=
    ⟨hrang, hself⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f'
    by_cases hf : f' = f
    · subst f'
      show Konsistent (genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f)
      rw [genUpdate_self]
      exact konsistent_cons rfl (hM.konsistent f)
    · show Konsistent (genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f')
      rw [genUpdate_noteq _ _ _ hf]
      exact hM.konsistent f'
  · intro f' e he
    by_cases hf : f' = f
    · subst f'
      change e ∈ genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f at he
      rw [genUpdate_self, List.mem_cons] at he
      rcases he with rfl | he
      · exact hgut
      · exact hM.spur_gut f e he
    · change e ∈ genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f' at he
      rw [genUpdate_noteq _ _ _ hf] at he
      exact hM.spur_gut f' e he
  · intro W hW e he
    have hW' : W ∈ M.welten ∨ W = M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) := by
      change W ∈ M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)] at hW
      rwa [List.mem_append, List.mem_singleton] at hW
    rcases hW' with hW' | hW'
    · exact hM.welt_gut W hW' e he
    · subst hW'
      have he' : e ∈ Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f := he
      rw [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact hgut
      · exact hM.spur_gut f e he'
  · show ∀ f', (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))]).spur f' (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))]).length =
      genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f'
    exact genProj_blatt M.lauf M.spuren f [Ereignis.nimmt L (offen (M.spuren f))] (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) hM.proj rfl
  · refine ⟨f, ?_⟩
    show (M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)]).getLast? =
      some (M.speicher.welt (genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) f))
    rw [gen_getLast_append_singleton, genUpdate_self]
  · show ForeignExclusion (M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))])
    exact genAuss_nimmt M.lauf M.spuren f L hM.auss hfrei hM.proj
  · show (M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)]).length = (M.tiefe + 1) + 1
    simp only [List.length_append, hM.tiefe_len, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.add_left_cancel_iff]


end Gabbro.Grammatik
