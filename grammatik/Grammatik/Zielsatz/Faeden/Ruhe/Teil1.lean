module

public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch

@[expose] public section



namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-! ## The answer sites on `P.mitRuhe` (round-6 finding W1) -/

section Ants

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem ants_nachΛ {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (s : Stmt D V l Γ Λ Λ₁) :
    (Stmt.nachΛ h s).ants = s.ants := by subst h; rfl
theorem ants_vorΛ {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂) (b : Block D V l Γ Λ₁ Λ') :
    (Block.vorΛ h b).ants = b.ants := by subst h; rfl
theorem ants_umΛ {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (e : Endblock D V l Γ Λ₁) :
    (Endblock.umΛ h e).ants = e.ants := by subst h; rfl

end Ants

mutual

theorem ruS_ants {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), (ruS s).ants = s.ants
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· ++ ·) (ruB_ants t) (ruB_ants e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· ++ ·) (ruB_ants p) (ruB_ants a)
  | _, _, _, _, .onTag _ arms => ruArms_ants arms
  | _, _, _, _, .onWhy _ arms => ruGArms_ants arms
  | _, _, _, _, .call .. => ants_nachΛ _ _
  | _, _, _, _, .callInd .. => ants_nachΛ _ _
  | _, _, _, _, .locks _ _ body => ruB_ants body
  | _, _, _, _, .breaking _ body => ruB_ants body
  | _, _, _, _, .traverse _ _ body => ruB_ants body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· ++ ·) (ruB_ants body) (ruB_ants ueber)
  | _, _, _, _, .forever _ _ body => ruB_ants body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => ants_nachΛ _ _
  | _, _, _, _, .retires .. => ants_nachΛ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_ants {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), (ruB b).ants = b.ants
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_ants s) (ruB_ants rest)
  | _, _, _, _, .bind _ rest => ruB_ants rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (ants_vorΛ _ _).trans (ruB_ants rest)
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => (ants_vorΛ _ _).trans (ruB_ants rest)
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((ants_umΛ _ _).trans (ruEnd_ants err))
        ((ants_vorΛ _ _).trans (ruB_ants rest))
  | _, _, _, _, .bindAxiom a _ _ _ _ _ _ rest => congrArg (Sum.inl a :: ·) (ruB_ants rest)
  | _, _, _, _, .bindAxiomElse a _ _ _ _ _ _ _ err rest =>
      congrArg (Sum.inl a :: ·) (kongr₂ (· ++ ·) (ruEnd_ants err) (ruB_ants rest))
  | _, _, _, _, .regRead r _ rest => congrArg (Sum.inr r :: ·) (ruB_ants rest)
  | _, _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (Sum.inr r :: ·) (kongr₂ (· ++ ·) (ruEnd_ants sonst) (ruB_ants rest))
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_ants rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_ants rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· ++ ·) (ruEnd_ants sonst) (ruB_ants rest)
  | _, _, _, _, .check _ sonst rest => kongr₂ (· ++ ·) (ruEnd_ants sonst) (ruB_ants rest)
  | _, _, _, _, .float _ _ _ _ _ rest => ruB_ants rest
  | _, _, _, _, .floatLit _ _ _ rest => ruB_ants rest
  | _, _, _, _, .floatOf _ _ _ rest => ruB_ants rest
  | _, _, _, _, .floatNarrow _ _ _ sonst rest =>
      kongr₂ (· ++ ·) (ruEnd_ants sonst) (ruB_ants rest)

theorem ruEnd_ants {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), (ruEnd e).ants = e.ants
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_ants s) (ruEnd_ants rest)
  | _, _, _, .bind _ rest => ruEnd_ants rest
  | _, _, _, .bindCall _ _ _ _ _ rest => (ants_umΛ _ _).trans (ruEnd_ants rest)
  | _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((ants_umΛ _ _).trans (ruEnd_ants err))
        ((ants_umΛ _ _).trans (ruEnd_ants rest))
  | _, _, _, .bindAxiom a _ _ _ _ _ _ rest => congrArg (Sum.inl a :: ·) (ruEnd_ants rest)
  | _, _, _, .bindAxiomElse a _ _ _ _ _ _ _ err rest =>
      congrArg (Sum.inl a :: ·) (kongr₂ (· ++ ·) (ruEnd_ants err) (ruEnd_ants rest))
  | _, _, _, .regRead r _ rest => congrArg (Sum.inr r :: ·) (ruEnd_ants rest)
  | _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (Sum.inr r :: ·) (kongr₂ (· ++ ·) (ruEnd_ants sonst) (ruEnd_ants rest))
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_ants rest
  | _, _, _, .bindCallInd _ _ _ _ _ rest => (ants_umΛ _ _).trans (ruEnd_ants rest)
  | _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· ++ ·) (ruEnd_ants sonst) (ruEnd_ants rest)
  | _, _, _, .exchange _ _ _ _ rest => ruEnd_ants rest
  | _, _, _, .ite _ t e => kongr₂ (· ++ ·) (ruEnd_ants e) (ruEnd_ants t)

theorem ruArms_ants {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    (ruArms arms).ants = arms.ants
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· ++ ·) (ruB_ants b) (ruArms_ants rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
      kongr₂ (· ++ ·) (ruB_ants b) (ruArms_ants rest)

theorem ruGArms_ants {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), (ruGArms arms).ants = arms.ants
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· ++ ·) (ruB_ants b) (ruGArms_ants rest)

end

/-- A body of `P.mitRuhe` has the answer sites of the body of `P`; the root has none. -/
theorem rumpf_mitRuhe_ants (P : Programm D) (f : D.Fn) :
    (P.mitRuhe.rumpf (some f)).ants = (P.rumpf f).ants :=
  (ants_umΛ _ _).trans (ruEnd_ants _)

theorem wertOk_valR : ∀ (τ : Ty) (v : Wert D τ),
    WertOk (D := D.mitRuhe) (tyR τ) (valR τ v) ↔ WertOk τ v
  | .int _ _, _ => Iff.rfl
  | .bool, _ => Iff.rfl
  | .opt _, _ => Iff.rfl
  | .sum _, _ => Iff.rfl
  | .why _, _ => Iff.rfl
  | .never, _ => Iff.rfl
  | .fl _ _, _ => Iff.rfl
  | .fnptr _, _ => Iff.rfl
  | .ptr _ _, _ => Iff.rfl
  | .ref _, _ => Iff.rfl
  | .arr _ _, _ => Iff.rfl
  | .str _, _ => Iff.rfl

/-- **An answer class of `D.mitRuhe` is empty exactly when it is in `D`**: the shifted types
    have the shifted values (`valR`/`valZ`), and no shifted pointer type names the root. -/
theorem antwortLeer_mitRuhe (e : Option Ty) :
    AntwortLeer D.mitRuhe (e.map tyR) ↔ AntwortLeer D e := by
  cases e with
  | none => exact ⟨fun h => absurd h antwortLeer_keinErg, fun h => absurd h antwortLeer_keinErg⟩
  | some τ =>
      show AntwortLeer D.mitRuhe (some (tyR τ)) ↔ _
      rw [antwortLeer_iff, antwortLeer_iff]
      constructor
      · intro h v hv
        exact h (valR τ v) ((wertOk_valR τ v).mpr hv)
      · intro h v hv
        have e : valR τ (valZ τ v) = v := valR_valZ τ v
        rw [← e] at hv
        exact h (valZ τ v) ((wertOk_valR τ _).mp hv)

theorem tyR_never : ∀ τ : Ty, tyR τ = .never ↔ τ = .never
  | .int _ _ => by simp only [reduceCtorEq]
  | .bool => by simp only [reduceCtorEq]
  | .opt _ => by simp only [reduceCtorEq]
  | .sum _ => by simp only [reduceCtorEq]
  | .why _ => by simp only [reduceCtorEq]
  | .never => by simp only
  | .fl _ _ => by simp only [reduceCtorEq]
  | .fnptr _ => by simp only [reduceCtorEq]
  | .ptr _ _ => by simp only [reduceCtorEq]
  | .ref _ => by simp only [reduceCtorEq]
  | .arr _ _ => by simp only [reduceCtorEq]
  | .str _ => by simp only [reduceCtorEq]

theorem stelleAx_mitRuhe (e : Option Ty) :
    (e.map tyR = some .never ∨ ¬ AntwortLeer D.mitRuhe (e.map tyR)) ↔
      (e = some .never ∨ ¬ AntwortLeer D e) := by
  rw [antwortLeer_mitRuhe]
  cases e with
  | none => simp only [Option.map_none, reduceCtorEq, false_or]
  | some τ => simp only [Option.map_some, Option.some.injEq, tyR_never]

/-- An answer site of `D.mitRuhe` is admissible exactly when it is in `D`. -/
theorem stelleOk_mitRuhe (x : D.Ax ⊕ D.Reg) : StelleOk D.mitRuhe x ↔ StelleOk D x := by
  cases x with
  | inl a => exact stelleAx_mitRuhe (D.aerg a)
  | inr r => exact not_congr (antwortLeer_mitRuhe (some (D.rtyp r)))

theorem decide_succ_eq (a b : Nat) : decide (a + 1 = b + 1) = decide (a = b) :=
  decide_eq_decide.mpr ⟨Nat.succ.inj, fun e => e ▸ rfl⟩

theorem bewacht_mitRuhe (c : D.Tab ⊕ D.Glob) (L : D.Lock) :
    @Bewacht D.mitRuhe c L ↔ @Bewacht D c L := by
  cases c <;> exact Iff.rfl

theorem waechter_mitRuhe (l : List (D.Lock ⊕ (D.Marke × Nat))) :
    waechter (D := D.mitRuhe) l = waechter (D := D) l := by
  induction l with
  | nil => rfl
  | cons w l ih => rcases w with L | m <;> simp only [waechter, ih]

theorem waechterVon_mitRuhe (c : D.Tab ⊕ D.Glob) :
    waechterVon (D := D.mitRuhe) c = waechterVon (D := D) c := by
  rcases c with t | g
  · exact waechter_mitRuhe (D := D) (D.braucht t)
  · exact waechter_mitRuhe (D := D) (D.gbraucht g)

theorem sigB_mitRuhe (f : D.Fn) (c : D.Tab ⊕ D.Glob) : sigB (D := D.mitRuhe) (some f) c = sigB f c := by
  unfold sigB
  rw [waechterVon_mitRuhe]
  rfl

theorem traegerSchreibt_mitRuhe (f : D.Fn) (c : D.Tab ⊕ D.Glob) :
    TraegerSchreibt (D := D.mitRuhe) (some f) c = TraegerSchreibt f c := by
  cases c <;> rfl

theorem atomar_mitRuhe (c : D.Tab ⊕ D.Glob) :
    AtomarAusgenommen (D := D.mitRuhe) c ↔ AtomarAusgenommen (D := D) c := Iff.rfl

theorem paarung_mitRuhe (c : D.Tab ⊕ D.Glob) :
    PaarungAusgenommen (D := D.mitRuhe) c ↔ PaarungAusgenommen (D := D) c := Iff.rfl

theorem mem_wsRuhe {ws : List D.Fn} {w' : D.mitRuhe.Fn} :
    w' ∈ wsRuhe ws ↔ ∃ w ∈ ws, w' = some w := by
  unfold wsRuhe
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := List.mem_map.mp h
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact List.mem_map_of_mem hw

/-- "Declared twice" survives an injective renaming both ways (fix lane F10). -/
theorem mehrfach_map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b)
    {ws : List α} {w : α} : Mehrfach (ws.map f) (f w) ↔ Mehrfach ws w := by
  constructor
  · intro h
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.mp h
    rcases l' with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp only [List.map_nil, reduceCtorEq, List.map_cons, List.cons.injEq, List.cons_ne_self, and_false, and_true, List.nil_eq] at he
    obtain ⟨h1, h2⟩ := he
    rw [hf a w h1.symm, hf b w h2.symm] at hl'
    exact hl'
  · intro h
    exact h.map f

/-- Two different positions holding one value make it "declared twice". -/
theorem mehrfach_of_getElem? {α : Type} : ∀ {l : List α} {i j : Nat} {x : α}, i < j →
    l[i]? = some x → l[j]? = some x → Mehrfach l x
  | [], _, _, _, _, hi, _ => by simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hi
  | _ :: _, _, 0, _, hij, _, _ => by omega
  | a :: l, 0, j + 1, x, _, hi, hj => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      simp only [List.getElem?_cons_succ] at hj
      subst hi
      exact List.Sublist.cons_cons a (List.singleton_sublist.mpr (List.mem_of_getElem? hj))
  | a :: l, i + 1, j + 1, x, hij, hi, hj => by
      simp only [List.getElem?_cons_succ] at hi hj
      exact List.Sublist.cons a (mehrfach_of_getElem? (by omega) hi hj)

section Transfer

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

theorem reach_mitRuhe_cases (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {w : D.Fn} {g' : D.mitRuhe.Fn} (h : reachB P.mitRuhe (fsRuhe fs) (some w) g' = true) :
    ∃ g, g' = some g ∧ reachB P fs w g = true := by
  cases g' with
  | none => rw [reachB_mitRuhe_nicht_ruhe P hAbg] at h; cases h
  | some g => exact ⟨g, rfl, by rw [← reachB_mitRuhe P hvoll hAbg]; exact h⟩

theorem reach_mitRuhe_ruhe_cases {g' : D.mitRuhe.Fn}
    (h : reachB P.mitRuhe (fsRuhe fs) none g' = true) : g' = none := by
  cases g' with
  | none => rfl
  | some g => rw [reachB_mitRuhe_ruhe P g] at h; cases h

theorem getrennt_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {c : D.Tab ⊕ D.Glob} (h : Getrennt P fs ws c) :
    Getrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c := by
  intro w₁' hw₁' w₂' hw₂' hne f' g' hf' hc hg'
  obtain ⟨w₁, hw₁, rfl⟩ := mem_wsRuhe.mp hw₁'
  obtain ⟨w₂, hw₂, rfl⟩ := mem_wsRuhe.mp hw₂'
  obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
  obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hg'
  rw [fussOrteG_mitRuhe] at hc
  rw [traegerSchreibt_mitRuhe]
  have hne' : w₁ ≠ w₂ ∨ Mehrfach ws w₁ := by
    rcases hne with hne | hne
    · exact Or.inl (fun e => hne (e ▸ rfl))
    · exact Or.inr ((mehrfach_map_inj (fun a b e => Option.some.inj e)).mp hne)
  exact h w₁ hw₁ w₂ hw₂ hne' f g hf hc hg

theorem schreibGetrennt_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ w, AbgK P fs (reachB P fs w)) {c : D.Tab ⊕ D.Glob}
    (h : SchreibGetrennt P fs ws c) : SchreibGetrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c := by
  intro w₁' hw₁' w₂' hw₂' hne g' hg' hgw h' hh'
  obtain ⟨w₁, hw₁, rfl⟩ := mem_wsRuhe.mp hw₁'
  obtain ⟨w₂, hw₂, rfl⟩ := mem_wsRuhe.mp hw₂'
  obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hg'
  obtain ⟨k, rfl, hk⟩ := reach_mitRuhe_cases P hvoll hAbg hh'
  rw [fussOrteG_mitRuhe, traegerSchreibt_mitRuhe]
  rw [traegerSchreibt_mitRuhe] at hgw
  exact h w₁ hw₁ w₂ hw₂ (fun e => hne (e ▸ rfl)) g hg hgw k hk

theorem lokW_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {c : D.Tab ⊕ D.Glob} (h : lokW P fs ws c = true) :
    lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws) c = true := by
  unfold lokW at h ⊢
  exact @decide_eq_true _ (Classical.propDecidable _)
    (getrennt_mitRuhe P hvoll hAbg (@of_decide_eq_true _ (Classical.propDecidable _) h))

/-- **The pool condition transfers to `P.mitRuhe`** (fix lane F10): the root is
    declared nowhere, and a user routine keeps its graph, writes and guards. -/
theorem einzelnPool_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : EinzelnPool P fs ws) : EinzelnPool P.mitRuhe (fsRuhe fs) (wsRuhe ws) := by
  intro w' hm
  cases w' with
  | none =>
      exfalso
      obtain ⟨w, _, e⟩ := mem_wsRuhe.mp (hm.subset List.mem_cons_self)
      cases e
  | some w =>
      have hp := h w ((mehrfach_map_inj (fun a b e => Option.some.inj e)).mp hm)
      refine ⟨hp.1, hp.2.1, fun f' hf' c hc => ?_⟩
      obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
      rw [traegerSchreibt_mitRuhe] at hc
      rcases hp.2.2 f hf c hc with ⟨L, hL⟩ | hA
      · exact Or.inl ⟨L, (bewacht_mitRuhe (D := D) c L).mpr hL⟩
      · exact Or.inr ((atomar_mitRuhe (D := D) c).mpr hA)

omit [DecidableEq D.Fn] in
theorem kandB_mitRuhe (L : List (D.Tab ⊕ D.Glob)) :
    kZ (kandB P.mitRuhe (fsRuhe fs) L) = kandB P fs L := by
  funext n
  show kandB P.mitRuhe (fsRuhe fs) L (n + 1) = kandB P fs L n
  unfold kandB
  rw [all_fsRuhe]
  have h0 : (D.mitRuhe).passt none (n + 1) = false :=
    decide_eq_false (Nat.succ_ne_zero n)
  rw [h0, Bool.not_false, Bool.true_or, Bool.true_and]
  congr 1
  funext g
  show (!D.passt g n ||
    ((P.mitRuhe.requires (some g)).orte ++ (P.mitRuhe.ensures (some g)).orte).all _) = _
  rw [requires_mitRuhe_orte, ensures_mitRuhe_orte]

omit [DecidableEq D.Fn] in
theorem frag_mitRuhe (h : programmImFragmentG P fs = true) :
    programmImFragmentG P.mitRuhe (fsRuhe fs) = true := by
  unfold programmImFragmentG
  rw [all_fsRuhe]
  refine Bool.and_eq_true_iff.mpr ⟨rfl, List.all_eq_true.mpr fun f hf => ?_⟩
  refine (rumpf_mitRuhe_gOk P _ _ f).trans ?_
  rw [kandB_mitRuhe, fussOrteG_mitRuhe]
  exact (List.all_eq_true.mp h) f hf

theorem abg_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w)) :
    ∀ w', AbgK P.mitRuhe (fsRuhe fs) (reachB P.mitRuhe (fsRuhe fs) w') := by
  intro w' f' hf'
  cases w' with
  | none =>
      rw [reach_mitRuhe_ruhe_cases P hf']
      rfl
  | some w =>
      obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
      rw [rumpf_mitRuhe_mE]
      have e : mZ (rufM (fsRuhe fs) (reachB P.mitRuhe (fsRuhe fs) (some w))) =
          rufM fs (reachB P fs w) := by
        apply merkmal_ext
        · funext h
          exact reachB_mitRuhe P hvoll hAbg w h
        · funext n
          show (fsRuhe fs).all (fun g' => !((D.mitRuhe).passt g' (n + 1)) ||
            reachB P.mitRuhe (fsRuhe fs) (some w) g') = _
          rw [all_fsRuhe]
          have h0 : (D.mitRuhe).passt none (n + 1) = false :=
            decide_eq_false (Nat.succ_ne_zero n)
          rw [h0, Bool.not_false, Bool.true_or, Bool.true_and]
          congr 1
          funext g
          show (!D.passt g n || reachB P.mitRuhe (fsRuhe fs) (some w) (some g)) = _
          rw [reachB_mitRuhe P hvoll hAbg]
        · rfl
      rw [e]
      exact hAbg w f hf

theorem fussS_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : ∀ f, FussS P S (lokW P fs ws) f) :
    ∀ f', FussS P.mitRuhe S.mitRuhe (lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws)) f'
  | none => ⟨fun c hc => by rw [fussOrte_mitRuhe_ruhe] at hc; exact absurd hc List.not_mem_nil,
      fun c hc => absurd hc List.not_mem_nil⟩
  | some f => by
      obtain ⟨h1, h2⟩ := h f
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [fussOrte_mitRuhe] at hc
        rcases h1 c hc with h3 | ⟨L, hL, hcL⟩
        · left
          simp only [Bool.or_eq_true] at h3 ⊢
          rw [sigB_mitRuhe]
          exact h3.imp id (lokW_mitRuhe P hvoll hAbg)
        · exact Or.inr ⟨L, (bewacht_mitRuhe (D := D) c L).mpr hL, hcL⟩
      · have hc' : c ∈ (P.rumpf f).regs.flatMap D.rtraeger := by
          have e := rumpf_mitRuhe_regs P f
          exact e ▸ hc
        have h3 := h2 c hc'
        simp only [Bool.or_eq_true] at h3 ⊢
        rw [sigB_mitRuhe]
        exact h3.imp id (lokW_mitRuhe P hvoll hAbg)

omit [DecidableEq D.Fn] in
theorem stufen_mitRuhe (h : StufenM P) : StufenM P.mitRuhe
  | none => rfl
  | some f => by
      show mE (bodenM (some f)) (P.mitRuhe.rumpf (some f)) = true
      rw [rumpf_mitRuhe_mE]
      exact h f

end Transfer
end Gabbro.Grammatik
