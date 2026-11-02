module
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch
import Grammatik.Kern.Semantik.Semantik.T1.SummeTransport
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
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body => ruB_ants body
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
  | _, _, _, _, .retScoped .. => rfl
  | _, _, _, _, .retWhyScoped .. => rfl
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
  | _, _, _, _, .narrowRequired _ _ _ rest => ruB_ants rest
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
  | _, _, _, .retScoped .. => rfl
  | _, _, _, .retWhyScoped .. => rfl
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
  | _, _, _, .narrowRequired _ _ _ rest => ruEnd_ants rest
  | _, _, _, .exchange _ _ _ _ rest => ruEnd_ants rest
  | _, _, _, .ite _ t e => kongr₂ (· ++ ·) (ruEnd_ants e) (ruEnd_ants t)

theorem ruArms_ants {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
    (ruArms arms).ants = arms.ants
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· ++ ·) (ruB_ants b) (ruArms_ants rest)
  | _, _, _, _, _, .cons (c := some _) b rest =>
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
  | .sum cs, _ => by
      change sumWort (Ty.mapCases (fun n => n + 1) id cs) = true ↔ sumWort cs = true
      rw [sumWort_mapCases]
  | .why _, _ => Iff.rfl
  | .never, _ => Iff.rfl
  | .fl _ _, _ => Iff.rfl
  | .fnptr _, _ => Iff.rfl
  | .ptr _, _ => Iff.rfl
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
  | .ptr _ => by simp only [reduceCtorEq]
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
end Gabbro.Grammatik
