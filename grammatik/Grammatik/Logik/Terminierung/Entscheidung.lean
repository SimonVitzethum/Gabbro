/-
  File:      Grammatik/Logik/Terminierung/Entscheidung.lean
  Subject:   T5 -- THE CLASSES MEET THE SEMANTICS (2026-10-22).

  * `tor_gut` -- the call gate of T4 holds for EVERY program, with the rank computed from the call graph
    (`rangB f`: how many functions `f` reaches) and the cycles of `zykS`: a callee reaches no more than its
    caller, and as many only if it reaches the caller back. So T4 needs nothing static beyond measures of one
    length along a cycle.
  * `terminierung` -- for every program whose measures meet the user's duty (`MassPflicht`, the `decreases`
    obligation): on every infinite run of machine GX every thread takes only finitely many steps. The budget
    `passes` is what makes a `forever` finite here; machine G grants the passes from outside.
  * `endet_ohne_budget` -- a thread whose start is of class `endet` (`klasse`, T1) never stands at a spent budget:
    no frame of it ever runs a `forever`. Its end does not lean on the budget.
  * `umgebung` and `bedingt` carry no theorem of their own beyond these two: their runs are finite per pass (T3,
    `durchgang_schritte`) and they may stop at the budget; whether a `leave` guard, a `return` inside the loop or a
    base path is ever taken is the program's question (undecidable in general).
-/
import Grammatik.Logik.Terminierung.Rekursion
import Grammatik.Gen.Abdeckung.Satz.MerkmalZerlegt
import Grammatik.Zielsatz.Faeden.Verbund.T1
import Grammatik.Logik.Ruf.Maschine.BudgetMonoton

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The gates read as feature sets -/

section Gate

variable (Z : D.Fn → Bool) (ZS : Nat → Bool) {V : Vertrag D}

mutual

theorem rufeS_mS : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    rufeS Z ZS true s = mS ⟨Z, ZS, fun _ => true⟩ s
  | _, _, _, _, .ite _ t e => by simp only [rufeS, mS, rufeB_mB t, rufeB_mB e]
  | _, _, _, _, .onOption _ p a => by simp only [rufeS, mS, rufeB_mB p, rufeB_mB a]
  | _, _, _, _, .onTag _ arms => by simp only [rufeS, mS, rufeArms_mArms arms]
  | _, _, _, _, .onWhy _ arms => by simp only [rufeS, mS, rufeGArms_mGArms arms]
  | _, _, _, _, .call .. => rfl
  | _, _, _, _, .callInd .. => rfl
  | _, _, _, _, .locks _ _ body => by simp only [rufeS, mS, rufeB_mB body, Bool.true_and]
  | _, _, _, _, .breaking _ body => by simp only [rufeS, mS, rufeB_mB body]
  | _, _, _, _, .traverse _ _ body => by simp only [rufeS, mS, rufeB_mB body]
  | _, _, _, _, .retry _ _ body ueber => by simp only [rufeS, mS, rufeB_mB body, rufeB_mB ueber]
  | _, _, _, _, .forever _ _ body => by simp only [rufeS, mS, rufeB_mB body, Bool.true_and]
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => rfl
  | _, _, _, _, .retires .. => rfl
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem rufeB_mB : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    rufeB Z ZS true b = mB ⟨Z, ZS, fun _ => true⟩ b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => by simp only [rufeB, mB, rufeS_mS s, rufeB_mB rest]
  | _, _, _, _, .bind _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindCall _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest => by simp only [rufeB, mB, rufeE_mE err, rufeB_mB rest]
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [rufeB, mB, rufeE_mE err, rufeB_mB rest]
  | _, _, _, _, .regRead _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .regReadElse _ _ _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]
  | _, _, _, _, .awaits _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .exchange _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .narrow _ _ _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]
  | _, _, _, _, .check _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]
  | _, _, _, _, .float _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .floatLit _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .floatOf _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .floatNarrow _ _ _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]

theorem rufeArms_mArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs), rufeArms Z ZS true arms = mArms ⟨Z, ZS, fun _ => true⟩ arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => by simp only [rufeArms, mArms, rufeB_mB b, rufeArms_mArms rest]

theorem rufeGArms_mGArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), rufeGArms Z ZS true arms = mGArms ⟨Z, ZS, fun _ => true⟩ arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => by simp only [rufeGArms, mGArms, rufeB_mB b, rufeGArms_mGArms rest]

theorem rufeE_mE : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    rufeE Z ZS true e = mE ⟨Z, ZS, fun _ => true⟩ e
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => by simp only [rufeE, mE, rufeS_mS s, rufeE_mE rest]
  | _, _, _, .bind _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCall _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCallElse _ _ _ _ _ err rest => by simp only [rufeE, mE, rufeE_mE err, rufeE_mE rest]
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [rufeE, mE, rufeE_mE err, rufeE_mE rest]
  | _, _, _, .regRead _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .regReadElse _ _ _ sonst rest => by simp only [rufeE, mE, rufeE_mE sonst, rufeE_mE rest]
  | _, _, _, .awaits _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCallInd _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]

end

/-- The `forever` gate is idle where the syntax holds no `forever`. -/
theorem befund_und_ewig (a b : Befund D) : (a ++ b).ewig = (a.ewig || b.ewig) := rfl

mutual

theorem rufeS_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (eb ie dl : Bool), (befS eb ie dl s).ewig = false → rufeS Z ZS false s = rufeS Z ZS true s
  | _, _, _, _, .ite _ t e, eb, ie, _, h => by
      simp only [befS, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeS, rufeB_ohneEwig t eb ie h.1, rufeB_ohneEwig e eb ie h.2]
  | _, _, _, _, .onOption _ p a, eb, ie, _, h => by
      simp only [befS, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeS, rufeB_ohneEwig p eb ie h.1, rufeB_ohneEwig a eb ie h.2]
  | _, _, _, _, .onTag _ arms, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeArms_ohneEwig arms eb ie h]
  | _, _, _, _, .onWhy _ arms, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeGArms_ohneEwig arms eb ie h]
  | _, _, _, _, .call .., _, _, _, _ => rfl
  | _, _, _, _, .callInd .., _, _, _, _ => rfl
  | _, _, _, _, .locks _ _ body, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body eb ie h]
  | _, _, _, _, .breaking _ body, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body eb ie h]
  | _, _, _, _, .traverse _ _ body, _, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body false ie h]
  | _, _, _, _, .retry _ _ body ueber, eb, ie, _, h => by
      simp only [befS, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeS, rufeB_ohneEwig body false ie h.1, rufeB_ohneEwig ueber eb ie h.2]
  | _, _, _, _, .forever _ _ _, _, _, _, h => by
      simp only [befS, befund_und_ewig, Bool.true_or, Bool.true_eq_false] at h
  | _, _, _, _, .assignSlot .., _, _, _, _ => rfl
  | _, _, _, _, .assignThru .., _, _, _, _ | _, _, _, _, .assignSlotRef .., _, _, _, _ => rfl
  | _, _, _, _, .assignGlob .., _, _, _, _ => rfl
  | _, _, _, _, .putBytes .., _, _, _, _ => rfl
  | _, _, _, _, .assignVar .., _, _, _, _ => rfl
  | _, _, _, _, .shift .., _, _, _, _ => rfl
  | _, _, _, _, .axiomCall .., _, _, _, _ => rfl
  | _, _, _, _, .regWrite .., _, _, _, _ => rfl
  | _, _, _, _, .transition .., _, _, _, _ => rfl
  | _, _, _, _, .publish .., _, _, _, _ => rfl
  | _, _, _, _, .advances .., _, _, _, _ => rfl
  | _, _, _, _, .retires .., _, _, _, _ => rfl
  | _, _, _, _, .ret .., _, _, _, _ => rfl
  | _, _, _, _, .retWhy .., _, _, _, _ => rfl
  | _, _, _, _, .leave _, _, _, _, _ => rfl
  | _, _, _, _, .next _, _, _, _, _ => rfl

theorem rufeB_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
    (eb ie : Bool), (befB eb ie b).ewig = false → rufeB Z ZS false b = rufeB Z ZS true b
  | _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, .cons s rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeS_ohneEwig s eb ie _ h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bind _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .bindCall _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig err eb ie h.1.2, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig err eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .regRead _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .regReadElse _ _ _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .awaits _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .exchange _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .narrow _ _ _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .check _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .float _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .floatLit _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .floatOf _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]

theorem rufeArms_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (eb ie : Bool), (befArms eb ie arms).ewig = false →
      rufeArms Z ZS false arms = rufeArms Z ZS true arms
  | _, _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, _, .cons b rest, eb, ie, h => by
      simp only [befArms, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeArms, rufeB_ohneEwig b eb ie h.1, rufeArms_ohneEwig rest eb ie h.2]

theorem rufeGArms_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (eb ie : Bool), (befGArms eb ie arms).ewig = false →
      rufeGArms Z ZS false arms = rufeGArms Z ZS true arms
  | _, _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, _, .cons b rest, eb, ie, h => by
      simp only [befGArms, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeGArms, rufeB_ohneEwig b eb ie h.1, rufeGArms_ohneEwig rest eb ie h.2]

theorem rufeE_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ)
    (eb ie : Bool), (befE eb ie e).ewig = false → rufeE Z ZS false e = rufeE Z ZS true e
  | _, _, _, .ret .., _, _, _ => rfl
  | _, _, _, .retWhy .., _, _, _ => rfl
  | _, _, _, .leave _, _, _, _ => rfl
  | _, _, _, .next _, _, _, _ => rfl
  | _, _, _, .cons s rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeS_ohneEwig s eb ie _ h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bind _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindCall _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig err eb ie h.1.2, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig err eb ie h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .regRead _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .regReadElse _ _ _ sonst rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig sonst eb ie h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .awaits _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindCallInd _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h.2]

end

end Gate

/-! ## 2. The rank from the call graph; the gate holds for every program -/

section Rang

variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn)

/-- **The rank of `f`**: how many functions it reaches. -/
def rangB (f : D.Fn) : Nat := fs.countP (reachB P fs f)

variable {P fs} (hvoll : ∀ g : D.Fn, g ∈ fs)
include hvoll

theorem reachB_trans {f g h : D.Fn} (h1 : reachB P fs f g = true) (h2 : reachB P fs g h = true) :
    reachB P fs f h = true :=
  Zielsatz.reachB_in P fs (Z := fun x => reachB P fs f x = true) h1
    (fun _ _ ha hr => Zielsatz.reachB_ruft P hvoll ha hr) h h2

theorem rangB_le {f g : D.Fn} (h : reachB P fs f g = true) : rangB P fs g ≤ rangB P fs f :=
  List.countP_mono_left (fun _ _ hx => reachB_trans hvoll h hx)

theorem rangB_lt {f g : D.Fn} (h : reachB P fs f g = true) (hn : reachB P fs g f = false) :
    rangB P fs g < rangB P fs f :=
  Zielsatz.countP_lt_of (reachB P fs g) (reachB P fs f) fs (fun _ hx => reachB_trans hvoll h hx)
    ⟨f, hvoll f, reachB_wurzel P fs f, hn⟩

/-- **Every callee passes the gate**: it reaches no more than its caller, and as many only on the caller's cycle. -/
theorem tor_ruft {f g : D.Fn} (hr : ruftB P f g = true) : tor (zykS P fs) (rangB P fs) f g = true := by
  have hfg : reachB P fs f g = true := Zielsatz.reachB_ruft P hvoll (reachB_wurzel P fs f) hr
  unfold tor
  cases hgf : reachB P fs g f
  · simp [rangB_lt hvoll hfg hgf]
  · have e : rangB P fs g = rangB P fs f := Nat.le_antisymm (rangB_le hvoll hfg) (rangB_le hvoll hgf)
    simp only [e, Nat.lt_irrefl, decide_false, Bool.false_or, beq_self_eq_true, Bool.true_and]
    simp only [zykS, zyklusMit, hfg, hgf, Bool.and_self, Bool.true_and]
    exact List.any_eq_true.2 ⟨g, hvoll g, by simp [hr, hgf]⟩

/-- A gate that every callee of `f` passes admits `f`'s body. -/
theorem rufeE_aus_ruft (Z : D.Fn → Bool) {f : D.Fn} (hZ : ∀ g, ruftB P f g = true → Z g = true) :
    rufeE Z (fun n => fs.all fun g => !(D.passt g n) || Z g) true (P.rumpf f) = true := by
  rw [rufeE_mE]
  show mE (rufM fs Z) (P.rumpf f) = true
  rw [Gen.rufM_zerlegt fs hvoll]
  apply List.all_eq_true.2
  intro g _
  cases h : ruftB P f g
  · have e := Gen.ruftB_eq P f g
    rw [h] at e
    have hm : mE (Gen.ohneRuf g) (P.rumpf f) = true := by
      cases hm : mE (Gen.ohneRuf g) (P.rumpf f)
      · rw [hm] at e; cases e
      · rfl
    simp [hm]
  · simp [hZ g h]

/-- **THE GATE HOLDS FOR EVERY PROGRAM.** -/
theorem tor_gut (f : D.Fn) :
    rufeE (tor (zykS P fs) (rangB P fs) f) (torS (zykS P fs) (rangB P fs) fs f) true (P.rumpf f) = true :=
  rufeE_aus_ruft hvoll _ fun _ hr => tor_ruft hvoll hr

end Rang

/-! ## 3. Every program terminates under its measure duty -/

section Satz

variable [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
  (m : Mass D) {fs : List D.Fn}

/-- **TERMINATION** (T5, first half): every program whose measures fall where the user's duty says (`MassPflicht`
    for the cycles of `zykS`) and have one length along a cycle: on every infinite GX run from the start, every
    thread takes only finitely many steps. No static premise beyond the measures: the gate holds for every program
    (`tor_gut`). -/
theorem terminierung (Q : AxEns D) (S : SperrInv D) (K : Faden → D.Fn → Bool)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P pa Q S Tg f) (hM : ∀ f, MassPflicht P pa Q S Tg m (zykS P fs) f)
    (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hL : ∀ f g, zykS P fs f g = true → (m f).length = (m g).length)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    ∃ N, ∀ j, N ≤ j → R.akt j ≠ some t :=
  rekursion_endlich_aus m (zykS P fs) (rangB P fs) fs Q S K lok sp init hO hRL hQ hlok hS hvoll hAbg
    hWurzel hTA hTV hTS hTO hFragS hFS hlokK hK hM hStart hsp hex (tor_gut hvoll) hL R h0 t

end Satz

/-! ## 4. The class `endet` keeps its hull free of `forever` -/

section Klasse

variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (mass : D.Fn → Bool)

theorem klasse_foldl (w : D.Fn) : ∀ (l : List D.Fn) (k : TermKlasse),
    k.rang ≤ (l.foldl (fun k g => if reachB P fs w g then k.schwaecher (lokal P fs mass g) else k) k).rang ∧
    ∀ g ∈ l, reachB P fs w g = true →
      (lokal P fs mass g).rang ≤ (l.foldl (fun k g => if reachB P fs w g then k.schwaecher (lokal P fs mass g) else k) k).rang
  | [], _ => ⟨Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, k => by
      simp only [List.foldl_cons]
      have ih := klasse_foldl w l (if reachB P fs w a then k.schwaecher (lokal P fs mass a) else k)
      have hk : k.rang ≤ (if reachB P fs w a then k.schwaecher (lokal P fs mass a) else k).rang := by
        split
        · rw [TermKlasse.schwaecher_rang]; omega
        · exact Nat.le_refl _
      refine ⟨Nat.le_trans hk ih.1, fun g hg hr => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · have : (lokal P fs mass g).rang ≤ (if reachB P fs w g then k.schwaecher (lokal P fs mass g) else k).rang := by
          rw [if_pos hr, TermKlasse.schwaecher_rang]; omega
        exact Nat.le_trans this ih.1
      · exact ih.2 g hg hr

/-- **The class of `w` is the weakest local class of its hull**: `endet` for `w` means `endet` for every function it
    reaches. -/
theorem klasse_endet_lokal {w : D.Fn} (h : klasse P fs mass w = .endet) {g : D.Fn} (hg : g ∈ fs)
    (hr : reachB P fs w g = true) : lokal P fs mass g = .endet := by
  have := (klasse_foldl P fs mass w fs .endet).2 g hg hr
  unfold klasse at h
  rw [h] at this
  apply TermKlasse.rang_inj
  simp only [TermKlasse.rang] at this ⊢
  omega

theorem lokal_endet_ewig {g : D.Fn} (h : lokal P fs mass g = .endet) : (befund P g).ewig = false := by
  unfold lokal at h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h4
  simpa using h4

/-- No function `g` reaches holds a `forever`. -/
def ewigFrei (g : D.Fn) : Bool := fs.all fun h => !(reachB P fs g h) || !(befund P h).ewig

/-- The indirect-call gate of `ewigFrei`. -/
def ewigFreiS (n : Nat) : Bool := fs.all fun g => !(D.passt g n) || ewigFrei P fs g

theorem ewigFrei_klasse (hvoll : ∀ g : D.Fn, g ∈ fs) {w : D.Fn} (h : klasse P fs mass w = .endet) :
    ewigFrei P fs w = true := by
  apply List.all_eq_true.2
  intro g _
  cases hr : reachB P fs w g
  · rfl
  · simp [lokal_endet_ewig P fs mass (klasse_endet_lokal P fs mass h (hvoll g) hr)]

/-- **A `forever`-free hull admits the body under the gate without `forever`.** -/
theorem ewigFrei_rumpf (hvoll : ∀ g : D.Fn, g ∈ fs) {f : D.Fn} (hf : ewigFrei P fs f = true) :
    rufeE (ewigFrei P fs) (ewigFreiS P fs) false (P.rumpf f) = true := by
  have hew : (befE false false (P.rumpf f)).ewig = false := by
    have := List.all_eq_true.mp hf f (hvoll f)
    simpa [reachB_wurzel, befund] using this
  rw [rufeE_ohneEwig _ _ (P.rumpf f) false false hew]
  refine rufeE_aus_ruft hvoll _ fun g hr => List.all_eq_true.2 fun h _ => ?_
  cases hgh : reachB P fs g h
  · rfl
  · have hfg : reachB P fs f g = true := Zielsatz.reachB_ruft P hvoll (reachB_wurzel P fs f) hr
    have := List.all_eq_true.mp hf h (hvoll h)
    simpa [reachB_trans hvoll hfg hgh] using this

end Klasse

/-! ## 5. `endet` never stands at a spent budget -/

section Budget

variable [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
  {fs : List D.Fn}

theorem rufeR_istEwig {Z : D.Fn → Bool} {ZS : Nat → Bool} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {r : GRest D V l Γ Λ} (h : rufeR Z ZS false r = true) : r.istEwig = false := by
  cases r <;> simp_all [rufeR, GRest.istEwig]

/-- The frame's residue admits no `forever`. -/
def EFR (P : Programm D) (fs : List D.Fn) (r : RufRahmenG D) : Prop :=
  rufeR (ewigFrei P fs) (ewigFreiS P fs) false r.rest.2.2.2.2 = true

theorem ewigFrei_schritt (hvoll : ∀ g : D.Fn, g ∈ fs) {M M' : RufMaschineG D} {t : Faden}
    (hs : RufSchrittGX P O pa Tg M t M')
    (hI : ∀ r ∈ (M.faeden t).kopf :: (M.faeden t).stapel, EFR P fs r) :
    ∀ r ∈ (M'.faeden t).kopf :: (M'.faeden t).stapel, EFR P fs r := by
  obtain ⟨σ, M'', hg, _, _, _, hfa, _, _⟩ := hs
  have hfa' : M'.faeden t = M''.faeden t := by rw [hfa]
  rw [hfa']
  have hI' : ∀ r ∈ ((mitSpeicher M σ).faeden t).kopf :: ((mitSpeicher M σ).faeden t).stapel, EFR P fs r := hI
  rcases schrittArt hg (fun _ => 0) (ewigFrei P fs) (ewigFreiS P fs) false with
    ⟨hst, hpot⟩ | ⟨g, caller', rho, s0, hst, hkopf, hpush⟩ | ⟨caller, rst, hst, hst', hpop⟩
  · intro r hr
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hpot (hI' _ List.mem_cons_self)).1
    · exact hI' r (List.mem_cons_of_mem _ hr)
  · obtain ⟨hokc, hdir⟩ := hpush (hI' _ List.mem_cons_self)
    have hgf : ewigFrei P fs g = true := by
      rcases hdir with ⟨hz, _⟩ | ⟨n, hn, hp, _⟩
      · exact hz
      · have := List.all_eq_true.mp hn g (hvoll g)
        simpa [hp] using this
    intro r hr
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · unfold EFR
      rw [hkopf]
      exact ewigFrei_rumpf P fs hvoll hgf
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hokc
      · exact hI' r (List.mem_cons_of_mem _ hr)
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hc : EFR P fs caller := hI' caller (by rw [hst]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      exact (hpop (fun _ => 0) _ _ false).1 hc
    · rw [hst'] at hr
      exact hI' r (by rw [hst]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

/-- **A thread whose start reaches no `forever` never stands at a `forever`**: no frame of it ever holds one, on
    every GX run -- so its head is never a spent budget (`RestHalt .budget` is a head `ewig 0`). -/
theorem ewigFrei_ohne_budget (hvoll : ∀ g : D.Fn, g ∈ fs) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init)
    (t : Faden) (hw : ewigFrei P fs (init t).1 = true) :
    ∀ j, ((R.M j).faeden t).kopf.rest.2.2.2.2.istEwig = false := by
  have hI : ∀ j, ∀ r ∈ ((R.M j).faeden t).kopf :: ((R.M j).faeden t).stapel, EFR P fs r := by
    intro j
    induction j with
    | zero =>
      rw [h0]
      rcases hi : init t with ⟨g, rho⟩
      rw [hi] at hw
      unfold RufStartG
      dsimp only
      rw [hi]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ewigFrei_rumpf P fs hvoll hw
    | succ j ih =>
      cases h : R.akt j with
      | none => rw [R.stotter j h]; exact ih
      | some u =>
        by_cases htu : t = u
        · subst htu
          exact ewigFrei_schritt hvoll (R.schritt j t h) ih
        · rw [Zielsatz.gx_fremd (R.schritt j u h) t htu]; exact ih
  intro j
  exact rufeR_istEwig (hI j _ List.mem_cons_self)

end Budget

/-! ## 6. The class `endet` -/

/-- **T5 -- THE CLASS `endet` MEANS WHAT IT SAYS.** A thread whose start function the algorithm puts in class
    `endet`: on every infinite GX run it takes only finitely many steps, and its head never stands at a `forever` (so
    never at a spent budget) -- its end does not lean on the passes machine G grants. -/
theorem endet_satz [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (m : Mass D) {fs : List D.Fn} (mass : D.Fn → Bool) (Q : AxEns D) (S : SperrInv D) (K : Faden → D.Fn → Bool)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P pa Q S Tg f) (hM : ∀ f, MassPflicht P pa Q S Tg m (zykS P fs) f)
    (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hL : ∀ f g, zykS P fs f g = true → (m f).length = (m g).length)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden)
    (hk : klasse P fs mass (init t).1 = .endet) :
    (∃ N, ∀ j, N ≤ j → R.akt j ≠ some t) ∧ ∀ j, ((R.M j).faeden t).kopf.rest.2.2.2.2.istEwig = false :=
  ⟨terminierung m Q S K lok sp init hO hRL hQ hlok hS hvoll hAbg hWurzel hTA hTV hTS hTO hFragS hFS hlokK hK hM
      hStart hsp hex hL R h0 t,
    ewigFrei_ohne_budget hvoll sp init R h0 t (ewigFrei_klasse P fs mass hvoll hk)⟩

end Gabbro.Grammatik
