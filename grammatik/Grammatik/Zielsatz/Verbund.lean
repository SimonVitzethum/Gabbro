/-
  File:      Grammatik/Zielsatz/Verbund.lean
  Subject:   LINKING SEPARATELY COMPILED UNITS, PROVED (Opus agent E, 2026-09-26):
             `gabbro_ziel_verbund : GabbroZielVerbund` (the statement is Spec.lean's), and the
             link check as ONE Bool, `schnittstelleB`, decided exactly (`schnittstelleB_iff`).

  THE ROUTE. The linked unit `verbinde e E₁ E₂` is an ordinary `Einheit`; the proof shows that
  it meets every premise of `GabbroZiel` and applies `gabbro_ziel` (with the concrete checker
  `akzeptiert_pruefer`). Nothing below the goal theorem is re-proved.
  * (a) `akzeptiertSpec_verbinde`: the per-body components of `AkzeptiertSpec` (fragment,
    lock floors, answer sites, lock-invariant places, roots) are each OWNER's verdict -- a
    body's footprint, fragment and features depend on its own text and the shared contracts
    only (`fussOrteG_teil`, `kandB_teil`, `verbindeP_rumpf`; the congruence of the footprint
    under other bodies, `endblockOrteP_mitRumpf`, is a structural induction over the syntax).
    The closed-graph component comes from each unit's closure and the placeholders being
    leaves (`abg_verbinde`: every edge of an owner's view is an edge of the linked program,
    `kante_teil`, and the linked graph is closed, `reachB_ruft` -- the fixpoint of
    `erreichB` is reached within `fs.length` rounds, `erreichB_stabil`, a counting argument).
    The three whole-program components (thread-locality, write separation, pool safety) are
    the link check's, over the COMPOSED hulls: the linked graph of a root lies in its composed
    hull (`huelle_of_reach`, from `KeinRueckruf`).
  * (b) `nutzerPflicht_verbinde`: the linked user duty is the two units' duties over the bodies
    they own (`koerper_mitRumpf2` and its two siblings: a body triple depends on its own body
    and the contracts only), the start obligation per unit over the shared initial memory.
  * (c) the hardware premise of the linked unit IS unit 1's; `E₂.Q = E₁.Q` makes it unit 2's.
  * (d) is the linked runtime's, a premise.

  What the proof does NOT use: the units' own footprint, race and pool components
  (`fuss`, `renn`, `einzeln` of `AkzeptiertSpec`) -- the link re-decides those three over the
  composed hulls, because a unit alone cannot see the other unit's threads nor the reads
  hidden behind an imported head.

  Witnesses: Zielsatz/VerbundZeuge.lean.
-/
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

section Kongruenz
variable (P : Programm D)
  (r : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))

mutual
theorem stmtOrteP_mitRumpf {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), stmtOrteP (mitRumpf P r) s = stmtOrteP P s
  | _, _, _, _, .assignSlot _ _ _ _ _ _ => rfl
  | _, _, _, _, .assignDurch _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .assignGlob _ _ _ _ => rfl
  | _, _, _, _, .schreibBytes _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .assignVar _ _ => rfl
  | _, _, _, _, .uebergang _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .ite c t e => by
      simp only [stmtOrteP, blockOrteP_mitRumpf t, blockOrteP_mitRumpf e]
  | _, _, _, _, .onOption o p a => by
      simp only [stmtOrteP, blockOrteP_mitRumpf p, blockOrteP_mitRumpf a]
  | _, _, _, _, .onTag v arms => by simp only [stmtOrteP, armsOrteP_mitRumpf arms]
  | _, _, _, _, .onGrund r' arms => by simp only [stmtOrteP, grundArmsOrteP_mitRumpf arms]
  | _, _, _, _, .call _ _ _ _ => rfl
  | _, _, _, _, .callInd _ _ _ _ => rfl
  | _, _, _, _, .locks _ _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .breaking _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .traverse _ _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .retry _ _ body ueber => by
      simp only [stmtOrteP, blockOrteP_mitRumpf body, blockOrteP_mitRumpf ueber]
  | _, _, _, _, .forever _ _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .axiomCall _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .regSchreib _ _ _ => rfl
  | _, _, _, _, .transition _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .publish _ _ _ _ _ _ => rfl
  | _, _, _, _, .advances _ _ _ _ => rfl
  | _, _, _, _, .retires _ _ _ _ => rfl
  | _, _, _, _, .ret _ _ => rfl
  | _, _, _, _, .retGrund _ _ => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem blockOrteP_mitRumpf {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), blockOrteP (mitRumpf P r) b = blockOrteP P b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => by
      simp only [blockOrteP, stmtOrteP_mitRumpf s, blockOrteP_mitRumpf rest]
  | _, _, _, _, .bind _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .bindCall _ _ _ _ _ rest => by
      simp only [blockOrteP, blockOrteP_mitRumpf rest]; rfl
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf err, blockOrteP_mitRumpf rest]; rfl
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .regLies _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .regLiesElse _ _ _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]
  | _, _, _, _, .awaits _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .exchange _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .narrow _ _ _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]
  | _, _, _, _, .pruefung _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]
  | _, _, _, _, .gleit _ _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .gleitLit _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .gleitVon _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .gleitNarrow _ _ _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]

theorem endblockOrteP_mitRumpf {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), endblockOrteP (mitRumpf P r) e = endblockOrteP P e
  | _, _, _, .ret _ _ => rfl
  | _, _, _, .retGrund _ _ => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => by
      simp only [endblockOrteP, stmtOrteP_mitRumpf s, endblockOrteP_mitRumpf rest]
  | _, _, _, .bind _ rest => by simp only [endblockOrteP, endblockOrteP_mitRumpf rest]

theorem armsOrteP_mitRumpf {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (a : Arms D V l Γ Λ Λ' cs),
    armsOrteP (mitRumpf P r) a = armsOrteP P a
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => by
      simp only [armsOrteP, blockOrteP_mitRumpf b, armsOrteP_mitRumpf rest]

theorem grundArmsOrteP_mitRumpf {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (a : GrundArms D V l Γ Λ Λ' n),
    grundArmsOrteP (mitRumpf P r) a = grundArmsOrteP P a
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => by
      simp only [grundArmsOrteP, blockOrteP_mitRumpf b, grundArmsOrteP_mitRumpf rest]
end

theorem fussOrteG_mitRumpf (f : D.Fn) (h : r f = P.rumpf f) :
    fussOrteG (mitRumpf P r) f = fussOrteG P f := by
  unfold fussOrteG fussOrte
  have e : (mitRumpf P r).rumpf f = P.rumpf f := h
  rw [e, endblockOrteP_mitRumpf]
  rfl

end Kongruenz

/-! ## Closure of the computed call graph -/

section Erreich

variable [DecidableEq D.Fn]

theorem erreichB_mono_n (P : Programm D) (fs : List D.Fn) (w : D.Fn) (n : Nat) (g : D.Fn)
    (h : erreichB P fs w n g = true) : erreichB P fs w (n + 1) g = true := by
  show erreichSchritt P fs (erreichB P fs w n) g = true
  simp [erreichSchritt, h]

theorem countP_lt_of {α : Type} (p q : α → Bool) : ∀ (l : List α), (∀ x, p x = true → q x = true) →
    (∃ x ∈ l, q x = true ∧ p x = false) → l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, hpq, ⟨x, hx, hq, hp⟩ => by
      simp only [List.countP_cons]
      have hle : l.countP p ≤ l.countP q := List.countP_mono_left (fun y _ hy => hpq y hy)
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp only [hq, hp, Bool.false_eq_true, ↓reduceIte]
        omega
      · have hlt := countP_lt_of p q l hpq ⟨x, hx', hq, hp⟩
        cases ha : p a
        · cases hb : q a <;> simp <;> omega
        · simp [hpq a ha]
          omega

theorem erreichB_stabil (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (w : D.Fn) : erreichB P fs w (fs.length + 1) = erreichB P fs w fs.length := by
  have hmono := erreichB_mono_n P fs w
  have hstab : ∀ m, erreichB P fs w (m + 1) = erreichB P fs w m →
      ∀ k, erreichB P fs w (m + k + 1) = erreichB P fs w (m + k) := by
    intro m hm k
    induction k with
    | zero => simpa using hm
    | succ k ih =>
        show erreichSchritt P fs (erreichB P fs w (m + k + 1)) =
          erreichSchritt P fs (erreichB P fs w (m + k))
        rw [ih]
  have hcnt : ∀ n, (∀ m, m < n → erreichB P fs w (m + 1) ≠ erreichB P fs w m) →
      n + 1 ≤ fs.countP (erreichB P fs w n) := by
    intro n
    induction n with
    | zero =>
        intro _
        have h0 : erreichB P fs w 0 w = true := by simp [erreichB]
        have : 0 < fs.countP (erreichB P fs w 0) := List.countP_pos_iff.mpr ⟨w, hvoll w, h0⟩
        omega
    | succ n ih =>
        intro h
        have h1 := ih (fun m hm => h m (by omega))
        have hne := h n (by omega)
        have hex : ∃ g, erreichB P fs w (n + 1) g = true ∧ erreichB P fs w n g = false := by
          refine Classical.byContradiction fun hc => hne (funext fun g => ?_)
          cases h1 : erreichB P fs w n g
          · cases h2 : erreichB P fs w (n + 1) g
            · rfl
            · exact absurd ⟨g, h2, h1⟩ hc
          · exact hmono n g h1
        obtain ⟨g, hg1, hg0⟩ := hex
        have := countP_lt_of (erreichB P fs w n) (erreichB P fs w (n + 1)) fs (hmono n)
          ⟨g, hvoll g, hg1, hg0⟩
        omega
  by_cases hall : ∀ m, m < fs.length → erreichB P fs w (m + 1) ≠ erreichB P fs w m
  · have h1 := hcnt fs.length hall
    have h2 : fs.countP (erreichB P fs w fs.length) ≤ fs.length := List.countP_le_length
    omega
  · have hex : ∃ m, m < fs.length ∧ erreichB P fs w (m + 1) = erreichB P fs w m :=
      Classical.byContradiction fun hc => hall fun m hm he => hc ⟨m, hm, he⟩
    obtain ⟨m, hm, he⟩ := hex
    have := hstab m he (fs.length - m)
    have e : m + (fs.length - m) = fs.length := by omega
    rw [e] at this
    exact this

/-- **The computed call graph is closed** (given a complete member list). -/
theorem reachB_ruft (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {w f g : D.Fn} (hf : reachB P fs w f = true) (hr : ruftB P f g = true) :
    reachB P fs w g = true := by
  unfold reachB at *
  rw [← erreichB_stabil P hvoll w]
  show erreichSchritt P fs (erreichB P fs w fs.length) g = true
  simp only [erreichSchritt, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact Or.inr ⟨f, hvoll f, hf, hr⟩

/-- Every set containing the root and closed under calls contains the computed graph. -/
theorem reachB_in (P : Programm D) (fs : List D.Fn) {Z : D.Fn → Prop} {w : D.Fn} (h0 : Z w)
    (hz : ∀ h g, Z h → ruftB P h g = true → Z g) : ∀ g, reachB P fs w g = true → Z g := by
  unfold reachB
  generalize fs.length = n
  induction n with
  | zero =>
      intro g hg
      have : g = w := by simpa [erreichB] using hg
      subst this
      exact h0
  | succ n ih =>
      intro g hg
      change erreichSchritt P fs (erreichB P fs w n) g = true at hg
      simp only [erreichSchritt, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hg
      rcases hg with hg | ⟨h, _, hh, hr⟩
      · exact ih g hg
      · exact hz h g (ih h hh) hr

/-- A graph whose edges are edges of `P'` lies in every closed `P'`-graph containing its root. -/
theorem reachB_teil {P P' : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hk : ∀ h g, ruftB P h g = true → ruftB P' h g = true) {w w' : D.Fn}
    (hw : reachB P' fs w' w = true) : ∀ g, reachB P fs w g = true → reachB P' fs w' g = true :=
  reachB_in P fs hw fun h g hh hr => reachB_ruft P' hvoll hh (hk h g hr)

end Erreich

end Gabbro.Grammatik.Zielsatz


namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

section Kongruenz2
variable (P : Programm D)

theorem fussOrte_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (f : D.Fn) (h : r f = r' f) : fussOrte (mitRumpf P r) f = fussOrte (mitRumpf P r') f := by
  unfold fussOrte
  have e1 : (mitRumpf P r).rumpf f = r f := rfl
  have e2 : (mitRumpf P r').rumpf f = r' f := rfl
  rw [e1, e2, endblockOrteP_mitRumpf, endblockOrteP_mitRumpf, h]
  rfl

theorem fussOrteG_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (f : D.Fn) (h : r f = r' f) : fussOrteG (mitRumpf P r) f = fussOrteG (mitRumpf P r') f := by
  unfold fussOrteG
  rw [fussOrte_mitRumpf2 P r r' f h]
  have e1 : (mitRumpf P r).rumpf f = r f := rfl
  have e2 : (mitRumpf P r').rumpf f = r' f := rfl
  rw [e1, e2, h]

theorem koerper_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) (h : r f = r' f) :
    KoerperGutS (mitRumpf P r) passes Q S f ↔ KoerperGutS (mitRumpf P r') passes Q S f := by
  unfold KoerperGutS
  have e : (mitRumpf P r).rumpf f = (mitRumpf P r').rumpf f := h
  rw [e]
  exact Iff.rfl

theorem invGutS_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) (h : r f = r' f) :
    InvGutS (mitRumpf P r) passes Q S f ↔ InvGutS (mitRumpf P r') passes Q S f := by
  unfold InvGutS
  have e : (mitRumpf P r).rumpf f = (mitRumpf P r').rumpf f := h
  rw [e]
  exact Iff.rfl

theorem invGutGrund_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) (h : r f = r' f) :
    InvGutGrund (mitRumpf P r) passes Q S f ↔ InvGutGrund (mitRumpf P r') passes Q S f := by
  unfold InvGutGrund
  have e : (mitRumpf P r).rumpf f = (mitRumpf P r').rumpf f := h
  rw [e]
  exact Iff.rfl

end Kongruenz2

section Verbund

variable [DecidableEq D.Fn] {E₁ E₂ : Einheit D} {e : D.Fn → Bool}

omit [DecidableEq D.Fn] in
/-- Under a shared link declaration the second unit's program is the first one's contracts
    with the second one's bodies. -/
theorem p2_eq (hV : Verbindbar E₁ E₂) : E₂.P = mitRumpf E₁.P E₂.P.rumpf := by
  unfold mitRumpf
  rw [hV.invariante, hV.requires, hV.ensures]

omit [DecidableEq D.Fn] in
theorem verbindeP_rumpf (f : D.Fn) :
    (verbindeP e E₁ E₂).rumpf f = (teilP e E₁ E₂ f).rumpf f := by
  show (if e f then E₁.P.rumpf f else E₂.P.rumpf f) = (if e f then E₁.P else E₂.P).rumpf f
  cases e f <;> rfl

omit [DecidableEq D.Fn] in
theorem teilP_gleich {f g : D.Fn} (h : e f = e g) : teilP e E₁ E₂ f = teilP e E₁ E₂ g := by
  unfold teilP
  rw [h]

theorem teilP_teil (hV : Verbindbar E₁ E₂) (f : D.Fn) :
    teilP e E₁ E₂ f = mitRumpf E₁.P (teilP e E₁ E₂ f).rumpf := by
  unfold teilP
  cases e f
  · exact p2_eq hV
  · rfl

theorem fussOrteG_teil (hV : Verbindbar E₁ E₂) (f : D.Fn) :
    fussOrteG (verbindeP e E₁ E₂) f = fussOrteG (teilP e E₁ E₂ f) f := by
  conv => rhs; rw [teilP_teil hV f]
  exact fussOrteG_mitRumpf2 E₁.P _ _ f (verbindeP_rumpf f)

theorem fussOrte_teil (hV : Verbindbar E₁ E₂) (f : D.Fn) :
    fussOrte (verbindeP e E₁ E₂) f = fussOrte (teilP e E₁ E₂ f) f := by
  conv => rhs; rw [teilP_teil hV f]
  exact fussOrte_mitRumpf2 E₁.P _ _ f (verbindeP_rumpf f)

theorem kandB_teil (hV : Verbindbar E₁ E₂) (fs : List D.Fn) (f : D.Fn) :
    kandB (verbindeP e E₁ E₂) fs = kandB (teilP e E₁ E₂ f) fs := by
  rw [teilP_teil hV f]
  rfl

theorem ruftB_teil (h g : D.Fn) :
    ruftB (verbindeP e E₁ E₂) h g = ruftB (teilP e E₁ E₂ h) h g := by
  unfold ruftB
  rw [verbindeP_rumpf]

/-- **The linked call graph of a root lies in its composed hull** (`HuelleV`): no callback. -/
theorem huelle_of_reach {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hNC : KeinRueckruf fs e E₁ E₂) (w : D.Fn) :
    ∀ h, reachB (verbindeP e E₁ E₂) fs w h = true → HuelleV fs e E₁ E₂ w h := by
  refine reachB_in _ fs (Or.inl ⟨rfl, reachB_wurzel _ fs w⟩) ?_
  intro h g hh hr
  rw [ruftB_teil] at hr
  rcases hh with ⟨heh, hwh⟩ | ⟨f, hne, heh, hwf, hfh⟩
  · rw [teilP_gleich heh] at hr
    have hwg := reachB_ruft _ hvoll hwh hr
    by_cases hg : e g = e w
    · exact Or.inl ⟨hg, hwg⟩
    · exact Or.inr ⟨g, hg, rfl, hwg, reachB_wurzel _ fs g⟩
  · rw [teilP_gleich heh] at hr
    have hfg := reachB_ruft _ hvoll hfh hr
    exact Or.inr ⟨f, hne, hNC w f g hne hwf hfg, hwf, hfg⟩

theorem teil_abg {fs : List D.Fn}
    (hA₁ : ∀ w, AbgK E₁.P fs (reachB E₁.P fs w)) (hA₂ : ∀ w, AbgK E₂.P fs (reachB E₂.P fs w))
    (f : D.Fn) : ∀ w, AbgK (teilP e E₁ E₂ f) fs (reachB (teilP e E₁ E₂ f) fs w) := by
  unfold teilP
  cases e f
  · exact hA₂
  · exact hA₁

/-- Every edge of the owner's view of `f` is an edge of the linked program (placeholders are
    leaves). -/
theorem kante_teil (hB₁ : Platzhalter e E₁.P) (hB₂ : Platzhalter (fun f => !e f) E₂.P)
    (f h g : D.Fn) (hr : ruftB (teilP e E₁ E₂ f) h g = true) :
    ruftB (verbindeP e E₁ E₂) h g = true := by
  rw [ruftB_teil]
  by_cases heh : e h = e f
  · rw [teilP_gleich heh]
    exact hr
  · exfalso
    unfold teilP at hr
    cases hf : e f
    · rw [hf] at heh hr
      have : e h = true := by cases h' : e h; exact absurd h' heh; rfl
      have := hB₂ h g (by simp [this])
      simp only [Bool.false_eq_true, ↓reduceIte] at hr
      rw [this] at hr
      cases hr
    · rw [hf] at heh hr
      have : e h = false := by cases h' : e h; rfl; exact absurd h' heh
      have := hB₁ h g this
      simp only [↓reduceIte] at hr
      rw [this] at hr
      cases hr

omit [DecidableEq D.Fn] in
theorem mle_rufM {fs : List D.Fn} {Z Z' : D.Fn → Bool} (h : ∀ g, Z g = true → Z' g = true) :
    MLe (rufM fs Z) (rufM fs Z') := by
  refine ⟨fun g hg => h g hg, fun n hn => ?_, fun _ _ => rfl⟩
  refine List.all_eq_true.mpr fun g hg => ?_
  have h1 := List.all_eq_true.mp hn g hg
  simp only [Bool.or_eq_true] at h1 ⊢
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h g h1)

/-- **The linked call graphs are closed.** -/
theorem abg_verbinde {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA₁ : ∀ w, AbgK E₁.P fs (reachB E₁.P fs w)) (hA₂ : ∀ w, AbgK E₂.P fs (reachB E₂.P fs w))
    (hB₁ : Platzhalter e E₁.P) (hB₂ : Platzhalter (fun f => !e f) E₂.P) :
    ∀ w, AbgK (verbindeP e E₁ E₂) fs (reachB (verbindeP e E₁ E₂) fs w) := by
  intro w f hf
  have hu := teil_abg (e := e) hA₁ hA₂ f f f (reachB_wurzel _ fs f)
  have hsub : ∀ g, reachB (teilP e E₁ E₂ f) fs f g = true →
      reachB (verbindeP e E₁ E₂) fs w g = true :=
    reachB_teil hvoll (kante_teil hB₁ hB₂ f) hf
  rw [verbindeP_rumpf]
  exact mE_mono (mle_rufM hsub) _ hu

omit [DecidableEq D.Fn] in
theorem mem_ws_verbinde {w : D.Fn} (h : w ∈ (verbinde e E₁ E₂).ws) : w ∈ E₁.ws ∨ w ∈ E₂.ws := by
  simp only [Einheit.ws, verbinde, List.map_append, List.mem_append] at h ⊢
  rcases h with ((h | h) | (h | h)) | (h | h)
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inr (Or.inl (Or.inr h))

/-- **The linked unit is accepted**: the per-unit verdicts carry every per-body component,
    the link check carries the three whole-program components over the composed hulls. -/
theorem akzeptiertSpec_verbinde {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA₁ : AkzeptiertSpec E₁.P E₁.S fs E₁.ws) (hA₂ : AkzeptiertSpec E₂.P E₂.S fs E₂.ws)
    (hV : Verbindbar E₁ E₂) (hS : SchnittstelleSpec fs e E₁ E₂) :
    AkzeptiertSpec (verbinde e E₁ E₂).P (verbinde e E₁ E₂).S fs (verbinde e E₁ E₂).ws := by
  have hH := huelle_of_reach (e := e) (E₁ := E₁) (E₂ := E₂) hvoll hS.keinRueckruf
  have hfrag : ∀ f, ((teilP e E₁ E₂ f).rumpf f).gOk
      (kandB (teilP e E₁ E₂ f) fs (fussOrteG (teilP e E₁ E₂ f) f)) (fun _ => true) = true := by
    intro f
    unfold teilP
    cases e f
    · exact List.all_eq_true.mp hA₂.frag f (hvoll f)
    · exact List.all_eq_true.mp hA₁.frag f (hvoll f)
  have hGetrennt : ∀ c, LokBedarf e E₁ E₂ c →
      Getrennt (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c := by
    intro c hc w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
    refine hS.lok c hc w₁ hw₁ w₂ hw₂ hne f g (hH w₁ f hf) ?_ (hH w₂ g hg)
    rw [← fussOrteG_teil hV]
    exact hcf
  refine ⟨?_, abg_verbinde hvoll hA₁.abg hA₂.abg hS.blatt₁ hS.blatt₂, ?_, ?_, hA₁.sperrOrte,
    ?_, ?_, ?_, ?_⟩
  · -- frag
    refine List.all_eq_true.mpr fun f _ => ?_
    show ((verbindeP e E₁ E₂).rumpf f).gOk
      (kandB (verbindeP e E₁ E₂) fs (fussOrteG (verbindeP e E₁ E₂) f)) (fun _ => true) = true
    rw [verbindeP_rumpf, kandB_teil hV fs f, fussOrteG_teil hV]
    exact hfrag f
  · -- fuss
    intro f
    have hlok : ∀ c, LokBedarf e E₁ E₂ c → lokW (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c = true :=
      fun c hc => @decide_eq_true _ (Classical.propDecidable _) (hGetrennt c hc)
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have hc' : c ∈ fussOrte (teilP e E₁ E₂ f) f := by
        rw [← fussOrte_teil hV]
        exact hc
      by_cases hs : sigB f c = true
      · exact Or.inl (by rw [hs, Bool.true_or])
      · by_cases hg : ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L
        · exact Or.inr hg
        · refine Or.inl ?_
          rw [hlok c ⟨f, Or.inl ⟨hc', by simpa using hs, hg⟩⟩, Bool.or_true]
    · have hc' : c ∈ ((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger := by
        rw [← verbindeP_rumpf]
        exact hc
      by_cases hs : sigB f c = true
      · rw [hs, Bool.true_or]
      · rw [hlok c ⟨f, Or.inr ⟨hc', by simpa using hs⟩⟩, Bool.or_true]
  · -- stufen
    intro f
    show Grammatik.mE (bodenM f) ((verbindeP e E₁ E₂).rumpf f) = true
    rw [verbindeP_rumpf]
    unfold teilP
    cases e f
    · exact hA₂.stufen f
    · exact hA₁.stufen f
  · -- wurzeln
    intro w hw
    rcases mem_ws_verbinde hw with h | h
    · exact hA₁.wurzeln w h
    · exact hA₂.wurzeln w h
  · -- einzeln
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hS.einzeln w hw
    exact ⟨h1, h2, fun f hf c hc => h3 f (hH w f hf) c hc⟩
  · -- renn
    intro c hB hAt w₁ hw₁ w₂ hw₂ hne g hg hgc h hh
    have := hS.renn c hB hAt w₁ hw₁ w₂ hw₂ hne g (hH w₁ g hg) hgc h (hH w₂ h hh)
    have e' : fussOrteG (verbinde e E₁ E₂).P h = fussOrteG (teilP e E₁ E₂ h) h := fussOrteG_teil hV h
    rw [e']
    exact this
  · -- antworten
    intro f x hx
    change x ∈ ((verbindeP e E₁ E₂).rumpf f).ants at hx
    rw [verbindeP_rumpf] at hx
    unfold teilP at hx
    cases hf : e f
    · rw [hf] at hx
      exact hA₂.antworten f x hx
    · rw [hf] at hx
      exact hA₁.antworten f x hx

/-- **The user's duty of the linked unit is the two units' duties.** -/
theorem nutzerPflicht_verbinde (hV : Verbindbar E₁ E₂) (hQ : E₂.Q = E₁.Q)
    (hN₁ : NutzerTeil e E₁) (hN₂ : NutzerTeil (fun f => !e f) E₂) :
    NutzerPflicht (verbinde e E₁ E₂) := by
  have hS : E₂.S = E₁.S := hV.sperren.symm
  refine ⟨⟨fun passes f => ?_, hN₁.logik.2.1, hN₁.logik.2.2⟩, ⟨hN₁.start.sperren, ?_⟩⟩
  · show KoerperGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutGrund (verbindeP e E₁ E₂) passes E₁.Q E₁.S f
    cases hf : e f
    · obtain ⟨k, i, g⟩ := hN₂.logik.1 passes f (by simp [hf])
      rw [p2_eq hV, hQ, hS] at k i g
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₂.P.rumpf f := by
        simp [hf]
      exact ⟨(koerper_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr g⟩
    · obtain ⟨k, i, g⟩ := hN₁.logik.1 passes f hf
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₁.P.rumpf f := by
        simp [hf]
      exact ⟨(koerper_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr g⟩
  · intro a ha
    show ReqAmEintritt E₁.P a.1 (E₁.sp0.welt []) a.2
    simp only [verbinde, List.mem_append] at ha
    rcases ha with (h | h) | (h | h)
    · exact hN₁.start.req a (List.mem_append_left _ h)
    · have := hN₂.start.req a (List.mem_append_left _ h)
      unfold ReqAmEintritt at this ⊢
      rw [hV.requires, hV.speicher]
      exact this
    · exact hN₁.start.req a (List.mem_append_right _ h)
    · have := hN₂.start.req a (List.mem_append_right _ h)
      unfold ReqAmEintritt at this ⊢
      rw [hV.requires, hV.speicher]
      exact this

end Verbund

/-- **LINKING, PROVED.** -/
theorem gabbro_ziel_verbund : GabbroZielVerbund := by
  intro C D _ E₁ E₂ e fs ls cs h₁ h₂ hV hS hN₁ hN₂ hQ O hH passes sp init hL lebt0 K hK
  have hA := akzeptiertSpec_verbinde fs.2 (C.korrekt E₁ fs ls cs h₁) (C.korrekt E₂ fs ls cs h₂)
    hV hS
  have hB : akzeptiert_pruefer.akzeptiert (verbinde e E₁ E₂) fs.1 ls.1 cs.1 = true :=
    (akzeptiert_iff fs.2 ls.2 cs.2).mpr hA
  exact gabbro_ziel akzeptiert_pruefer D (verbinde e E₁ E₂) fs ls cs hB
    (nutzerPflicht_verbinde hV hQ hN₁ hN₂) O hH passes sp init hL lebt0 K hK


end Gabbro.Grammatik.Zielsatz


namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

/-! ## The link check as ONE Bool -/

section Bool

variable [DecidableEq D.Fn]

/-- `Platzhalter`, decided: every function the unit does not own calls nothing. -/
def platzhalterB (fs : List D.Fn) (eigen : D.Fn → Bool) (P : Programm D) : Bool :=
  fs.all fun f => eigen f || fs.all fun g => !ruftB P f g

/-- `HuelleV`, decided. -/
def huelleB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (w h : D.Fn) : Bool :=
  (decide (e h = e w) && reachB (teilP e E₁ E₂ w) fs w h) ||
  fs.any fun f => !decide (e f = e w) && decide (e h = e f) &&
    reachB (teilP e E₁ E₂ w) fs w f && reachB (teilP e E₁ E₂ f) fs f h

/-- `KeinRueckruf`, decided. -/
def keinRueckrufB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Bool :=
  fs.all fun w => fs.all fun f => fs.all fun h =>
    !(!decide (e f = e w) && reachB (teilP e E₁ E₂ w) fs w f &&
      reachB (teilP e E₁ E₂ f) fs f h) || decide (e h = e f)

/-- `LokBedarf`, decided. -/
def lokBedarfB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (c : D.Tab ⊕ D.Glob) :
    Bool :=
  fs.any fun f =>
    (istIn (fussOrte (teilP e E₁ E₂ f) f) c && !sigB f c &&
      !((waechterVon c).any fun L => istIn (E₁.S.orte L) c)) ||
    (istIn (((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger) c && !sigB f c)

/-- `GetrenntV`, decided. -/
def getrenntVB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w₁ => ws.all fun w₂ => (decide (w₁ = w₂) && !(mehrfachB ws w₁)) ||
    (fs.all fun f => !(huelleB fs e E₁ E₂ w₁ f) || !(istIn (fussOrteG (teilP e E₁ E₂ f) f) c)) ||
    (fs.all fun g => !(huelleB fs e E₁ E₂ w₂ g) || !(TraegerSchreibt g c))

/-- `SchreibGetrenntV`, decided. -/
def schreibGetrenntVB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w₁ => ws.all fun w₂ => decide (w₁ = w₂) ||
    (fs.all fun g => !(huelleB fs e E₁ E₂ w₁ g) || !(TraegerSchreibt g c)) ||
    (fs.all fun h => !(huelleB fs e E₁ E₂ w₂ h) ||
      (!(TraegerSchreibt h c) && !(istIn (fussOrteG (teilP e E₁ E₂ h) h) c)))

/-- `PoolSicherV`, decided over the carrier list `cs`. -/
def poolSicherVB (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (e : D.Fn → Bool)
    (E₁ E₂ : Einheit D) (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && decide (D.gruende w = 0) && fs.all fun f =>
    !(huelleB fs e E₁ E₂ w f) ||
      (cs.all fun c => !(TraegerSchreibt f c) || (!(waechterVon c).isEmpty || atomarB c))

/-- **THE LINK CHECK** (`SchnittstelleSpec`, decided): placeholders are leaves, no callback
    through an imported function, and thread-locality, write separation and pool safety over
    the COMPOSED hulls. -/
def schnittstelleB (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (e : D.Fn → Bool)
    (E₁ E₂ : Einheit D) : Bool :=
  platzhalterB fs e E₁.P && platzhalterB fs (fun f => !e f) E₂.P && keinRueckrufB fs e E₁ E₂ &&
    (cs.all fun c => !(lokBedarfB fs e E₁ E₂ c) || getrenntVB fs e E₁ E₂ (verbinde e E₁ E₂).ws c) &&
    (cs.all fun c => ausgenommenB c || schreibGetrenntVB fs e E₁ E₂ (verbinde e E₁ E₂).ws c) &&
    ((verbinde e E₁ E₂).ws.all fun w =>
      !(mehrfachB (verbinde e E₁ E₂).ws w) || poolSicherVB fs cs e E₁ E₂ w)

variable {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} {e : D.Fn → Bool} {E₁ E₂ : Einheit D}

theorem platzhalterB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {eigen : D.Fn → Bool} {P : Programm D} :
    platzhalterB fs eigen P = true ↔ Platzhalter eigen P := by
  unfold platzhalterB Platzhalter
  constructor
  · intro h f g hf
    have h1 := List.all_eq_true.mp h f (hvoll f)
    rw [hf, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 g (hvoll g)
    simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun f _ => ?_
    cases hf : eigen f
    · rw [Bool.false_or]
      exact List.all_eq_true.mpr fun g _ => by simp [h f g hf]
    · rfl

theorem huelleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {w h : D.Fn} :
    huelleB fs e E₁ E₂ w h = true ↔ HuelleV fs e E₁ E₂ w h := by
  unfold huelleB HuelleV
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨f, _, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨f, h1, h2, h3, h4⟩
  · rintro (⟨h1, h2⟩ | ⟨f, h1, h2, h3, h4⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨f, hvoll f, ⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem keinRueckrufB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    keinRueckrufB fs e E₁ E₂ = true ↔ KeinRueckruf fs e E₁ E₂ := by
  unfold keinRueckrufB KeinRueckruf
  constructor
  · intro h w f g hne hwf hfg
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h w (hvoll w)) f
      (hvoll f)) g (hvoll g)
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
      Bool.not_eq_false'] at h1
    rcases h1 with ((h1 | h1) | h1) | h1
    · exact absurd h1 hne
    · rw [hwf] at h1; cases h1
    · rw [hfg] at h1; cases h1
    · exact h1
  · intro h
    refine List.all_eq_true.mpr fun w _ => List.all_eq_true.mpr fun f _ =>
      List.all_eq_true.mpr fun g _ => ?_
    by_cases hne : e f = e w
    · simp [hne]
    · cases hwf : reachB (teilP e E₁ E₂ w) fs w f
      · simp
      · cases hfg : reachB (teilP e E₁ E₂ f) fs f g
        · simp
        · simp [h w f g hne hwf hfg]

theorem lokBedarfB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {c : D.Tab ⊕ D.Glob} :
    lokBedarfB fs e E₁ E₂ c = true ↔ LokBedarf e E₁ E₂ c := by
  unfold lokBedarfB LokBedarf
  have hW : ((waechterVon c).any fun L => istIn (E₁.S.orte L) c) = true ↔
      ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨L, hL, hi⟩
      exact ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hi⟩
    · rintro ⟨L, hL, hi⟩
      exact ⟨L, waechterVon_mem.mpr hL, istIn_iff.mpr hi⟩
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, _, hf⟩
    refine ⟨f, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hf
    rcases hf with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨istIn_iff.mp h1, h2, fun hx => ?_⟩
      rw [hW.mpr hx] at h3
      cases h3
    · exact Or.inr ⟨istIn_iff.mp h1, h2⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, hvoll f, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    rcases hf with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨⟨istIn_iff.mpr h1, h2⟩, ?_⟩
      cases hx : ((waechterVon c).any fun L => istIn (E₁.S.orte L) c)
      · rfl
      · exact absurd (hW.mp hx) h3
    · exact Or.inr ⟨istIn_iff.mpr h1, h2⟩

theorem getrenntVB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {ws : List D.Fn} {c : D.Tab ⊕ D.Glob} :
    getrenntVB fs e E₁ E₂ ws c = true ↔ GetrenntV fs e E₁ E₂ ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne f g hf hc hg
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    rcases h1 with (h1 | h1) | h1
    · rcases hne with hne | hne
      · exact absurd h1.1 hne
      · rw [mehrfachB_iff.mpr hne] at h1
        cases h1.2
    · have h2 := (List.all_eq_true.mp h1) f (hvoll f)
      rw [(huelleB_iff hvoll).mpr hf, istIn_iff.mpr hc] at h2
      simp at h2
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [(huelleB_iff hvoll).mpr hg] at h2
      simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2 ∧ mehrfachB ws w1 = false
    · obtain ⟨rfl, hm⟩ := hne
      simp [hm]
    have hne' : w1 ≠ w2 ∨ Mehrfach ws w1 := by
      by_cases he : w1 = w2
      · refine Or.inr (mehrfachB_iff.mp ?_)
        cases hm : mehrfachB ws w1
        · exact absurd ⟨he, hm⟩ hne
        · rfl
      · exact Or.inl he
    by_cases hfr : (fs.all fun f => !(huelleB fs e E₁ E₂ w1 f) ||
        !(istIn (fussOrteG (teilP e E₁ E₂ f) f) c)) = true
    · simp [hfr]
    · have hex : ∃ f, HuelleV fs e E₁ E₂ w1 f ∧ c ∈ fussOrteG (teilP e E₁ E₂ f) f := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun f _ => ?_)
        cases hr : huelleB fs e E₁ E₂ w1 f
        · rfl
        · cases hi : istIn (fussOrteG (teilP e E₁ E₂ f) f) c
          · rfl
          · exact absurd ⟨f, (huelleB_iff hvoll).mp hr, istIn_iff.mp hi⟩ hn
      obtain ⟨f, hf, hc⟩ := hex
      have hw : (fs.all fun g => !(huelleB fs e E₁ E₂ w2 g) || !(TraegerSchreibt g c)) = true :=
        List.all_eq_true.mpr fun g _ => by
          cases hg : huelleB fs e E₁ E₂ w2 g
          · rfl
          · simp [h w1 hw1 w2 hw2 hne' f g hf hc ((huelleB_iff hvoll).mp hg)]
      simp [hw]

theorem schreibGetrenntVB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {ws : List D.Fn}
    {c : D.Tab ⊕ D.Glob} :
    schreibGetrenntVB fs e E₁ E₂ ws c = true ↔ SchreibGetrenntV fs e E₁ E₂ ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne g hg hgc k hk
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with (h1 | h1) | h1
    · exact absurd h1 hne
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [(huelleB_iff hvoll).mpr hg, hgc] at h2
      simp at h2
    · have h2 := (List.all_eq_true.mp h1) k (hvoll k)
      rw [(huelleB_iff hvoll).mpr hk] at h2
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h2
      refine ⟨h2.1, fun hc => ?_⟩
      rw [istIn_iff.mpr hc] at h2
      cases h2.2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2
    · simp [hne]
    by_cases hfr : (fs.all fun g => !(huelleB fs e E₁ E₂ w1 g) || !(TraegerSchreibt g c)) = true
    · simp [hfr]
    · have hex : ∃ g, HuelleV fs e E₁ E₂ w1 g ∧ TraegerSchreibt g c = true := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun g _ => ?_)
        cases hr : huelleB fs e E₁ E₂ w1 g
        · rfl
        · cases hi : TraegerSchreibt g c
          · rfl
          · exact absurd ⟨g, (huelleB_iff hvoll).mp hr, hi⟩ hn
      obtain ⟨g, hg, hgc⟩ := hex
      have hw : (fs.all fun k => !(huelleB fs e E₁ E₂ w2 k) ||
          (!(TraegerSchreibt k c) && !(istIn (fussOrteG (teilP e E₁ E₂ k) k) c))) = true :=
        List.all_eq_true.mpr fun k _ => by
          cases hk : huelleB fs e E₁ E₂ w2 k
          · rfl
          · obtain ⟨h1, h2⟩ := h w1 hw1 w2 hw2 hne g hg hgc k ((huelleB_iff hvoll).mp hk)
            cases hi : istIn (fussOrteG (teilP e E₁ E₂ k) k) c
            · simp [h1]
            · exact absurd (istIn_iff.mp hi) h2
      simp [hw]

theorem poolSicherVB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {w : D.Fn} : poolSicherVB fs cs e E₁ E₂ w = true ↔ PoolSicherV fs e E₁ E₂ w := by
  unfold poolSicherVB PoolSicherV
  have hex : ∀ c : D.Tab ⊕ D.Glob, (!(waechterVon c).isEmpty || atomarB c) = true ↔
      (∃ L, Bewacht c L) ∨ AtomarAusgenommen c := by
    intro c
    constructor
    · intro hc
      have hc' : ausgenommenB c = true := hc
      by_cases hB : ∃ L, Bewacht c L
      · exact Or.inl hB
      · refine Or.inr (Classical.byContradiction fun hA => ?_)
        have := ausgenommenB_false.mpr ⟨fun L hL => hB ⟨L, hL⟩, hA⟩
        rw [hc'] at this
        cases this
    · intro hc
      show ausgenommenB c = true
      cases hx : ausgenommenB c
      · obtain ⟨hB, hA⟩ := ausgenommenB_false.mp hx
        rcases hc with ⟨L, hL⟩ | hc
        · exact absurd hL (hB L)
        · exact absurd hc hA
      · rfl
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun f hf c hc => ?_⟩
    have h4 := List.all_eq_true.mp h3 f (hvoll f)
    rw [(huelleB_iff hvoll).mpr hf, Bool.not_true, Bool.false_or] at h4
    have h5 := List.all_eq_true.mp h4 c (hcs c)
    rw [hc, Bool.not_true, Bool.false_or] at h5
    exact (hex c).mp h5
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : huelleB fs e E₁ E₂ w f
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      refine List.all_eq_true.mpr fun c _ => ?_
      cases hc : TraegerSchreibt f c
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact (hex c).mpr (h3 f ((huelleB_iff hvoll).mp hf) c hc)

/-- **The link Bool decides exactly `SchnittstelleSpec`** (given complete member lists). -/
theorem schnittstelleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    schnittstelleB fs cs e E₁ E₂ = true ↔ SchnittstelleSpec fs e E₁ E₂ := by
  unfold schnittstelleB
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    refine ⟨(platzhalterB_iff hvoll).mp h1, (platzhalterB_iff hvoll).mp h2,
      (keinRueckrufB_iff hvoll).mp h3, fun c hc => ?_, fun c hB hA => ?_, fun w hw => ?_⟩
    · have h := List.all_eq_true.mp h4 c (hcs c)
      rw [(lokBedarfB_iff hvoll).mpr hc, Bool.not_true, Bool.false_or] at h
      exact (getrenntVB_iff hvoll).mp h
    · have h := List.all_eq_true.mp h5 c (hcs c)
      rw [ausgenommenB_false.mpr ⟨hB, hA⟩, Bool.false_or] at h
      exact (schreibGetrenntVB_iff hvoll).mp h
    · have hw' : w ∈ (verbinde e E₁ E₂).ws := hw.subset (List.mem_cons_self)
      have h := List.all_eq_true.mp h6 w hw'
      rw [mehrfachB_iff.mpr hw, Bool.not_true, Bool.false_or] at h
      exact (poolSicherVB_iff hvoll hcs).mp h
  · intro h
    refine ⟨⟨⟨⟨⟨(platzhalterB_iff hvoll).mpr h.blatt₁, (platzhalterB_iff hvoll).mpr h.blatt₂⟩,
      (keinRueckrufB_iff hvoll).mpr h.keinRueckruf⟩, ?_⟩, ?_⟩, ?_⟩
    · refine List.all_eq_true.mpr fun c _ => ?_
      cases hc : lokBedarfB fs e E₁ E₂ c
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact (getrenntVB_iff hvoll).mpr (h.lok c ((lokBedarfB_iff hvoll).mp hc))
    · refine List.all_eq_true.mpr fun c _ => ?_
      cases ha : ausgenommenB c
      · obtain ⟨hB, hA⟩ := ausgenommenB_false.mp ha
        rw [Bool.false_or]
        exact (schreibGetrenntVB_iff hvoll).mpr (h.renn c hB hA)
      · rfl
    · refine List.all_eq_true.mpr fun w _ => ?_
      cases hm : mehrfachB (verbinde e E₁ E₂).ws w
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact (poolSicherVB_iff hvoll hcs).mpr (h.einzeln w (mehrfachB_iff.mp hm))

end Bool

end Gabbro.Grammatik.Zielsatz

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

/-! ## Embedding and iteration -/

section Einbettung

variable [DecidableEq D.Fn]

/-- **Linking is conservative**: a unit linked with a partner that owns nothing and starts
    nothing IS the unit. The statement `GabbroZiel` is unchanged by this diff; this lemma says
    the new operation does not move a single unit either. -/
theorem verbinde_leer (E E' : Einheit D) (h1 : E'.starts = []) (h2 : E'.gestartet = []) :
    verbinde (fun _ => true) E E' = E := by
  cases E
  unfold verbinde verbindeP mitRumpf
  rw [h1, h2, List.append_nil, List.append_nil]
  rfl

/-- **The linked unit is accepted by the concrete checker** -- so it can be linked again: a
    chain of units, by iteration. -/
theorem verbinde_akzeptiert {E₁ E₂ : Einheit D} {e : D.Fn → Bool} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (h₁ : Akzeptiert E₁.P E₁.S fs ls cs E₁.ws = true)
    (h₂ : Akzeptiert E₂.P E₂.S fs ls cs E₂.ws = true) (hV : Verbindbar E₁ E₂)
    (hS : schnittstelleB fs cs e E₁ E₂ = true) :
    Akzeptiert (verbinde e E₁ E₂).P (verbinde e E₁ E₂).S fs ls cs (verbinde e E₁ E₂).ws = true :=
  (akzeptiert_iff hvoll hls hcs).mpr (akzeptiertSpec_verbinde hvoll
    ((akzeptiert_iff hvoll hls hcs).mp h₁) ((akzeptiert_iff hvoll hls hcs).mp h₂) hV
    ((schnittstelleB_iff hvoll hcs).mp hS))

/-- **The user duty of the linked unit, restricted to what the two users own** (`a₁` inside
    unit 1's share, `a₂` inside unit 2's): the premise (b) of a further link. -/
theorem nutzerTeil_verbinde {E₁ E₂ : Einheit D} {e a₁ a₂ : D.Fn → Bool}
    (hV : Verbindbar E₁ E₂) (hQ : E₂.Q = E₁.Q)
    (h₁ : ∀ f, a₁ f = true → e f = true) (h₂ : ∀ f, a₂ f = true → e f = false)
    (hN₁ : NutzerTeil a₁ E₁) (hN₂ : NutzerTeil a₂ E₂) :
    NutzerTeil (fun f => a₁ f || a₂ f) (verbinde e E₁ E₂) := by
  have hS : E₂.S = E₁.S := hV.sperren.symm
  refine ⟨⟨fun passes f hf => ?_, hN₁.logik.2.1, hN₁.logik.2.2⟩, ⟨hN₁.start.sperren, ?_⟩⟩
  · show KoerperGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutGrund (verbindeP e E₁ E₂) passes E₁.Q E₁.S f
    cases ha : a₁ f
    · have ha2 : a₂ f = true := by simpa [ha] using hf
      have hef := h₂ f ha2
      obtain ⟨k, i, g⟩ := hN₂.logik.1 passes f ha2
      rw [p2_eq hV, hQ, hS] at k i g
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₂.P.rumpf f := by
        simp [hef]
      exact ⟨(koerper_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr g⟩
    · have hef := h₁ f ha
      obtain ⟨k, i, g⟩ := hN₁.logik.1 passes f ha
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₁.P.rumpf f := by
        simp [hef]
      exact ⟨(koerper_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr g⟩
  · intro a ha
    show ReqAmEintritt E₁.P a.1 (E₁.sp0.welt []) a.2
    simp only [verbinde, List.mem_append] at ha
    rcases ha with (h | h) | (h | h)
    · exact hN₁.start.req a (List.mem_append_left _ h)
    · have := hN₂.start.req a (List.mem_append_left _ h)
      unfold ReqAmEintritt at this ⊢
      rw [hV.requires, hV.speicher]
      exact this
    · exact hN₁.start.req a (List.mem_append_right _ h)
    · have := hN₂.start.req a (List.mem_append_right _ h)
      unfold ReqAmEintritt at this ⊢
      rw [hV.requires, hV.speicher]
      exact this

end Einbettung

#print axioms gabbro_ziel_verbund
#print axioms akzeptiertSpec_verbinde
#print axioms nutzerPflicht_verbinde
#print axioms schnittstelleB_iff
#print axioms reachB_ruft
#print axioms verbinde_leer
#print axioms verbinde_akzeptiert
#print axioms nutzerTeil_verbinde

end Gabbro.Grammatik.Zielsatz
