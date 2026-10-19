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
import Grammatik.Zielsatz.Kern.Beweis

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
  | _, _, _, _, .assignThru _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .assignGlob _ _ _ _ => rfl
  | _, _, _, _, .putBytes _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .assignVar _ _ => rfl
  | _, _, _, _, .shift _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .ite c t e => by
      simp only [stmtOrteP, blockOrteP_mitRumpf t, blockOrteP_mitRumpf e]
  | _, _, _, _, .onOption o p a => by
      simp only [stmtOrteP, blockOrteP_mitRumpf p, blockOrteP_mitRumpf a]
  | _, _, _, _, .onTag v arms => by simp only [stmtOrteP, armsOrteP_mitRumpf arms]
  | _, _, _, _, .onWhy r' arms => by simp only [stmtOrteP, grundArmsOrteP_mitRumpf arms]
  | _, _, _, _, .call _ _ _ _ => rfl
  | _, _, _, _, .callInd _ _ _ _ => rfl
  | _, _, _, _, .locks _ _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .breaking _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .traverse _ _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .retry _ _ body ueber => by
      simp only [stmtOrteP, blockOrteP_mitRumpf body, blockOrteP_mitRumpf ueber]
  | _, _, _, _, .forever _ _ body => by simp only [stmtOrteP, blockOrteP_mitRumpf body]
  | _, _, _, _, .axiomCall _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .regWrite _ _ _ => rfl
  | _, _, _, _, .transition _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .publish _ _ _ _ _ _ => rfl
  | _, _, _, _, .advances _ _ _ _ => rfl
  | _, _, _, _, .retires _ _ _ _ => rfl
  | _, _, _, _, .ret _ _ => rfl
  | _, _, _, _, .retWhy _ _ => rfl
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
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf err, blockOrteP_mitRumpf rest]
  | _, _, _, _, .regRead _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .regReadElse _ _ _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]
  | _, _, _, _, .awaits _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .exchange _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .narrow _ _ _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]
  | _, _, _, _, .check _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]
  | _, _, _, _, .float _ _ _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .floatLit _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .floatOf _ _ _ rest => by simp only [blockOrteP, blockOrteP_mitRumpf rest]
  | _, _, _, _, .floatNarrow _ _ _ sonst rest => by
      simp only [blockOrteP, endblockOrteP_mitRumpf sonst, blockOrteP_mitRumpf rest]

theorem endblockOrteP_mitRumpf {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), endblockOrteP (mitRumpf P r) e = endblockOrteP P e
  | _, _, _, .ret _ _ => rfl
  | _, _, _, .retWhy _ _ => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => by
      simp only [endblockOrteP, stmtOrteP_mitRumpf s, endblockOrteP_mitRumpf rest]
  | _, _, _, .bind _ rest => by simp only [endblockOrteP, endblockOrteP_mitRumpf rest]
  | _, _, _, .bindCall _ _ _ _ _ rest => by
      simp only [endblockOrteP, endblockOrteP_mitRumpf rest]; rfl
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => by simp only [endblockOrteP, endblockOrteP_mitRumpf rest]
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [endblockOrteP, endblockOrteP_mitRumpf err, endblockOrteP_mitRumpf rest]

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

end Gabbro.Grammatik.Zielsatz
