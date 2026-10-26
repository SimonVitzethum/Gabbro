/-
  File:      stage0/Stage0/Schnell/BlattPaar.lean
  Subject:   **A leaf does the same over a compact tail.** `OrakelPaar c OF OM`: the two oracles answer paired worlds
             alike (the fast one sees `c` questions fewer). `blatt_paar`: a leaf statement run in two paired worlds ends
             in paired outcomes -- the same kind, the same values, paired worlds (`AusPaar`).
-/
import Stage0.Schnell.Kompakt

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **Two oracles for one machine**: the fast one answers a world over a fast tail as the other answers the paired
    world over the machine's tail. -/
structure OrakelPaar (c : Nat) (OF OM : Orakel D) : Prop where
  wirkt : ∀ {sF sM : List (Ereignis D)} {σF σM : World D} (a : D.Ax) (ρ : Env D (D.aparams a)),
    Schwanz c sF sM → Paar sF sM σF σM →
      Paar sF sM (OF.wirkt a σF ρ).1 (OM.wirkt a σM ρ).1 ∧ (OF.wirkt a σF ρ).2 = (OM.wirkt a σM ρ).2
  regLies : ∀ {sF sM : List (Ereignis D)} {σF σM : World D} (r : D.Reg),
    Schwanz c sF sM → Paar sF sM σF σM → OF.regLies r σF = OM.regLies r σM
  sichtbar : ∀ {sF sM : List (Ereignis D)} {σF σM : World D} (g : D.Glob),
    Schwanz c sF sM → Paar sF sM σF σM → OF.sichtbar g σF = OM.sichtbar g σM
  zeiger : OF.zeiger = OM.zeiger

variable {c : Nat} {OF OM : Orakel D} {sF sM : List (Ereignis D)} {σF σM : World D}

theorem axiomAntwort_paar (hO : OrakelPaar c OF OM) (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) (a : D.Ax)
    (ρ : Env D (D.aparams a)) :
    Paar sF sM (axiomAntwort OF a σF ρ).1 (axiomAntwort OM a σM ρ).1 ∧
      (axiomAntwort OF a σF ρ).2 = (axiomAntwort OM a σM ρ).2 := by
  obtain ⟨hp, hr⟩ := hO.wirkt a ρ hS (h.fragt (.inl a))
  simp only [axiomAntwort]
  exact ⟨hp, by rw [hr, hO.zeiger]⟩

theorem axiomAntwortSonst_paar (hO : OrakelPaar c OF OM) (hS : Schwanz c sF sM) (h : Paar sF sM σF σM) (a : D.Ax)
    (ρ : Env D (D.aparams a)) :
    Paar sF sM (axiomAntwortSonst OF a σF ρ).1 (axiomAntwortSonst OM a σM ρ).1 ∧
      (axiomAntwortSonst OF a σF ρ).2 = (axiomAntwortSonst OM a σM ρ).2 := by
  obtain ⟨hp, hr⟩ := hO.wirkt a ρ hS (h.fragt (.inl a))
  simp only [axiomAntwortSonst]
  exact ⟨hp, by rw [hr, hO.zeiger]⟩

theorem Paar.evalErg {σ₀F σ₀M : World D} (h₀ : Paar sF sM σ₀F σ₀M) (h : Paar sF sM σF σM) {Γ : Ctx}
    {Λ : List (Res D)} {e : Option Ty} (x : ErgExpr D Γ Λ e) (ρ : Env D Γ) :
    evalErg σ₀F x σF ρ = evalErg σ₀M x σM ρ := by
  cases x with
  | empty => rfl
  | val e => exact h₀.eval h e ρ

/-- **Paired outcomes**: the same kind and values, paired worlds. -/
inductive AusPaar (sF sM : List (Ereignis D)) {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    Ausgang V l Γ → Ausgang V l Γ → Prop
  | ok {σF σM : World D} {ρ : Env D Γ} : Paar sF sM σF σM → AusPaar sF sM (.ok σF ρ) (.ok σM ρ)
  | zurueck {σF σM : World D} {v : ErgVal D V.erg} : Paar sF sM σF σM →
      AusPaar sF sM (.zurueck σF v) (.zurueck σM v)
  | why {σF σM : World D} {r : Fin V.gruende} : Paar sF sM σF σM → AusPaar sF sM (.why σF r) (.why σM r)
  | leave {h : l = true} {σF σM : World D} {ρ : Env D Γ} : Paar sF sM σF σM →
      AusPaar sF sM (.leave h σF ρ) (.leave h σM ρ)
  | next {h : l = true} {σF σM : World D} {ρ : Env D Γ} : Paar sF sM σF σM →
      AusPaar sF sM (.next h σF ρ) (.next h σM ρ)
  | logik (e : Logik D) : AusPaar sF sM (.logik e) (.logik e)
  | hardware (e : Hardware D) : AusPaar sF sM (.hardware e) (.hardware e)

/-- **A leaf over a compact tail**: the same outcome over paired worlds. -/
theorem blatt_paar (hS : Schwanz c sF sM) (hO : OrakelPaar c OF OM) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true → ∀ {σF σM : World D}, Paar sF sM σF σM → ∀ (ρ : Env D Γ),
      AusPaar sF sM (execStmt OF passes R s σF ρ) (execStmt OM passes R s σM ρ)
  | .assignSlot t f i e _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ (i.orte ++ e.orte)
    rw [hl.eval hl i ρ, hl.eval hl e ρ]
    exact .ok (hl.schreibSlot hS _ _ _ _ _)
  | .assignThru p t _ f i e _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ (p.orte ++ i.orte ++ e.orte)
    rw [hl.eval hl i ρ, hl.eval hl e ρ]
    exact .ok (hl.schreibSlot hS _ _ _ _ _)
  | .assignSlotRef r t _ _ f e _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ (r.orte ++ e.orte)
    rw [hl.eval hl r ρ, hl.eval hl e ρ]
    exact .ok (hl.schreibSlot hS _ _ _ _ _)
  | .assignGlob g e _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ e.orte
    rw [hl.eval hl e ρ]
    exact .ok (hl.schreibGlob hS _ _ _)
  | .putBytes t f hf n i _ _ e _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ (i.orte ++ e.orte)
    rw [hl.eval hl i ρ, hl.eval hl e ρ]
    exact .ok (Paar.schreibBytes hS t f hf Λ _ _ hl)
  | .assignVar x e, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ e.orte
    rw [hl.eval hl e ρ]
    exact .ok hl
  | .shift t f hτ i von nach hn _ _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ (.inl t :: i.orte)
    rw [hl.eval hl i ρ, hl.slots]
    split
    · exact .ok (hl.schreibSlot hS _ _ _ _ _)
    · exact .logik _
  | .axiomCall a args _ _ _ _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ args.orte
    rw [hl.evalArgs args ρ]
    obtain ⟨hp, ho⟩ := axiomAntwort_paar hO hS hl a (evalArgs (σM.lese Λ args.orte) args (σM.lese Λ args.orte) ρ)
    revert hp ho
    generalize axiomAntwort OF a _ _ = pF
    generalize axiomAntwort OM a _ _ = pM
    rintro hp ho
    obtain ⟨σ1, o1⟩ := pF
    obtain ⟨σ2, o2⟩ := pM
    simp only at hp ho
    subst ho
    cases o1
    · exact .hardware _
    · exact .ok hp
  | .regWrite r _ e, _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .ok (h.lese hS Λ e.orte)
  | .transition .., _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .ok (h.fragt _)
  | .publish g e _ _ _ _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ e.orte
    rw [hl.eval hl e ρ]
    exact .ok (hl.schreibGlob hS _ _ _)
  | .advances .., _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .ok h
  | .retires .., _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .ok h
  | .ret e _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    have hl := h.lese hS Λ e.orte
    rw [hl.evalErg hl e ρ]
    exact .zurueck hl
  | .retWhy .., _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .why h
  | .leave _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .leave h
  | .next _, _, σF, σM, h, ρ => by
    simp only [execStmt]
    exact .next h
  | .ite .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .onOption .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .onTag .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .onWhy .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .call .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .callInd .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .locks .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .breaking .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .traverse .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .retry .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .forever .., hb, _, _, _, _ => by simp [Stmt.istBlatt] at hb

end Gabbro.Stage0
