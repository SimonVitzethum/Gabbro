module

public import Grammatik.Kern.Syntax.Konst.Auswertung
public import Grammatik.Kern.Syntax.Konst.Kongruenz
public import Grammatik.Kern.Syntax.Konst.Rang
public import Grammatik.Logik.Ruf.RufTiefe

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Soundness of checked const calls.

  `const_call_sound`: for every admissible, terminating program with a
  successful checked evaluation to `v`, every world, oracle, pass count and
  every depth at or above the certified bound, `rufAt` answers `.ok` with
  the same value, and the answer world keeps the input slots and globals
  (the design's frame condition: reads only append trace events). The proof
  goes by induction on the rank-free structural congruence (`constRufGleich`)
  plus depth stability (`rufAt_stabil_ab`); frame preservation is proved
  separately by fuel induction (`constRufErhaelt`), since relations only
  ever compare two runs. The termination rank is not consumed by the
  congruence itself; `n` fixes the certified depth bound. Uniqueness, depth
  stability and error correspondence follow separately below. -/

/-- Frame predicates over single outcomes: every world inside agrees with
    the entry world on slots and globals. -/
@[expose] inductive AusgangErhaelt (c : ConstProgram) (σ : World c.D) : Ausgang V l Γ → Prop where
  | ok : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.ok σ' ρ')
  | zurueck : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.zurueck σ' v)
  | why : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.why σ' r)
  | leave : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.leave h σ' ρ')
  | next : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.next h σ' ρ')
  | logik (e : Logik c.D) : AusgangErhaelt c σ (.logik e)
  | hardware (e : Hardware c.D) : AusgangErhaelt c σ (.hardware e)

@[expose] inductive EndErhaelt (c : ConstProgram) (σ : World c.D) : EndAusgang V l Γ → Prop where
  | zurueck : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.zurueck σ' v)
  | why : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.why σ' r)
  | leave : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.leave h σ' ρ')
  | next : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.next h σ' ρ')
  | logik (e : Logik c.D) : EndErhaelt c σ (.logik e)
  | hardware (e : Hardware c.D) : EndErhaelt c σ (.hardware e)

@[expose] inductive RufErhaelt (c : ConstProgram) (σ : World c.D) : RufAusgang f → Prop where
  | ok : σ'.slots = σ.slots → σ'.globs = σ.globs → RufErhaelt c σ (.ok σ' v)
  | why : σ'.slots = σ.slots → σ'.globs = σ.globs → RufErhaelt c σ (.why σ' r)
  | logik (e : Logik c.D) : RufErhaelt c σ (.logik e)
  | hardware (e : Hardware c.D) : RufErhaelt c σ (.hardware e)

mutual
theorem constStmtErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Stmt c.D V l Γ [] []} (h : ConstStmt c body)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execStmt O p R body σ ρ) :=
  match h with
  | .assignVar _ => by simp only [execStmt]; exact AusgangErhaelt.ok rfl rfl
  | .ite _ hyes hno => by
    simp only [execStmt]
    by_cases hcond : wahr? (eval σ _ σ ρ) = true
    · simp only [if_pos hcond]
      exact constBlockErhaelt c hyes O p R σ ρ hR
    · simp only [if_neg hcond]
      exact constBlockErhaelt c hno O p R σ ρ hR
  | .onOption _ hpresent habsent => by
    simp only [execStmt]
    cases hval : (eval σ _ σ ρ : Option _) with
    | none => simp only [hval]; exact constBlockErhaelt c habsent O p R σ ρ hR
    | some k =>
      simp only [hval]
      cases constBlockErhaelt c hpresent O p R σ (.cons k ρ) hR with
      | ok _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.ok hS hG
      | zurueck _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.zurueck hS hG
      | why _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.why hS hG
      | leave _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.leave hS hG
      | next _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.next hS hG
      | logik _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.logik _
      | hardware _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.hardware _
  | .onTag _ harms => by simp only [execStmt]; exact constArmsErhaelt c harms O p R _ σ ρ hR
  | .onWhy _ harms => by simp only [execStmt]; exact constReasonErhaelt c harms O p R _ σ ρ hR
  | .call _ _ _ hr _ _ => by
    simp only [execStmt]
    cases (hR _ σ _) with
    | ok _ _ hS hG => dsimp only; exact AusgangErhaelt.ok hS hG
    | why _ r₁ hS hG => exact Fin.elim0 (Fin.cast hr r₁)
    | logik _ => dsimp only; exact AusgangErhaelt.logik _
    | hardware _ => dsimp only; exact AusgangErhaelt.hardware _
  | .ret _ => by simp only [execStmt]; exact AusgangErhaelt.zurueck rfl rfl
theorem constBlockErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Block c.D V l Γ [] []} (h : ConstBlock c body)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execBlock O p R body σ ρ) :=
  match h with
  | .nil => by simp only [execBlock]; exact AusgangErhaelt.ok rfl rfl
  | .cons hs hrest => by
    simp only [execBlock]
    cases constStmtErhaelt c hs O p R σ ρ hR with
    | ok _ _ hS hG => dsimp only; exact constBlockErhaelt c hrest O p R _ _ hR
    | zurueck _ _ hS hG => dsimp only; exact AusgangErhaelt.zurueck hS hG
    | why _ _ hS hG => dsimp only; exact AusgangErhaelt.why hS hG
    | leave _ _ hS hG => dsimp only; exact AusgangErhaelt.leave hS hG
    | next _ _ hS hG => dsimp only; exact AusgangErhaelt.next hS hG
    | logik _ => dsimp only; exact AusgangErhaelt.logik _
    | hardware _ => dsimp only; exact AusgangErhaelt.hardware _
  | .bind _ hrest => by
    simp only [execBlock]
    cases constBlockErhaelt c hrest O p R σ _ hR with
    | ok _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.ok hS hG
    | zurueck _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.zurueck hS hG
    | why _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.why hS hG
    | leave _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.leave hS hG
    | next _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.next hS hG
    | logik _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.logik _
    | hardware _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.hardware _
  | .bindCall _ _ _ _ hr _ _ _ hrest => by
    simp only [execBlock]
    cases (hR _ σ _) with
    | ok _ _ hS hG =>
      dsimp only
      cases constBlockErhaelt c hrest O p R _ _ hR with
      | ok _ _ hS' hG' => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.ok hS' hG'
      | zurueck _ _ hS' hG' => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.zurueck hS' hG'
      | why _ _ hS' hG' => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.why hS' hG'
      | leave _ _ hS' hG' => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.leave hS' hG'
      | next _ _ hS' hG' => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.next hS' hG'
      | logik _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.logik _
      | hardware _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.hardware _
    | why _ r₁ _ _ => exact Fin.elim0 (Fin.cast hr r₁)
    | logik _ => dsimp only; exact AusgangErhaelt.logik _
    | hardware _ => dsimp only; exact AusgangErhaelt.hardware _
theorem constEndErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Endblock c.D V l Γ []} (h : ConstEnd c body)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    EndErhaelt c σ (execEnd O p R body σ ρ) :=
  match h with
  | .ret _ => by simp only [execEnd]; exact EndErhaelt.zurueck rfl rfl
  | .cons hs hrest => by
    simp only [execEnd]
    cases constStmtErhaelt c hs O p R σ ρ hR with
    | ok _ _ hS hG => dsimp only; exact constEndErhaelt c hrest O p R _ _ hR
    | zurueck _ _ hS hG => dsimp only; exact EndErhaelt.zurueck hS hG
    | why _ _ hS hG => dsimp only; exact EndErhaelt.why hS hG
    | leave _ _ hS hG => dsimp only; exact EndErhaelt.leave hS hG
    | next _ _ hS hG => dsimp only; exact EndErhaelt.next hS hG
    | logik _ => dsimp only; exact EndErhaelt.logik _
    | hardware _ => dsimp only; exact EndErhaelt.hardware _
  | .bind _ hrest => by
    simp only [execEnd]
    cases constEndErhaelt c hrest O p R σ _ hR with
    | zurueck _ _ hS hG => simp only [EndAusgang.schrumpf]; exact EndErhaelt.zurueck hS hG
    | why _ _ hS hG => simp only [EndAusgang.schrumpf]; exact EndErhaelt.why hS hG
    | leave _ _ hS hG => simp only [EndAusgang.schrumpf]; exact EndErhaelt.leave hS hG
    | next _ _ hS hG => simp only [EndAusgang.schrumpf]; exact EndErhaelt.next hS hG
    | logik _ => simp only [EndAusgang.schrumpf]; exact EndErhaelt.logik _
    | hardware _ => simp only [EndAusgang.schrumpf]; exact EndErhaelt.hardware _
  | .bindCall _ _ _ _ hr _ _ _ hrest => by
    simp only [execEnd]
    cases (hR _ σ _) with
    | ok _ _ hS hG =>
      dsimp only
      cases constEndErhaelt c hrest O p R _ _ hR with
      | zurueck _ _ hS' hG' => simp only [EndAusgang.schrumpf]; exact EndErhaelt.zurueck hS' hG'
      | why _ _ hS' hG' => simp only [EndAusgang.schrumpf]; exact EndErhaelt.why hS' hG'
      | leave _ _ hS' hG' => simp only [EndAusgang.schrumpf]; exact EndErhaelt.leave hS' hG'
      | next _ _ hS' hG' => simp only [EndAusgang.schrumpf]; exact EndErhaelt.next hS' hG'
      | logik _ => simp only [EndAusgang.schrumpf]; exact EndErhaelt.logik _
      | hardware _ => simp only [EndAusgang.schrumpf]; exact EndErhaelt.hardware _
    | why _ r₁ _ _ => exact Fin.elim0 (Fin.cast hr r₁)
    | logik _ => dsimp only; exact EndErhaelt.logik _
    | hardware _ => dsimp only; exact EndErhaelt.hardware _
  | .ite _ hyes hno => by
    simp only [execEnd]
    by_cases hcond : wahr? (eval σ _ σ ρ) = true
    · simp only [if_pos hcond]
      exact constEndErhaelt c hyes O p R σ ρ hR
    · simp only [if_neg hcond]
      exact constEndErhaelt c hno O p R σ ρ hR
theorem constArmsErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : Arms c.D V l Γ [] [] cs} (h : ConstArms c arms)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v : Wert c.D (.sum cs)) (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execArms O p R arms v σ ρ) := by
  cases h with
  | nil =>
    obtain ⟨i, _⟩ := v
    exact i.elim0
  | cons hbody hrest =>
    obtain ⟨⟨tag, _⟩, _⟩ := v
    cases tag with
    | zero => simp only [execArms]; exact schrumpfArmErhaelt c (constBlockErhaelt c hbody O p R σ _ hR)
    | succ _ => simp only [execArms]; exact constArmsErhaelt c hrest O p R _ σ ρ hR
theorem constReasonErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : GrundArms c.D V l Γ [] [] n} (h : ConstReasonArms c arms)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v : Fin n) (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execGrund O p R arms v σ ρ) := by
  cases h with
  | nil => exact Fin.elim0 v
  | cons hbody hrest =>
    cases v with
    | mk tag _ =>
      cases tag with
      | zero => simp only [execGrund]; exact constBlockErhaelt c hbody O p R σ ρ hR
      | succ _ => simp only [execGrund]; exact constReasonErhaelt c hrest O p R _ σ ρ hR
end

/-- Shrinking preserves single-run frame. -/
theorem schrumpfArmErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {k : Option Ty} {o : Ausgang V l (ArmCtx Γ k)} {σ : World c.D}
    (h : AusgangErhaelt c σ o) : AusgangErhaelt c σ (o.schrumpfArm k) := by
  cases k with
  | none => simp only [Ausgang.schrumpfArm]; exact h
  | some _ =>
    simp only [Ausgang.schrumpfArm]
    cases h with
    | ok _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.ok hS hG
    | zurueck _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.zurueck hS hG
    | why _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.why hS hG
    | leave _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.leave hS hG
    | next _ _ hS hG => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.next hS hG
    | logik _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.logik _
    | hardware _ => simp only [Ausgang.schrumpf]; exact AusgangErhaelt.hardware _

/-- Successful const calls keep slots and globals, by fuel induction with
    the handler premise carried by itself. -/
theorem constRufErhaelt (c : ConstProgram) (hadm : ConstAdmissible c) :
    ∀ (d : Nat) (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g))
      (O : Orakel c.D) (p : Nat),
      RufErhaelt c σ (rufAt c.P O p d g σ ρ) := by
  intro d
  induction d with
  | zero =>
    intro g σ ρ O p
    simp only [rufAt]
    exact RufErhaelt.logik _
  | succ d ih =>
    intro g σ ρ O p
    rw [rufAt_succ_eq (c.P) O p d]
    simp only [rufSchritt]
    by_cases hgate : wahr? (eval (σ.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.requires g) (σ.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) ρ) = false
    · simp only [if_pos hgate]
      exact RufErhaelt.logik _
    · simp only [if_neg hgate]
      have hbridge := constRumpfTransport c g O p (rufAt c.P O p d) _ _
      have hbody := constEndErhaelt c (hadm g) O p (rufAt c.P O p d) _ _ (fun h s r => ih h s r O p)
      rw [hbridge] at hbody
      cases hbody with
      | zurueck _ _ hS hG =>
        by_cases hensgate : wahr? (eval _ (c.P.ensures g) _ _) = false
        · simp only [if_pos hensgate]
          exact RufErhaelt.logik _
        · simp only [if_neg hensgate]
          have hempty : c.D.invs = [] := by cases h : c.D.invs with | nil => rfl | cons i _ => exact (c.noInvariants i).elim
          rw [hempty]
          dsimp only
          exact RufErhaelt.ok hS hG
      | why _ _ hS hG => dsimp only; exact RufErhaelt.why hS hG
      | leave h1 _ _ => cases h1
      | next h1 _ _ => cases h1
      | logik _ => dsimp only; exact RufErhaelt.logik _
      | hardware _ => dsimp only; exact RufErhaelt.hardware _

/-- Generic meaning theorem: a successful checked evaluation denotes the
    same value at every world, oracle, pass count and sufficient depth,
    with the design's frame condition. -/
theorem const_call_sound (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert : ConstCallCertificate c f args) (hadm : ConstAdmissible c) (n : Nat)
    (hterm : ConstTermination c n) :
    ∀ (σ : World c.D) (O : Orakel c.D) (passes depth : Nat),
      max cert.bound (n + 1) ≤ depth →
      ∃ σ', rufAt c.P O passes depth f σ args = RufAusgang.ok σ' cert.value ∧ σ'.slots = σ.slots ∧ σ'.globs = σ.globs := by
  have _ := hterm
  intro σ O passes depth hdepth
  have hok := cert.equation
  have hnab : ∀ g : c.D.Fn, rufAt c.P (constOrakel c) 0 cert.bound f (constWelt c) args ≠ RufAusgang.logik (.abstieg g) := by
    intro g hcon
    rw [hok] at hcon
    cases hcon
  have hmax : cert.bound + (max cert.bound (n + 1) - cert.bound) = max cert.bound (n + 1) :=
    Nat.add_sub_cancel' (Nat.le_max_left cert.bound (n + 1))
  have hcanon := rufAt_stabil_ab c.P (constOrakel c) 0 cert.bound f (constWelt c) args hnab (max cert.bound (n + 1) - cert.bound)
  rw [hmax] at hcanon
  rw [hok] at hcanon
  have hW := constWeltRahmenAlle c (constWelt c) σ
  have hrel := constRufGleich c hadm (max cert.bound (n + 1)) f (constWelt c) σ args (constOrakel c) O 0 passes hW
  rw [hcanon] at hrel
  cases harb : rufAt c.P O passes (max cert.bound (n + 1)) f σ args with
  | ok σ' v' =>
    have hnab' : ∀ g : c.D.Fn, rufAt c.P O passes (max cert.bound (n + 1)) f σ args ≠ RufAusgang.logik (.abstieg g) := by
      intro g hcon
      rw [harb] at hcon
      cases hcon
    have hstep : max cert.bound (n + 1) + (depth - max cert.bound (n + 1)) = depth :=
      Nat.add_sub_cancel' hdepth
    have hstab := rufAt_stabil_ab c.P O passes (max cert.bound (n + 1)) f σ args hnab' (depth - max cert.bound (n + 1))
    rw [hstep, harb] at hstab
    rw [harb] at hrel
    cases hrel with
    | ok _ _ _ _ _ _ hv' =>
      have hcert := constRufErhaelt c hadm cert.bound f (constWelt c) args (constOrakel c) 0
      rw [hok] at hcert
      cases hcert with
      | ok _ _ hSc hGc =>
        refine ⟨σ', ?_, ?_, ?_⟩
        · rw [hstab]
          congr 1
          exact hv'.symm
        · rw [← hS, hSc, hW.1]
        · rw [← hG, hGc, hW.2]
  | why _ _ =>
    rw [harb] at hrel
    cases hrel
  | logik _ =>
    rw [harb] at hrel
    cases hrel
  | hardware _ =>
    rw [harb] at hrel
    cases hrel

/-- Uniqueness: two certificates over one call denote one value. -/
theorem const_call_eindeutig (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert₁ cert₂ : ConstCallCertificate c f args) (hadm : ConstAdmissible c) (n : Nat)
    (hterm : ConstTermination c n) :
    cert₁.value = cert₂.value := by
  have depth := max (max cert₁.bound (n + 1)) (max cert₂.bound (n + 1))
  have hD₁ : max cert₁.bound (n + 1) ≤ depth := Nat.le_max_left _ _
  have hD₂ : max cert₂.bound (n + 1) ≤ depth := Nat.le_max_right _ _
  obtain ⟨s₁, e₁, _, _⟩ := const_call_sound c f args cert₁ hadm n hterm (constWelt c) (constOrakel c) 0 depth hD₁
  obtain ⟨s₂, e₂, _, _⟩ := const_call_sound c f args cert₂ hadm n hterm (constWelt c) (constOrakel c) 0 depth hD₂
  rw [e₁] at e₂
  cases e₂
  rfl

/-- Depth stability: past its bound the certified call no longer moves. -/
theorem const_call_stabil (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert : ConstCallCertificate c f args) :
    ∀ k : Nat, rufAt c.P (constOrakel c) 0 (cert.bound + k) f (constWelt c) args = rufAt c.P (constOrakel c) 0 cert.bound f (constWelt c) args := by
  intro k
  have hnab : ∀ g : c.D.Fn, rufAt c.P (constOrakel c) 0 cert.bound f (constWelt c) args ≠ RufAusgang.logik (.abstieg g) := by
    intro g hcon
    rw [cert.equation] at hcon
    cases hcon
  exact rufAt_stabil_ab c.P (constOrakel c) 0 cert.bound f (constWelt c) args hnab k

/-- Error correspondence, contract half: a failed requires or ensures maps
    to the matching `vorbedingung`/`nachbedingung` outcome, never to a value. -/
theorem const_call_fehlerVertrag (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (g : c.D.Fn)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik (.vorbedingung g) ∨ rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik (.nachbedingung g)) :
    evalConstCall c f args limit = ConstCallResult.contract g := by
  unfold evalConstCall
  dsimp only
  rw [if_pos haufwand]
  rcases h with h | h <;> simp only [h]

/-- Error correspondence, exhaustion half: exhausted fuel refuses with the
    used and allowed work. -/
theorem const_call_fehlerErschoepft (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (g : c.D.Fn)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik (.abstieg g)) :
    evalConstCall c f args limit = ConstCallResult.exhausted (constArbeitsSchranke c f) limit := by
  unfold evalConstCall
  dsimp only
  rw [if_pos haufwand]
  simp only [h]

/-- Error correspondence, limit half: work past the limit refuses before
    any reduction. -/
theorem const_call_fehlerLimit (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat)
    (hneg : ¬ constArbeitsSchranke c f ≤ limit) :
    evalConstCall c f args limit = ConstCallResult.exhausted (constArbeitsSchranke c f) limit := by
  unfold evalConstCall
  dsimp only
  rw [if_neg hneg]

/-- Error correspondence, range half: a range failure never denotes. -/
theorem const_call_fehlerBereich (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik .bereich) :
    evalConstCall c f args limit = ConstCallResult.range f := by
  unfold evalConstCall
  dsimp only
  rw [if_pos haufwand]
  simp only [h]

/-- Error correspondence, dependency half: a hardware answer needed outside
    the closed program refuses as an unresolved dependency. -/
theorem const_call_fehlerHardware (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (e : Hardware c.D)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.hardware e) :
    evalConstCall c f args limit = ConstCallResult.dependency f := by
  unfold evalConstCall
  dsimp only
  rw [if_pos haufwand]
  simp only [h]

/-- Error correspondence, reason half: the absent reason channel refuses as
    an unresolved dependency. -/
theorem const_call_fehlerGrund (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (w : World c.D) (r : Fin (c.D.gruende f))
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.why w r) :
    evalConstCall c f args limit = ConstCallResult.dependency f := by
  unfold evalConstCall
  dsimp only
  rw [if_pos haufwand]
  simp only [h]

end Gabbro.Grammatik
