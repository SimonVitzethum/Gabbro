/- Call closure and section checks survive the idle-root translation. The signature gate
   stays false: declared pointer costs do not yet enter the model's cost potential. -/
module
public import Grammatik.Logik.Fortschritt.Halten.RuheKosten
@[expose] public section

namespace Gabbro.Grammatik.HaltRuhe
variable {D : Deklaration}

section Calls
variable (Z : D.Fn → Bool) {V : Vertrag D}

@[simp] theorem rufeS_nachΛ {l : Bool} {Γ : Ctx} {Λ a b : List (Res D)} (h : a = b)
    (s : Stmt D V l Γ Λ a) :
    rufeS Z (fun _ => false) true (Stmt.nachΛ h s) = rufeS Z (fun _ => false) true s := by
  subst h
  rfl

@[simp] theorem rufeB_vorΛ {l : Bool} {Γ : Ctx} {a b Λ : List (Res D)} (h : a = b)
    (s : Block D V l Γ a Λ) :
    rufeB Z (fun _ => false) true (Block.vorΛ h s) = rufeB Z (fun _ => false) true s := by
  subst h
  rfl

@[simp] theorem rufeE_umΛ {l : Bool} {Γ : Ctx} {a b : List (Res D)} (h : a = b)
    (s : Endblock D V l Γ a) :
    rufeE Z (fun _ => false) true (Endblock.umΛ h s) = rufeE Z (fun _ => false) true s := by
  subst h
  rfl

mutual
theorem rufeS_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    rufeS (fun g => g.elim false Z) (fun _ => false) true (ruS s) =
      rufeS Z (fun _ => false) true s := by
  cases s <;> simp only [ruS, rufeS_nachΛ, rufeS, rufeB_ru, rufeArms_ru, rufeGArms_ru,
    rufeE_umΛ, rufeE_ru, Option.elim]
termination_by structural s

theorem rufeB_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    rufeB (fun g => g.elim false Z) (fun _ => false) true (ruB b) =
      rufeB Z (fun _ => false) true b := by
  cases b <;> simp only [ruB, rufeB, rufeB_vorΛ, rufeS_ru, rufeB_ru, rufeE_umΛ,
    rufeE_ru, Option.elim]
termination_by structural b

theorem rufeArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) :
    rufeArms (fun g => g.elim false Z) (fun _ => false) true (ruArms arms) =
      rufeArms Z (fun _ => false) true arms := by
  cases arms <;> simp only [ruArms, rufeArms, rufeB_ru, rufeArms_ru]
termination_by structural arms

theorem rufeGArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) :
    rufeGArms (fun g => g.elim false Z) (fun _ => false) true (ruGArms arms) =
      rufeGArms Z (fun _ => false) true arms := by
  cases arms <;> simp only [ruGArms, rufeGArms, rufeB_ru, rufeGArms_ru]
termination_by structural arms

theorem rufeE_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    rufeE (fun g => g.elim false Z) (fun _ => false) true (ruEnd e) =
      rufeE Z (fun _ => false) true e := by
  cases e <;> simp only [ruEnd, rufeE, rufeE_umΛ, rufeS_ru, rufeE_ru, Option.elim]
termination_by structural e
end
end Calls

section Sections
variable (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
  {V : Vertrag D}

@[simp] theorem haltS_nachΛ {l : Bool} {Γ : Ctx} {Λ a b : List (Res D)} (eq : a = b)
    (s : Stmt D V l Γ Λ a) : haltS h c Z pa (Stmt.nachΛ eq s) = haltS h c Z pa s := by
  subst eq
  rfl

@[simp] theorem haltB_vorΛ {l : Bool} {Γ : Ctx} {a b Λ : List (Res D)} (eq : a = b)
    (s : Block D V l Γ a Λ) : haltB h c Z pa (Block.vorΛ eq s) = haltB h c Z pa s := by
  subst eq
  rfl

@[simp] theorem haltE_umΛ {l : Bool} {Γ : Ctx} {a b : List (Res D)} (eq : a = b)
    (s : Endblock D V l Γ a) : haltE h c Z pa (Endblock.umΛ eq s) = haltE h c Z pa s := by
  subst eq
  rfl

mutual
theorem haltS_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    haltS h (fun g => g.elim 0 c) (fun g => g.elim false Z) pa (ruS s) = haltS h c Z pa s := by
  cases s <;> simp only [ruS, haltS_nachΛ, haltS, haltB_ru, haltArms_ru, haltGArms_ru,
    haltE_umΛ, haltE_ru, kostenBlock_ru, rufeB_ru]
termination_by structural s

theorem haltB_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    haltB h (fun g => g.elim 0 c) (fun g => g.elim false Z) pa (ruB b) = haltB h c Z pa b := by
  cases b <;> simp only [ruB, haltB, haltB_vorΛ, haltS_ru, haltB_ru, haltE_umΛ, haltE_ru]
termination_by structural b

theorem haltArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) :
    haltArms h (fun g => g.elim 0 c) (fun g => g.elim false Z) pa (ruArms arms) =
      haltArms h c Z pa arms := by
  cases arms <;> simp only [ruArms, haltArms, haltB_ru, haltArms_ru]
termination_by structural arms

theorem haltGArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) :
    haltGArms h (fun g => g.elim 0 c) (fun g => g.elim false Z) pa (ruGArms arms) =
      haltGArms h c Z pa arms := by
  cases arms <;> simp only [ruGArms, haltGArms, haltB_ru, haltGArms_ru]
termination_by structural arms

theorem haltE_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    haltE h (fun g => g.elim 0 c) (fun g => g.elim false Z) pa (ruEnd e) = haltE h c Z pa e := by
  cases e <;> simp only [ruEnd, haltE, haltE_umΛ, haltS_ru, haltE_ru]
termination_by structural e
end
end Sections
end Gabbro.Grammatik.HaltRuhe
