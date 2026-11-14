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

/- Match the constructors directly so the recursive calls retain their size relation.
   The translated indices agree definitionally; rewrite those laws with `erw`. -/
mutual
theorem rufeS_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    rufeS (D := D.mitRuhe) (fun (g : Option D.Fn) => g.elim false Z) (fun _ => false) true (ruS s) =
      rufeS Z (fun _ => false) true s := by
  match s with
  | .assignSlot .. | .assignThru .. | .assignGlob .. | .putBytes .. | .assignVar .. | .shift ..
  | .ite .. | .onOption .. | .onTag .. | .onWhy .. | .call .. | .callInd .. | .locks ..
  | .breaking .. | .traverse .. | .retry .. | .forever .. | .axiomCall .. | .regWrite ..
  | .transition .. | .publish .. | .advances .. | .retires .. | .ret .. | .retWhy .. | .leave ..
  | .next .. | .assignSlotRef .. | .consumeTraverse .. | .retScoped .. | .retWhyScoped ..
  | .axiomCallElse .. | .callIndElse .. | .assignThruOwn .. =>
    simp only [ruS, rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [rufeS_nachΛ]
        | erw [rufeB_vorΛ]
        | erw [rufeE_umΛ]
        | erw [rufeS_ru]
        | erw [rufeB_ru]
        | erw [rufeArms_ru]
        | erw [rufeGArms_ru]
        | erw [rufeE_ru]
        | simp only [rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none])
    try rfl
termination_by sizeOf s

theorem rufeB_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    rufeB (D := D.mitRuhe) (fun (g : Option D.Fn) => g.elim false Z) (fun _ => false) true (ruB b) =
      rufeB Z (fun _ => false) true b := by
  match b with
  | .nil .. | .cons .. | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse ..
  | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse .. | .awaits ..
  | .exchange .. | .narrow .. | .check .. | .float .. | .floatLit .. | .floatOf ..
  | .floatNarrow .. | .narrowRequired .. | .bindCallIndElse .. =>
    simp only [ruB, rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [rufeS_nachΛ]
        | erw [rufeB_vorΛ]
        | erw [rufeE_umΛ]
        | erw [rufeS_ru]
        | erw [rufeB_ru]
        | erw [rufeArms_ru]
        | erw [rufeGArms_ru]
        | erw [rufeE_ru]
        | simp only [rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none])
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) ..
  | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    simp only [ruB, rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [rufeB_ru rest]
        | erw [rufeS_nachΛ]
        | erw [rufeB_vorΛ]
        | erw [rufeE_umΛ]
        | erw [rufeS_ru]
        | erw [rufeB_ru]
        | erw [rufeArms_ru]
        | erw [rufeGArms_ru]
        | erw [rufeE_ru]
        | simp only [rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none])
    try rfl
termination_by sizeOf b

theorem rufeArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) :
    rufeArms (D := D.mitRuhe) (fun (g : Option D.Fn) => g.elim false Z) (fun _ => false) true (ruArms arms) =
      rufeArms Z (fun _ => false) true arms := by
  match arms with
  | .nil => rfl
  | .cons (c := none) b rest | .cons (c := some _) b rest =>
    simp only [ruArms, rufeArms]
    erw [rufeB_ru b, rufeArms_ru rest]
termination_by sizeOf arms

theorem rufeGArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) :
    rufeGArms (D := D.mitRuhe) (fun (g : Option D.Fn) => g.elim false Z) (fun _ => false) true (ruGArms arms) =
      rufeGArms Z (fun _ => false) true arms := by
  match arms with
  | .nil => rfl
  | .cons b rest =>
    simp only [ruGArms, rufeGArms]
    erw [rufeB_ru b, rufeGArms_ru rest]
termination_by sizeOf arms

theorem rufeE_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    rufeE (D := D.mitRuhe) (fun (g : Option D.Fn) => g.elim false Z) (fun _ => false) true (ruEnd e) =
      rufeE Z (fun _ => false) true e := by
  match e with
  | .ret .. | .retWhy .. | .leave .. | .next .. | .cons .. | .bind .. | .bindCall ..
  | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse ..
  | .awaits .. | .bindCallInd .. | .narrow .. | .exchange .. | .ite .. | .narrowRequired ..
  | .retScoped .. | .retWhyScoped .. | .bindCallIndElse .. | .float .. | .floatLit ..
  | .floatOf .. | .floatNarrow .. =>
    simp only [ruEnd, rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [rufeS_nachΛ]
        | erw [rufeB_vorΛ]
        | erw [rufeE_umΛ]
        | erw [rufeS_ru]
        | erw [rufeB_ru]
        | erw [rufeArms_ru]
        | erw [rufeGArms_ru]
        | erw [rufeE_ru]
        | simp only [rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none])
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) ..
  | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    simp only [ruEnd, rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [rufeE_ru rest]
        | erw [rufeS_nachΛ]
        | erw [rufeB_vorΛ]
        | erw [rufeE_umΛ]
        | erw [rufeS_ru]
        | erw [rufeB_ru]
        | erw [rufeArms_ru]
        | erw [rufeGArms_ru]
        | erw [rufeE_ru]
        | simp only [rufeS, rufeB, rufeE, Option.elim_some, Option.elim_none])
    try rfl
termination_by sizeOf e
end
end Calls

section Sections
variable (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
  {V : Vertrag D}

@[simp] theorem haltS_nachΛ {l : Bool} {Γ : Ctx} {Λ a b : List (Res D)} (eq : a = b)
    (s : Stmt D V l Γ Λ a) : haltS h ep c Z pa (Stmt.nachΛ eq s) = haltS h ep c Z pa s := by
  subst eq
  rfl

@[simp] theorem haltB_vorΛ {l : Bool} {Γ : Ctx} {a b Λ : List (Res D)} (eq : a = b)
    (s : Block D V l Γ a Λ) : haltB h ep c Z pa (Block.vorΛ eq s) = haltB h ep c Z pa s := by
  subst eq
  rfl

@[simp] theorem haltE_umΛ {l : Bool} {Γ : Ctx} {a b : List (Res D)} (eq : a = b)
    (s : Endblock D V l Γ a) : haltE h ep c Z pa (Endblock.umΛ eq s) = haltE h ep c Z pa s := by
  subst eq
  rfl

mutual
theorem haltS_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    haltS (D := D.mitRuhe) h ep (fun (g : Option D.Fn) => g.elim 0 c) (fun (g : Option D.Fn) => g.elim false Z) pa (ruS s) =
      haltS h ep c Z pa s := by
  match s with
  | .assignSlot .. | .assignThru .. | .assignGlob .. | .putBytes .. | .assignVar .. | .shift ..
  | .ite .. | .onOption .. | .onTag .. | .onWhy .. | .call .. | .callInd .. | .locks ..
  | .breaking .. | .traverse .. | .retry .. | .forever .. | .axiomCall .. | .regWrite ..
  | .transition .. | .publish .. | .advances .. | .retires .. | .ret .. | .retWhy .. | .leave ..
  | .next .. | .assignSlotRef .. | .consumeTraverse .. | .retScoped .. | .retWhyScoped ..
  | .axiomCallElse .. | .callIndElse .. | .assignThruOwn .. =>
    simp only [ruS, haltS, haltB, haltE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [haltS_nachΛ]
        | erw [haltB_vorΛ]
        | erw [haltE_umΛ]
        | erw [kostenBlock_ru]
        | erw [rufeB_ru]
        | erw [haltS_ru]
        | erw [haltB_ru]
        | erw [haltArms_ru]
        | erw [haltGArms_ru]
        | erw [haltE_ru]
        | simp only [haltS, haltB, haltE, Option.elim_some, Option.elim_none])
    try rfl
termination_by sizeOf s

theorem haltB_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    haltB (D := D.mitRuhe) h ep (fun (g : Option D.Fn) => g.elim 0 c) (fun (g : Option D.Fn) => g.elim false Z) pa (ruB b) =
      haltB h ep c Z pa b := by
  match b with
  | .nil .. | .cons .. | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse ..
  | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse .. | .awaits ..
  | .exchange .. | .narrow .. | .check .. | .float .. | .floatLit .. | .floatOf ..
  | .floatNarrow .. | .narrowRequired .. | .bindCallIndElse .. =>
    simp only [ruB, haltS, haltB, haltE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [haltS_nachΛ]
        | erw [haltB_vorΛ]
        | erw [haltE_umΛ]
        | erw [kostenBlock_ru]
        | erw [rufeB_ru]
        | erw [haltS_ru]
        | erw [haltB_ru]
        | erw [haltArms_ru]
        | erw [haltGArms_ru]
        | erw [haltE_ru]
        | simp only [haltS, haltB, haltE, Option.elim_some, Option.elim_none])
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) ..
  | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    simp only [ruB, haltS, haltB, haltE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [haltB_ru rest]
        | erw [haltS_nachΛ]
        | erw [haltB_vorΛ]
        | erw [haltE_umΛ]
        | erw [kostenBlock_ru]
        | erw [rufeB_ru]
        | erw [haltS_ru]
        | erw [haltB_ru]
        | erw [haltArms_ru]
        | erw [haltGArms_ru]
        | erw [haltE_ru]
        | simp only [haltS, haltB, haltE, Option.elim_some, Option.elim_none])
    try rfl
termination_by sizeOf b

theorem haltArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) :
    haltArms (D := D.mitRuhe) h ep (fun (g : Option D.Fn) => g.elim 0 c) (fun (g : Option D.Fn) => g.elim false Z) pa (ruArms arms) =
      haltArms h ep c Z pa arms := by
  match arms with
  | .nil => rfl
  | .cons (c := none) b rest | .cons (c := some _) b rest =>
    simp only [ruArms, haltArms]
    erw [haltB_ru b, haltArms_ru rest]
termination_by sizeOf arms

theorem haltGArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) :
    haltGArms (D := D.mitRuhe) h ep (fun (g : Option D.Fn) => g.elim 0 c) (fun (g : Option D.Fn) => g.elim false Z) pa (ruGArms arms) =
      haltGArms h ep c Z pa arms := by
  match arms with
  | .nil => rfl
  | .cons b rest =>
    simp only [ruGArms, haltGArms]
    erw [haltB_ru b, haltGArms_ru rest]
termination_by sizeOf arms

theorem haltE_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    haltE (D := D.mitRuhe) h ep (fun (g : Option D.Fn) => g.elim 0 c) (fun (g : Option D.Fn) => g.elim false Z) pa (ruEnd e) =
      haltE h ep c Z pa e := by
  match e with
  | .ret .. | .retWhy .. | .leave .. | .next .. | .cons .. | .bind .. | .bindCall ..
  | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse ..
  | .awaits .. | .bindCallInd .. | .narrow .. | .exchange .. | .ite .. | .narrowRequired ..
  | .retScoped .. | .retWhyScoped .. | .bindCallIndElse .. | .float .. | .floatLit ..
  | .floatOf .. | .floatNarrow .. =>
    simp only [ruEnd, haltS, haltB, haltE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [haltS_nachΛ]
        | erw [haltB_vorΛ]
        | erw [haltE_umΛ]
        | erw [kostenBlock_ru]
        | erw [rufeB_ru]
        | erw [haltS_ru]
        | erw [haltB_ru]
        | erw [haltArms_ru]
        | erw [haltGArms_ru]
        | erw [haltE_ru]
        | simp only [haltS, haltB, haltE, Option.elim_some, Option.elim_none])
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) ..
  | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    simp only [ruEnd, haltS, haltB, haltE, Option.elim_some, Option.elim_none]
    repeat
      (first
        | erw [haltE_ru rest]
        | erw [haltS_nachΛ]
        | erw [haltB_vorΛ]
        | erw [haltE_umΛ]
        | erw [kostenBlock_ru]
        | erw [rufeB_ru]
        | erw [haltS_ru]
        | erw [haltB_ru]
        | erw [haltArms_ru]
        | erw [haltGArms_ru]
        | erw [haltE_ru]
        | simp only [haltS, haltB, haltE, Option.elim_some, Option.elim_none])
    try rfl
termination_by sizeOf e
end
end Sections
end Gabbro.Grammatik.HaltRuhe
