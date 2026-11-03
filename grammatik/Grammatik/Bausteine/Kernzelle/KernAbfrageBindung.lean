module

public import Grammatik.Bausteine.Kernzelle.KernAbfrage
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil2

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik

variable {D : Deklaration}

variable [DecidableEq D.Ax]

/-! ## 1. Where a body queries the core

    A foreign call carries no call-graph edge (`reachB` cannot see it: a
    foreign body is answered outside the program, and the call itself is the
    trace event `Ereignis.fremd`). So the update-to-query link is not a graph
    round but a direct syntactic fact: the core-query wrapper binds the axiom.
    The traversal below mirrors the generic feature check `mE` case by case
    (`FadenMerkmal.Teil1`), with existence instead of admission: `true` iff
    some `bindAxiom`/`bindAxiomOpt` (plain, `else`, or top-level) of exactly
    `q` occurs. -/

mutual

/-- Some statement binds the core-query axiom. -/
def bindetAxS (q : D.Ax) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => bindetAxB q t || bindetAxB q e
  | .onOption _ p a => bindetAxB q p || bindetAxB q a
  | .onTag _ arms => bindetAxArms q arms
  | .onWhy _ arms => bindetAxGArms q arms
  | .call _ _ _ _ => false
  | .callInd _ _ _ _ => false
  | .locks _ _ body => bindetAxB q body
  | .breaking _ body => bindetAxB q body
  | .traverse _ _ body => bindetAxB q body
  | .consumeTraverse _ _ _ _ _ _ body => bindetAxB q body
  | .retry _ _ body ueber => bindetAxB q body || bindetAxB q ueber
  | .forever _ _ body => bindetAxB q body
  | .assignSlot _ _ _ _ _ _ => false
  | .assignThru _ _ _ _ _ _ _ _ => false
  | .assignGlob _ _ _ _ => false
  | .putBytes _ _ _ _ _ _ _ _ _ _ => false
  | .assignVar _ _ => false
  | .shift _ _ _ _ _ _ _ _ _ _ => false
  | .axiomCall a _ _ _ _ _ _ => decide (a = q)
  | .axiomCallElse _ a _ _ _ _ _ _ err => decide (a = q) || bindetAxE q err
  | .regWrite _ _ _ => false
  | .transition _ _ _ _ _ _ _ => false
  | .publish _ _ _ _ _ _ => false
  | .advances _ _ _ _ => false
  | .retires _ _ _ _ => false
  | .ret _ _ => false
  | .retWhy _ _ => false
  | .retScoped _ _ => false
  | .retWhyScoped _ _ => false
  | .leave _ => false
  | .next _ => false
  | .assignSlotRef _ _ _ _ _ _ _ _ => false
  | .callIndElse _ _ _ _ _ err => bindetAxE q err

/-- Some block binds the core-query axiom. -/
def bindetAxB (q : D.Ax) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => false
  | .cons s rest => bindetAxS q s || bindetAxB q rest
  | .bind _ rest => bindetAxB q rest
  | .bindCall _ _ _ _ _ rest => bindetAxB q rest
  | .bindCallInd _ _ _ _ _ rest => bindetAxB q rest
  | .bindCallIndElse _ _ _ _ _ err rest =>
      bindetAxE q err || bindetAxB q rest
  | .bindCallElse _ _ _ _ _ err rest => bindetAxE q err || bindetAxB q rest
  | .bindAxiom a _ _ _ _ _ _ rest => decide (a = q) || bindetAxB q rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxB q rest
  | .bindAxiomOpt _ a _ _ _ _ _ rest => decide (a = q) || bindetAxB q rest
  | .bindAxiomOptElse _ a _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxB q rest
  | .regRead _ _ rest => bindetAxB q rest
  | .regReadElse _ _ _ sonst rest => bindetAxE q sonst || bindetAxB q rest
  | .awaits _ _ _ _ _ rest => bindetAxB q rest
  | .exchange _ _ _ _ rest => bindetAxB q rest
  | .narrow _ _ _ sonst rest => bindetAxE q sonst || bindetAxB q rest
  | .narrowRequired _ _ _ rest => bindetAxB q rest
  | .check _ sonst rest => bindetAxE q sonst || bindetAxB q rest
  | .float _ _ _ _ rest => bindetAxB q rest
  | .floatLit _ _ rest => bindetAxB q rest
  | .floatOf _ _ rest => bindetAxB q rest
  | .floatNarrow _ _ _ sonst rest => bindetAxE q sonst || bindetAxB q rest

/-- Some tagged arm binds the core-query axiom. -/
def bindetAxArms (q : D.Ax) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => false
  | .cons b rest => bindetAxB q b || bindetAxArms q rest

/-- Some reason arm binds the core-query axiom. -/
def bindetAxGArms (q : D.Ax) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => false
  | .cons b rest => bindetAxB q b || bindetAxGArms q rest

/-- Some top-level body binds the core-query axiom. -/
def bindetAxE (q : D.Ax) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret _ _ => false
  | .retWhy _ _ => false
  | .retScoped _ _ => false
  | .retWhyScoped _ _ => false
  | .leave _ => false
  | .next _ => false
  | .cons s rest => bindetAxS q s || bindetAxE q rest
  | .bind _ rest => bindetAxE q rest
  | .bindCall _ _ _ _ _ rest => bindetAxE q rest
  | .bindCallElse _ _ _ _ _ err rest => bindetAxE q err || bindetAxE q rest
  | .bindAxiom a _ _ _ _ _ _ rest => decide (a = q) || bindetAxE q rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxE q rest
  | .bindAxiomOpt _ a _ _ _ _ _ rest => decide (a = q) || bindetAxE q rest
  | .bindAxiomOptElse _ a _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxE q rest
  | .regRead _ _ rest => bindetAxE q rest
  | .regReadElse _ _ _ sonst rest => bindetAxE q sonst || bindetAxE q rest
  | .awaits _ _ _ _ _ rest => bindetAxE q rest
  | .bindCallInd _ _ _ _ _ rest => bindetAxE q rest
  | .bindCallIndElse _ _ _ _ _ err rest => bindetAxE q err || bindetAxE q rest
  | .narrow _ _ _ sonst rest => bindetAxE q sonst || bindetAxE q rest
  | .narrowRequired _ _ _ rest => bindetAxE q rest
  | .exchange _ _ _ rest => bindetAxE q rest
  | .ite _ t e => bindetAxE q t || bindetAxE q e

end

/-! ## 2. The connected query

    The wrapper (`a.kernAbfrage`, already admitted by `akkuZulaessig` with
    its exact shape and the update's call edge) binds the hardware axiom
    through the C08 foreign-call path. Together with the shape and the
    provenance, this is the checked core identity: the update's queried core
    is the running core under the declared assignment, with no unproved
    hardware assumption beyond the named `AxVertragO` ensures on the answer. -/

/-- **The connected core query**: the shape, the hardware provenance and the
    wrapper's foreign bind. -/
def KernAbfrageVerbunden (P : Programm D) (a : AccumulatorDecl D) (q : D.Ax) : Prop :=
  KernAbfrageGestalt D q a.kernZahl ∧ KernAbfrageHerkunft D q ∧
    bindetAxE q (P.rumpf a.kernAbfrage) = true

/-- The connected query, decided over the member lists. -/
def kernAbfrageEinzelB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob)
    (a : AccumulatorDecl D) (q : D.Ax) : Bool :=
  kernAbfrageGestaltB D q a.kernZahl tabs globs &&
  kernAbfrageHerkunftB D q &&
  bindetAxE q (P.rumpf a.kernAbfrage)

/-- The Bool decides the connected query. -/
theorem kernAbfrageEinzelB_iff {P : Programm D} {tabs : List D.Tab}
    {globs : List D.Glob} {a : AccumulatorDecl D} {q : D.Ax}
    (hT : ∀ t : D.Tab, t ∈ tabs) (hG : ∀ g : D.Glob, g ∈ globs) :
    kernAbfrageEinzelB P tabs globs a q = true ↔ KernAbfrageVerbunden P a q := by
  unfold kernAbfrageEinzelB KernAbfrageVerbunden
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(kernAbfrageGestaltB_iff hT hG).mp h1,
      (kernAbfrageHerkunftB_iff).mp h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(kernAbfrageGestaltB_iff hT hG).mpr h1,
      (kernAbfrageHerkunftB_iff).mpr h2, h3⟩

/-- The Bool decides the connected query. -/
theorem kernAbfrageEinzelB_iff {P : Programm D} {tabs : List D.Tab}
    {globs : List D.Glob} {a : AccumulatorDecl D} {q : D.Ax}
    (hT : ∀ t : D.Tab, t ∈ tabs) (hG : ∀ g : D.Glob, g ∈ globs) :
    kernAbfrageEinzelB P tabs globs a q = true ↔ KernAbfrageVerbunden P a q := by
  unfold kernAbfrageEinzelB KernAbfrageVerbunden
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(kernAbfrageGestaltB_iff hT hG).mp h1,
      (kernAbfrageHerkunftB_iff).mp h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(kernAbfrageGestaltB_iff hT hG).mpr h1,
      (kernAbfrageHerkunftB_iff).mpr h2, h3⟩

#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageEinzelB_iff

/-! ## 3. Transfer to the idle-root program

    The wrapper's foreign bind rides the body translation: `ruS`/`ruB`/`ruEnd`
    map every binding constructor to itself with the same axiom, and the
    holding casts (`nachΛ`/`vorΛ`/`umΛ`) change nothing observable. The shape
    and provenance ride the declaration, whose foreign fields the idle root
    keeps (`aparams`/`aerg` shifted by `tyR`, which fixes `int`). -/

/-- The `Ax` equality on the idle-root program rides the declaration's. -/
instance : DecidableEq (D.mitRuhe).Ax := inferInstanceAs (DecidableEq D.Ax)

/-- Casts change no binding observation. -/
theorem bindetAxS_nachΛ {E : Deklaration} [DecidableEq E.Ax] {V : Vertrag E}
    {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res E)} (q : E.Ax)
    (h : Λ₁ = Λ₂) (s : Stmt E V l Γ Λ Λ₁) :
    bindetAxS q (Stmt.nachΛ h s) = bindetAxS q s := by
  cases h
  rfl

/-- Casts change no binding observation. -/
theorem bindetAxB_vorΛ {E : Deklaration} [DecidableEq E.Ax] {V : Vertrag E}
    {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res E)} (q : E.Ax)
    (h : Λ₁ = Λ₂) (b : Block E V l Γ Λ₁ Λ') :
    bindetAxB q (Block.vorΛ h b) = bindetAxB q b := by
  cases h
  rfl

/-- Casts change no binding observation. -/
theorem bindetAxE_umΛ {E : Deklaration} [DecidableEq E.Ax] {V : Vertrag E}
    {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res E)} (q : E.Ax)
    (h : Λ₁ = Λ₂) (e : Endblock E V l Γ Λ₁) :
    bindetAxE q (Endblock.umΛ h e) = bindetAxE q e := by
  cases h
  rfl

mutual

/-- The body translation keeps the binding observation on statements. -/
theorem ruS_bindetAx {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (q : D.Ax),
    bindetAxS (D := D.mitRuhe) q (ruS s) = bindetAxS q s
  | _, _, _, _, .assignSlot .., _ => rfl
  | _, _, _, _, .assignThru .., _ => rfl
  | _, _, _, _, .assignSlotRef .., _ => rfl
  | _, _, _, _, .assignGlob .., _ => rfl
  | _, _, _, _, .putBytes .., _ => rfl
  | _, _, _, _, .assignVar .., _ => rfl
  | _, _, _, _, .shift .., _ => rfl
  | _, _, _, _, .ite _ t e, _ => kongr₂ (· || ·) (ruB_bindetAx t _) (ruB_bindetAx e _)
  | _, _, _, _, .onOption _ p a, _ => kongr₂ (· || ·) (ruB_bindetAx p _) (ruB_bindetAx a _)
  | _, _, _, _, .onTag _ arms, _ => ruArms_bindetAx arms _
  | _, _, _, _, .onWhy _ arms, _ => ruGArms_bindetAx arms _
  | _, _, _, _, .call .., _ => (bindetAxS_nachΛ _ _ _).trans rfl
  | _, _, _, _, .callInd .., _ => (bindetAxS_nachΛ _ _ _).trans rfl
  | _, _, _, _, .callIndElse _ _ _ _ _ _ err, _ =>
      (bindetAxS_nachΛ _ _ _).trans ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE err _))
  | _, _, _, _, .locks _ _ body, _ => ruB_bindetAx body _
  | _, _, _, _, .breaking _ body, _ => ruB_bindetAx body _
  | _, _, _, _, .traverse _ _ body, _ => ruB_bindetAx body _
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body, _ => ruB_bindetAx body _
  | _, _, _, _, .retry _ _ body ueber, _ => kongr₂ (· || ·) (ruB_bindetAx body _) (ruB_bindetAx ueber _)
  | _, _, _, _, .forever _ _ body, _ => ruB_bindetAx body _
  | _, _, _, _, .axiomCall .., _ => rfl
  | _, _, _, _, .axiomCallElse .., _ =>
      (bindetAxS_nachΛ _ _ _).trans
        (kongr₂ (· || ·) rfl ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE _ _)))
  | _, _, _, _, .regWrite .., _ => rfl
  | _, _, _, _, .transition .., _ => rfl
  | _, _, _, _, .publish .., _ => rfl
  | _, _, _, _, .advances .., _ => (bindetAxS_nachΛ _ _ _).trans rfl
  | _, _, _, _, .retires .., _ => (bindetAxS_nachΛ _ _ _).trans rfl
  | _, _, _, _, .ret .., _ => rfl
  | _, _, _, _, .retWhy .., _ => rfl
  | _, _, _, _, .retScoped .., _ => rfl
  | _, _, _, _, .retWhyScoped .., _ => rfl
  | _, _, _, _, .leave _, _ => rfl
  | _, _, _, _, .next _, _ => rfl

/-- The body translation keeps the binding observation on blocks. -/
theorem ruB_bindetAx {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (q : D.Ax),
    bindetAxB (D := D.mitRuhe) q (ruB b) = bindetAxB q b
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .cons s rest, _ => kongr₂ (· || ·) (ruS_bindetAx s _) (ruB_bindetAx rest _)
  | _, _, _, _, .bind _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .bindCall _ _ _ _ _ rest, _ =>
      (bindetAxB_vorΛ _ _ _).trans (ruB_bindetAx rest _)
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest, _ =>
      (bindetAxB_vorΛ _ _ _).trans (ruB_bindetAx rest _)
  | _, _, _, _, .bindCallIndElse _ _ _ _ _ _ err rest, _ =>
      kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE err _))
        ((bindetAxB_vorΛ _ _ _).trans (ruB_bindetAx rest _))
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest, _ =>
      kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE err _))
        ((bindetAxB_vorΛ _ _ _).trans (ruB_bindetAx rest _))
  | _, _, _, _, .bindAxiom a _ _ _ _ _ _ rest, _ =>
      kongr₂ (· || ·) rfl (ruB_bindetAx rest _)
  | _, _, _, _, .bindAxiomElse a _ _ _ _ _ _ _ err rest, _ =>
      kongr₂ (· || ·) rfl (kongr₂ (· || ·) (ruEnd_bindetAxE err _) (ruB_bindetAx rest _))
  | _, _, _, _, .bindAxiomOpt e a _ _ _ _ _ rest, _ => by
      have ih1 := ruB_bindetAx (V := V) rest q
      cases e with
      | none =>
          simp only [ruB, bindetAxB]
          exact kongr₂ (· || ·) rfl ((bindetAxB_vorΛ _ _ _).trans ih1)
      | some _ =>
          simp only [ruB, bindetAxB]
          exact kongr₂ (· || ·) rfl ((bindetAxB_vorΛ _ _ _).trans ih1)
  | _, _, _, _, .bindAxiomOptElse e a _ _ _ _ _ _ err rest, _ => by
      have ih0 := ruEnd_bindetAxE (V := V) err q
      have ih1 := ruB_bindetAx (V := V) rest q
      cases e with
      | none =>
          simp only [ruB, bindetAxB]
          exact kongr₂ (· || ·) rfl
            (kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans ih0)
              ((bindetAxB_vorΛ _ _ _).trans ih1))
      | some _ =>
          simp only [ruB, bindetAxB]
          exact kongr₂ (· || ·) rfl
            (kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans ih0)
              ((bindetAxB_vorΛ _ _ _).trans ih1))
  | _, _, _, _, .regRead _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .regReadElse _ _ _ sonst rest, _ =>
      kongr₂ (· || ·) (ruEnd_bindetAxE sonst _) (ruB_bindetAx rest _)
  | _, _, _, _, .awaits _ _ _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .exchange _ _ _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .narrow _ _ _ sonst rest, _ =>
      kongr₂ (· || ·) (ruEnd_bindetAxE sonst _) (ruB_bindetAx rest _)
  | _, _, _, _, .narrowRequired _ _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .check _ sonst rest, _ =>
      kongr₂ (· || ·) (ruEnd_bindetAxE sonst _) (ruB_bindetAx rest _)
  | _, _, _, _, .float _ _ _ _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .floatLit _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .floatOf _ _ rest, _ => ruB_bindetAx rest _
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, _ =>
      kongr₂ (· || ·) (ruEnd_bindetAxE sonst _) (ruB_bindetAx rest _)

/-- The body translation keeps the binding observation on end blocks. -/
theorem ruEnd_bindetAxE {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (q : D.Ax),
    bindetAxE (D := D.mitRuhe) q (ruEnd e) = bindetAxE q e
  | _, _, _, .ret .., _ => rfl
  | _, _, _, .retWhy .., _ => rfl
  | _, _, _, .retScoped .., _ => rfl
  | _, _, _, .retWhyScoped .., _ => rfl
  | _, _, _, .leave _, _ => rfl
  | _, _, _, .next _, _ => rfl
  | _, _, _, .cons s rest, _ => kongr₂ (· || ·) (ruS_bindetAx s _) (ruEnd_bindetAxE rest _)
  | _, _, _, .bind _ rest, _ => ruEnd_bindetAxE rest _
  | _, _, _, .bindCall _ _ _ _ _ rest, _ =>
      (bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE rest _)
  | _, _, _, .bindCallElse _ _ _ _ _ err rest, _ =>
      kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE err _))
        ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE rest _))
  | _, _, _, .bindAxiom a _ _ _ _ _ _ rest, _ =>
      kongr₂ (· || ·) rfl (ruEnd_bindetAxE rest _)
  | _, _, _, .bindAxiomElse a _ _ _ _ _ _ _ err rest, _ =>
      kongr₂ (· || ·) rfl (kongr₂ (· || ·) (ruEnd_bindetAxE err _) (ruEnd_bindetAxE rest _))
  | _, _, _, .bindAxiomOpt e a _ _ _ _ _ rest, _ => by
      have ih1 := ruEnd_bindetAxE (V := V) rest q
      cases e with
      | none =>
          simp only [ruEnd, bindetAxE]
          exact kongr₂ (· || ·) rfl ((bindetAxE_umΛ _ _ _).trans ih1)
      | some _ =>
          simp only [ruEnd, bindetAxE]
          exact kongr₂ (· || ·) rfl ((bindetAxE_umΛ _ _ _).trans ih1)
  | _, _, _, .bindAxiomOptElse e a _ _ _ _ _ _ err rest, _ => by
      have ih0 := ruEnd_bindetAxE (V := V) err q
      have ih1 := ruEnd_bindetAxE (V := V) rest q
      cases e with
      | none =>
          simp only [ruEnd, bindetAxE]
          exact kongr₂ (· || ·) rfl
            (kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans ih0)
              ((bindetAxE_umΛ _ _ _).trans ih1))
      | some _ =>
          simp only [ruEnd, bindetAxE]
          exact kongr₂ (· || ·) rfl
            (kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans ih0)
              ((bindetAxE_umΛ _ _ _).trans ih1))
  | _, _, _, .regRead _ _ rest, _ => ruEnd_bindetAxE rest _
  | _, _, _, .regReadElse _ _ _ sonst rest, _ =>
      kongr₂ (· || ·) (ruEnd_bindetAxE sonst _) (ruEnd_bindetAxE rest _)
  | _, _, _, .awaits _ _ _ _ _ rest, _ => ruEnd_bindetAxE rest _
  | _, _, _, .bindCallInd _ _ _ _ _ rest, _ =>
      (bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE rest _)
  | _, _, _, .bindCallIndElse _ _ _ _ _ _ err rest, _ =>
      kongr₂ (· || ·) ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE err _))
        ((bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE rest _))
  | _, _, _, .narrow _ _ _ sonst rest, _ =>
      kongr₂ (· || ·) (ruEnd_bindetAxE sonst _) (ruEnd_bindetAxE rest _)
  | _, _, _, .narrowRequired _ _ _ rest, _ => ruEnd_bindetAxE rest _
  | _, _, _, .exchange _ _ _ rest, _ => ruEnd_bindetAxE rest _
  | _, _, _, .ite _ t e, _ => kongr₂ (· || ·) (ruEnd_bindetAxE t _) (ruEnd_bindetAxE e _)

/-- The body translation keeps the binding observation on tagged arms. -/
theorem ruArms_bindetAx {V : vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) (q : D.Ax),
    bindetAxArms (D := D.mitRuhe) q (ruArms arms) = bindetAxArms q arms
  | _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, .cons b rest, _ => kongr₂ (· || ·) (ruB_bindetAx b _) (ruArms_bindetAx rest _)

/-- The body translation keeps the binding observation on reason arms. -/
theorem ruGArms_bindetAx {V : vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (q : D.Ax),
    bindetAxGArms (D := D.mitRuhe) q (ruGArms arms) = bindetAxGArms q arms
  | _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, .cons b rest, _ => kongr₂ (· || ·) (ruB_bindetAx b _) (ruGArms_bindetAx rest _)

end

/-- The wrapper's foreign bind rides the idle-root translation. -/
theorem bindetAxE_mitRuhe (P : Programm D) (f : D.Fn) (q : D.Ax) :
    bindetAxE (D := D.mitRuhe) q (P.mitRuhe.rumpf (some f)) = bindetAxE q (P.rumpf f) :=
  (bindetAxE_umΛ _ _ _).trans (ruEnd_bindetAxE _ _)

/-- The core-query shape rides the idle-root declaration. -/
theorem kernAbfrageGestalt_mitRuhe {q : D.Ax} {N : Nat}
    (h : KernAbfrageGestalt D q N) : KernAbfrageGestalt D.mitRuhe q N := by
  obtain ⟨hN, hP, hE, hR, hW, hGs⟩ := h
  refine ⟨hN, ?_, ?_, hR, hW, hGs⟩
  · show (D.aparams q).map tyR = []
    rw [hP]
    rfl
  · show (D.aerg q).map tyR = some (Ty.int 0 ((N : Int) - 1))
    rw [hE]
    rfl

/-- The core-query provenance rides the idle-root declaration (identical fields). -/
theorem kernAbfrageHerkunft_mitRuhe {q : D.Ax}
    (h : KernAbfrageHerkunft D q) : KernAbfrageHerkunft D.mitRuhe q :=
  h

/-- The connected query rides the idle-root program. -/
theorem kernAbfrageVerbunden_mitRuhe (P : Programm D) {a : AccumulatorDecl D}
    {q : D.Ax} (h : KernAbfrageVerbunden P a q) :
    KernAbfrageVerbunden P.mitRuhe (AccumulatorDecl.mitRuhe a) q := by
  obtain ⟨hG, hH, hB⟩ := h
  refine ⟨kernAbfrageGestalt_mitRuhe hG, kernAbfrageHerkunft_mitRuhe hH, ?_⟩
  show bindetAxE q (P.mitRuhe.rumpf (some a.kernAbfrage)) = true
  rw [bindetAxE_mitRuhe P a.kernAbfrage q]
  exact hB

#print axioms Gabbro.Grammatik.Kernzelle.bindetAxE_mitRuhe
#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageGestalt_mitRuhe
#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageHerkunft_mitRuhe
#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageVerbunden_mitRuhe

end Gabbro.Grammatik.Kernzelle
