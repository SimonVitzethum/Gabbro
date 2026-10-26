/-
  File:      stage0/Stage0/Schritt/Geraet.lean
  Subject:   The executable step, part 8: leaves (`blatt`, `dannBlatt`), bindings at the head of an end block
             (`endeBind`), foreign calls (`*BindAxiom*`, whose answer world keeps the trace: `OrakelSpurTreu`),
             register reads, `awaits`, `exchange` and the float forms. A register read whose value breaks the
             device's promise, a float outside its range without `else`, a foreign call without an answer: no
             step (the machine stops, as in the model).
-/
import Stage0.Schritt.Blatt

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- A leaf at the head of an end block. -/
def zugBlattEnde (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (ρ : Env D Γ) (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩) : Option (Zug P O passes M f) :=
  if hleaf : s.istBlatt = true then
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      match hst : execStmt O passes keinRuf s (M.weltVon f) ρ with
      | .ok σ' ρ' =>
        have he := erw_neu (blatt_erw hO passes s hleaf _ _ _ _ hst)
        some ⟨_, .blatt M f l Γ Λ Λ' s rest ρ hleaf hk (heldIn_of hΛ) σ' ρ' _ hst he.1 he.2,
          _, blatt_schreib hsw passes keinRuf s hleaf _ ρ hst⟩
      | _ => none
    else none
  else none

/-- A leaf at the head of a `dann` block. -/
def zugBlattDann (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx}
    {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ) (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩) : Option (Zug P O passes M f) :=
  if hleaf : s.istBlatt = true then
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      match hst : execStmt O passes keinRuf s (M.weltVon f) ρ with
      | .ok σ' ρ' =>
        have he := erw_neu (blatt_erw hO passes s hleaf _ _ _ _ hst)
        some ⟨_, .dannBlatt M f l Γ Λ Λ' Λ'' s rest k ρ hleaf hk (heldIn_of hΛ) σ' ρ' _ hst he.1 he.2,
          _, blatt_schreib hsw passes keinRuf s hleaf _ ρ hst⟩
      | _ => none
    else none
  else none

/-- The trace after a foreign call: its question on top of the reads. -/
theorem ax_neu {O : Orakel D} (hO : OrakelSpurTreu O) (M : RufMaschineG D) (f : Faden) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) (a : D.Ax) (ρa : Env D (D.aparams a)) {σ₂ : World D} {x : Option (ErgVal D (D.aerg a))}
    (hax : axiomAntwort O a ((M.weltVon f).lese Λ os) ρa = (σ₂, x)) :
    σ₂.spur = (.fremd (.inl a) :: leseEv (M.weltVon f) Λ os) ++ (M.faeden f).spur := by
  have h := axiomAntwort_spur hO a ((M.weltVon f).lese Λ os) ρa
  rw [hax] at h
  rw [h, lese_neu]
  rfl

theorem axS_neu {O : Orakel D} (hO : OrakelSpurTreu O) (M : RufMaschineG D) (f : Faden) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) (a : D.Ax) (ρa : Env D (D.aparams a)) {σ₂ : World D}
    {x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hax : axiomAntwortSonst O a ((M.weltVon f).lese Λ os) ρa = (σ₂, x)) :
    σ₂.spur = (.fremd (.inl a) :: leseEv (M.weltVon f) Λ os) ++ (M.faeden f).spur := by
  have h := axiomAntwortSonst_spur hO a ((M.weltVon f).lese Λ os) ρa
  rw [hax] at h
  rw [h, lese_neu]
  rfl

/-- `let x = e;` at the head of an end block. -/
def zugEndeBind (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (ρ : Env D Γ)
    (e : Expr D Γ Λ τ) (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bind e rest)⟩) : Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    some ⟨_, .endeBind M f l Γ Λ τ e rest ρ hk _ rfl _ (lese_neu M f Λ e.orte) (heldIn_of hΛ), [], rfl⟩
  else none

/-- `let x = a(args);` of a foreign body at the head of an end block. -/
def zugEndeAx (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (ρ : Env D Γ) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bindAxiom a args he hw hg hd hgd rest)⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let σ₁ := (M.weltVon f).lese Λ args.orte
    match hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
    | (σ₂, some v) =>
      some ⟨_, .endeBindAxiom M f l Γ Λ τ a args he hw hg hd hgd rest ρ hk σ₁ rfl σ₂ v hax _
        (ax_neu hO M f Λ args.orte a _ hax) (heldIn_of hΛ), _, axiom_schreib hsw hax⟩
    | (_, none) => none
  else none

/-- `let x = a(args) else (e) { … }` of a fallible foreign body at the head of an end block. -/
def zugEndeAxSonst (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty} (ρ : Env D Γ) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ) (hr : 0 < D.agruende a)
    (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
    (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let σ₁ := (M.weltVon f).lese Λ args.orte
    match hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
    | (σ₂, some (.inl v)) =>
      some ⟨_, .endeBindAxiomElseOk M f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hk σ₁ rfl σ₂ v hax _
        (axS_neu hO M f Λ args.orte a _ hax) (heldIn_of hΛ), _, axiomSonst_schreib hsw hax⟩
    | (σ₂, some (.inr r)) =>
      some ⟨_, .endeBindAxiomElseGrund M f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hk σ₁ rfl σ₂ r hax _
        (axS_neu hO M f Λ args.orte a _ hax) (heldIn_of hΛ), _, axiomSonst_schreib hsw hax⟩
    | (_, none) => none
  else none

/-- **The device, atomic, foreign-call and float forms at the head of a `dann` block.** -/
def zugDannGeraet (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (ρ : Env D Γ) (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann b k⟩) : Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    match b, hk with
    | .bindAxiom (τ := τ) a args he hw hg hd hgd rest, hk =>
      let σ₁ := (M.weltVon f).lese Λ args.orte
      match hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some v) =>
        some ⟨_, .dannBindAxiom M f l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hk σ₁ rfl σ₂ v hax _
          (ax_neu hO M f Λ args.orte a _ hax) (heldIn_of hΛ), _, axiom_schreib hsw hax⟩
      | (_, none) => none
    | .bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest, hk =>
      let σ₁ := (M.weltVon f).lese Λ args.orte
      match hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some (.inl v)) =>
        some ⟨_, .dannBindAxiomElseOk M f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hk σ₁ rfl σ₂ v hax _
          (axS_neu hO M f Λ args.orte a _ hax) (heldIn_of hΛ), _, axiomSonst_schreib hsw hax⟩
      | (σ₂, some (.inr r)) =>
        some ⟨_, .dannBindAxiomElseGrund M f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hk σ₁ rfl σ₂ r hax _
          (axS_neu hO M f Λ args.orte a _ hax) (heldIn_of hΛ), _, axiomSonst_schreib hsw hax⟩
      | (_, none) => none
    | .regRead r hkl rest, hk =>
      match hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) with
      | some v =>
        if hz : D.rzusage r v = true then
          some ⟨_, .dannRegLies M f l Γ Λ Λ' r hkl rest k ρ hk v hv hz (heldIn_of hΛ), [], rfl⟩
        else none
      | none => none
    | .regReadElse r hkl zusage sonst rest, hk =>
      match hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) with
      | some v =>
        let σ₁ := ((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte
        if hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = true then
          some ⟨_, .dannRegLiesElseWahr M f l Γ Λ Λ' r hkl zusage sonst rest k ρ hk v hv σ₁ rfl hw
            (leseEv ((M.weltVon f).fragt (.inr (.inl r))) Λ zusage.orte ++ [.fremd (.inr (.inl r))])
            (by rw [lese_spur, List.append_assoc]; rfl) (heldIn_of hΛ), [], rfl⟩
        else
          some ⟨_, .dannRegLiesElseFalsch M f l Γ Λ Λ' r hkl zusage sonst rest k ρ hk v hv σ₁ rfl
            (by simpa using hw) (leseEv ((M.weltVon f).fragt (.inr (.inl r))) Λ zusage.orte ++ [.fremd (.inr (.inl r))])
            (by rw [lese_spur, List.append_assoc]; rfl)
            (heldIn_of hΛ), [], rfl⟩
      | none => none
    | .awaits g payload hp hL hat rest, hk =>
      if hvis : O.sichtbar g ((M.weltVon f).fragt (.inr (.inr g))) = true then
        some ⟨_, .dannAwaits M f l Γ Λ Λ' g payload hp hL hat rest k ρ hk hvis _ rfl
          (leseEv _ Λ [.inr g] ++ [.fremd (.inr (.inr g))]) (by rw [lese_spur]; rfl) (heldIn_of hΛ), [], rfl⟩
      else none
    | .exchange g neuE hw hL rest, hk =>
      let σ₁ := (M.weltVon f).lese Λ (.inr g :: neuE.orte)
      some ⟨_, .dannExchange M f l Γ Λ Λ' g neuE hw hL rest k ρ hk σ₁ rfl _ rfl
        (.gzugriff g true Λ σ₁.haelt :: leseEv (M.weltVon f) Λ (.inr g :: neuE.orte)) rfl (heldIn_of hΛ),
        [.glob g (eval σ₁ neuE σ₁ (.cons (σ₁.globs g) ρ))], rfl⟩
    | .float (l1 := l₁) (h1 := h₁) (l2 := l₂) (h2 := h₂) op a b lo hi rest, hk =>
      let σ₁ := (M.weltVon f).lese Λ (a.orte ++ b.orte)
      match hv : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
      | some v =>
        some ⟨_, .dannGleit M f l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hk σ₁ rfl v hv _
          (lese_neu M f Λ (a.orte ++ b.orte)) (heldIn_of hΛ), [], rfl⟩
      | none => none
    | .floatLit q lo hi rest, hk =>
      match hv : gleitPasst lo hi (bruch q) with
      | some v => some ⟨_, .dannGleitLit M f l Γ Λ Λ' q lo hi rest k ρ hk v hv, [], rfl⟩
      | none => none
    | .floatOf (l1 := l₁) (h1 := h₁) e lo hi rest, hk =>
      let σ₁ := (M.weltVon f).lese Λ e.orte
      match hv : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
      | some v =>
        some ⟨_, .dannGleitVon M f l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hk σ₁ rfl v hv _ (lese_neu M f Λ e.orte)
          (heldIn_of hΛ), [], rfl⟩
      | none => none
    | .floatNarrow (l1 := l₁) (h1 := h₁) e lo hi sonst rest, hk =>
      let σ₁ := (M.weltVon f).lese Λ e.orte
      match hv : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
      | some v =>
        some ⟨_, .dannGleitNarrowOk M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hk σ₁ rfl v hv _
          (lese_neu M f Λ e.orte) (heldIn_of hΛ), [], rfl⟩
      | none =>
        some ⟨_, .dannGleitNarrowElse M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hk σ₁ rfl hv _
          (lese_neu M f Λ e.orte) (heldIn_of hΛ), [], rfl⟩
    | _, _ => none
  else none

end Gabbro.Stage0
