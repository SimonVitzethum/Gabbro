/-
  File:      stage0/Stage0/Schritt/Schreib.lean
  Subject:   **What a step writes.** A list of cell and static writes (`Schreib`), applied to a memory exactly as the
             semantics writes (`storeSlot`, `storeGlob`). `blattSchreib`: the writes of a leaf statement, and
             `blatt_schreib`: the memory a leaf leaves is its memory with these writes. A foreign body's writes are
             the oracle's (`OrakelSchreibt`). The fast machine applies the writes of a step to its arrays in place.
-/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **One write**: a cell, or a static. -/
inductive Schreib (D : Deklaration) where
  | slot (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
  | glob (g : D.Glob) (v : Wert D (D.gtyp g))

/-- One write applied to a memory, as the semantics writes. -/
def Schreib.auf : Schreib D → Speicher D → Speicher D
  | .slot t k f v, S => ((S.welt []).storeSlot t k f v).speicher
  | .glob g v, S => ((S.welt []).storeGlob g v).speicher

/-- Writes applied in order. -/
def schreibAuf (w : List (Schreib D)) (S : Speicher D) : Speicher D := w.foldl (fun S s => s.auf S) S

theorem schreibAuf_append (w w' : List (Schreib D)) (S : Speicher D) :
    schreibAuf (w ++ w') S = schreibAuf w' (schreibAuf w S) := by
  simp [schreibAuf, List.foldl_append]

/-- **An oracle whose answers name their writes.** -/
def OrakelSchreibt (O : Orakel D) (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) : Prop :=
  ∀ a σ ρ, (O.wirkt a σ ρ).1.speicher = schreibAuf (ow a σ ρ) σ.speicher

theorem axiom_schreib {O : Orakel D} {ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)}
    (hsw : OrakelSchreibt O ow) {a : D.Ax} {σ σ₂ : World D} {ρ : Env D (D.aparams a)}
    {x : Option (ErgVal D (D.aerg a))} (hax : axiomAntwort O a σ ρ = (σ₂, x)) :
    σ₂.speicher = schreibAuf (ow a (σ.fragt (.inl a)) ρ) σ.speicher := by
  have h := congrArg Prod.fst hax
  simp only [axiomAntwort] at h
  rw [← h]
  exact hsw _ _ _

theorem axiomSonst_schreib {O : Orakel D} {ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)}
    (hsw : OrakelSchreibt O ow) {a : D.Ax} {σ σ₂ : World D} {ρ : Env D (D.aparams a)}
    {x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))} (hax : axiomAntwortSonst O a σ ρ = (σ₂, x)) :
    σ₂.speicher = schreibAuf (ow a (σ.fragt (.inl a)) ρ) σ.speicher := by
  have h := congrArg Prod.fst hax
  simp only [axiomAntwortSonst] at h
  rw [← h]
  exact hsw _ _ _

/-- The writes of `schreibBytes`. -/
def bytesSchreib (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) : Int → List Byte → List (Schreib D)
  | _, [] => []
  | k, b :: bs => .slot t k f (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255))) :: bytesSchreib t f hf (k + 1) bs

/-- **The writes of a leaf.** -/
def blattSchreib (O : Orakel D) (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D))
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → World D → Env D Γ → List (Schreib D)
  | .assignSlot t f i e _ _, σ, ρ =>
    let σ := σ.lese Λ (i.orte ++ e.orte)
    [.slot t (eval σ i σ ρ).n f (eval σ e σ ρ)]
  | .assignThru p t _ f i e _ _, σ, ρ =>
    let σ := σ.lese Λ (p.orte ++ i.orte ++ e.orte)
    [.slot t (eval σ i σ ρ).n f (eval σ e σ ρ)]
  | .assignSlotRef r t _ _ f e _ _, σ, ρ =>
    let σ := σ.lese Λ (r.orte ++ e.orte)
    [.slot t ((eval σ r σ ρ).zelle : Int) f (eval σ e σ ρ)]
  | .assignGlob g e _ _, σ, ρ =>
    let σ := σ.lese Λ e.orte
    [.glob g (eval σ e σ ρ)]
  | .putBytes t f hf n i _ _ e _ _, σ, ρ =>
    let σ := σ.lese Λ (i.orte ++ e.orte)
    bytesSchreib t f hf (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)
  | .shift t f hτ i von nach hn _ _ _, σ, ρ =>
    let σ := σ.lese Λ (.inl t :: i.orte)
    let k := (eval σ i σ ρ).n
    if (hτ ▸ σ.slots t k f : Zahl _ _).n = von then [.slot t k f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))] else []
  | .axiomCall a args _ _ _ _ _, σ, ρ =>
    let σ := σ.lese Λ args.orte
    ow a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)
  | .publish g e _ _ _ _, σ, ρ =>
    let σ := σ.lese Λ e.orte
    [.glob g (eval σ e σ ρ)]
  | _, _, _ => []

theorem schreibBytes_speicher (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) :
    ∀ (bs : List Byte) (k : Int) (σ : World D),
      (σ.schreibBytes t f hf Λ k bs).speicher = schreibAuf (bytesSchreib t f hf k bs) σ.speicher
  | [], _, _ => rfl
  | b :: bs, k, σ => by
    simp only [World.schreibBytes, bytesSchreib]
    rw [schreibBytes_speicher t f hf Λ bs (k + 1)]
    rfl

/-- **A leaf writes what `blattSchreib` names.** -/
theorem blatt_schreib {O : Orakel D} {ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)}
    (hw : OrakelSchreibt O ow) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true → ∀ (σ : World D) (ρ : Env D Γ) {σ' : World D} {ρ' : Env D Γ},
      execStmt O passes R s σ ρ = .ok σ' ρ' → σ'.speicher = schreibAuf (blattSchreib O ow s σ ρ) σ.speicher
  | .assignSlot .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .assignThru .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .assignSlotRef .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .assignGlob .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .putBytes t f hf n i _ _ e _ _, _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact schreibBytes_speicher t f hf Λ _ _ _
  | .assignVar .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .shift .., _, σ, ρ, _, _, h => by
    simp only [execStmt] at h
    simp only [blattSchreib]
    split at h
    · simp only [Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (by assumption)]
      rfl
    · cases h
  | .axiomCall a args .., _, σ, ρ, _, _, h => by
    simp only [execStmt] at h
    split at h
    · rename_i σ'' v hax
      simp only [Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : (axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 = σ'' := by
        rw [hax]
      rw [← h1]
      exact hw _ _ _
    · cases h
  | .regWrite .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .transition .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .publish .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .advances .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .retires .., _, σ, ρ, _, _, h => by
    simp only [execStmt, Ausgang.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .ret .., _, _, _, _, _, h => by simp [execStmt] at h
  | .retWhy .., _, _, _, _, _, h => by simp [execStmt] at h
  | .leave _, _, _, _, _, _, h => by simp [execStmt] at h
  | .next _, _, _, _, _, _, h => by simp [execStmt] at h
  | .ite .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .onOption .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .onTag .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .onWhy .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .call .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .callInd .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .locks .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .breaking .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .traverse .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .retry .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb
  | .forever .., hb, _, _, _, _, _ => by simp [Stmt.istBlatt] at hb

end Gabbro.Stage0
