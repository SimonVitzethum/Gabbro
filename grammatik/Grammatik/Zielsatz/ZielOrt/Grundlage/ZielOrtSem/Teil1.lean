module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Agreement on a footprint -/

/-- Two worlds agree on the carriers `S` (slots of every table in `S`,
    the value of every global in `S`). Traces are not compared. -/
def GleichAuf (S : List (D.Tab ⊕ D.Glob)) (σ σ' : World D) : Prop :=
  (∀ t, Sum.inl t ∈ S → σ.slots t = σ'.slots t) ∧
  (∀ g, Sum.inr g ∈ S → σ.globs g = σ'.globs g)

namespace GleichAuf

variable {S S' : List (D.Tab ⊕ D.Glob)} {σ σ' σ'' : World D}

theorem refl (S : List (D.Tab ⊕ D.Glob)) (σ : World D) : GleichAuf S σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem symm (h : GleichAuf S σ σ') : GleichAuf S σ' σ :=
  ⟨fun t ht => (h.1 t ht).symm, fun g hg => (h.2 g hg).symm⟩

theorem trans (h1 : GleichAuf S σ σ') (h2 : GleichAuf S σ' σ'') : GleichAuf S σ σ'' :=
  ⟨fun t ht => (h1.1 t ht).trans (h2.1 t ht), fun g hg => (h1.2 g hg).trans (h2.2 g hg)⟩

theorem mono (hsub : ∀ o ∈ S', o ∈ S) (h : GleichAuf S σ σ') : GleichAuf S' σ σ' :=
  ⟨fun t ht => h.1 t (hsub _ ht), fun g hg => h.2 g (hsub _ hg)⟩

/-- Same memory, any traces. -/
theorem vonSpeicher (h : σ.speicher = σ'.speicher) : GleichAuf S σ σ' := by
  have hs : σ.slots = σ'.slots := congrArg Speicher.slots h
  have hg : σ.globs = σ'.globs := congrArg Speicher.globs h
  exact ⟨fun t _ => by rw [hs], fun g _ => by rw [hg]⟩

theorem lese (h : GleichAuf S σ σ') (Λ Λ' : List (Res D)) (os os' : List (D.Tab ⊕ D.Glob)) :
    GleichAuf S (σ.lese Λ os) (σ'.lese Λ' os') := h

theorem lese_links (h : GleichAuf S σ σ') (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    GleichAuf S (σ.lese Λ os) σ' := h

theorem gibt (h : GleichAuf S σ σ') (L : D.Lock) : GleichAuf S (σ.gibt L) σ' := h

theorem nimmt (h : GleichAuf S σ σ') (L : D.Lock) : GleichAuf S (σ.nimmt L) σ' := h

end GleichAuf

/-- An expression reads only its carriers. -/
theorem eval_gleichAuf {S : List (D.Tab ⊕ D.Glob)} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (hsub : ∀ o ∈ e.orte, o ∈ S) {σ σ' : World D} (h : GleichAuf S σ σ')
    (ρ : Env D Γ) : eval σ e σ ρ = eval σ' e σ' ρ :=
  Extraktion.eval_liest_nur_orte e S hsub σ σ' σ σ' ρ
    (fun t ht k f => congrFun (congrFun (h.1 t ht) k) f) (fun g hg => h.2 g hg)
    (fun t ht k f => congrFun (congrFun (h.1 t ht) k) f) (fun g hg => h.2 g hg)

/-- Arguments read only their carriers. -/
theorem evalArgs_gleichAuf {S : List (D.Tab ⊕ D.Glob)} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {τs : List Ty} (args : Args D Γ Λ τs), (∀ o ∈ args.orte, o ∈ S) →
      ∀ {σ σ' : World D}, GleichAuf S σ σ' → ∀ (ρ : Env D Γ),
        evalArgs σ args σ ρ = evalArgs σ' args σ' ρ
  | _, .nil, _, _, _, _, _ => rfl
  | _, .cons e rest, hsub, σ, σ', h, ρ => by
      show Env.cons (eval σ e σ ρ) (evalArgs σ rest σ ρ) =
        Env.cons (eval σ' e σ' ρ) (evalArgs σ' rest σ' ρ)
      rw [eval_gleichAuf e (fun o ho => hsub o (List.mem_append_left _ ho)) h ρ,
        evalArgs_gleichAuf rest (fun o ho => hsub o (List.mem_append_right _ ho)) h ρ]

/-- A result expression reads only its carriers. -/
theorem evalErg_gleichAuf {S : List (D.Tab ⊕ D.Glob)} {Γ : Ctx} {Λ : List (Res D)}
    {e : Option Ty} (x : ErgExpr D Γ Λ e) (hsub : ∀ o ∈ x.orte, o ∈ S) {σ σ' : World D}
    (h : GleichAuf S σ σ') (ρ : Env D Γ) : evalErg σ x σ ρ = evalErg σ' x σ' ρ := by
  cases x with
  | empty => rfl
  | val e => exact eval_gleichAuf e hsub h ρ

/-- A slot store of the same value at the same place keeps agreement. -/
theorem gleichAuf_storeSlot {S : List (D.Tab ⊕ D.Glob)} {σ σ' : World D}
    (h : GleichAuf S σ σ') (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    GleichAuf S (σ.storeSlot t k f v) (σ'.storeSlot t k f v) := by
  refine ⟨fun t' ht' => ?_, fun g hg => h.2 g hg⟩
  have e := h.1 t' ht'
  funext k' f'
  by_cases htt : t' = t
  · subst htt
    by_cases hk : k' = k
    · subst hk
      by_cases hf : f' = f
      · subst hf
        simp only [World.storeSlot, ↓reduceDIte, ↓reduceIte]
      · rw [storeSlot_fremd_feld _ _ _ _ _ _ _ rfl hf, storeSlot_fremd_feld _ _ _ _ _ _ _ rfl hf, e]
    · simp only [World.storeSlot, dif_pos rfl, if_neg hk]
      rw [e]
  · rw [storeSlot_fremd_traeger _ htt, storeSlot_fremd_traeger _ htt, e]

theorem gleichAuf_schreibSlot {S : List (D.Tab ⊕ D.Glob)} {σ σ' : World D}
    (h : GleichAuf S σ σ') (t : D.Tab) (Λ Λ' : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) :
    GleichAuf S (σ.schreibSlot t Λ k f v) (σ'.schreibSlot t Λ' k f v) :=
  gleichAuf_storeSlot h t k f v

theorem gleichAuf_schreibGlob {S : List (D.Tab ⊕ D.Glob)} {σ σ' : World D}
    (h : GleichAuf S σ σ') (g : D.Glob) (Λ Λ' : List (Res D)) (v : Wert D (D.gtyp g)) :
    GleichAuf S (σ.schreibGlob g Λ v) (σ'.schreibGlob g Λ' v) := by
  refine ⟨fun t ht => h.1 t ht, fun g' hg' => ?_⟩
  by_cases hgg : g' = g
  · subst hgg
    simp only [World.schreibGlob, World.merke, World.storeGlob, List.cons_append, List.nil_append, ↓reduceDIte]
  · show (σ.storeGlob g v).globs g' = (σ'.storeGlob g v).globs g'
    rw [storeGlob_fremd_global _ hgg, storeGlob_fremd_global _ hgg]
    exact h.2 g' hg'

theorem gleichAuf_schreibBytes {S : List (D.Tab ⊕ D.Glob)} (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ Λ' : List (Res D)) :
    ∀ (bs : List Byte) {σ σ' : World D} (k : Int), GleichAuf S σ σ' →
      GleichAuf S (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes t f hf Λ' k bs)
  | [], _, _, _, h => h
  | _ :: bs, _, _, k, h =>
      gleichAuf_schreibBytes t f hf Λ Λ' bs (k + 1) (gleichAuf_schreibSlot h t Λ Λ' k f _)

/-! ## 2. Leaves are local -/

/-- The trace only grows along a leaf of the fragment (`Erw`). -/
theorem spur_laenge_erw {σ σ' : World D} (h : Erw σ σ') : σ.spur.length ≤ σ'.spur.length := by
  obtain ⟨neu, e, _⟩ := h
  rw [e, List.length_append]
  exact Nat.le_add_left _ _

/-- **Leaf locality.** A leaf of the fragment, run at a world `σ` that
    agrees with the machine world `W` on a footprint `S` covering the leaf's
    carriers, ends exactly where the machine's run ends in environment, and
    in a world that agrees with the machine's on `S`; its trace only grows. -/
theorem blatt_lokal (P : Programm D) (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hk : s.kOk = true)
    (hb : s.istBlatt = true) {S : List (D.Tab ⊕ D.Glob)} (hS : ∀ o ∈ stmtOrteP P s, o ∈ S) {σ W : World D}
    (hg : GleichAuf S σ W) {ρ : Env D Γ} {W' : World D} {ρ' : Env D Γ}
    (h : execStmt O passes keinRuf s W ρ = .ok W' ρ') :
    ∃ σ', execStmt O passes keinRuf s σ ρ = .ok σ' ρ' ∧ GleichAuf S σ' W' ∧
      σ.spur.length ≤ σ'.spur.length := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ (i.orte ++ e.orte) (i.orte ++ e.orte)
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))⟩
      rw [eval_gleichAuf i (fun o ho => hS o (List.mem_append_left _ ho)) hg1,
        eval_gleichAuf e (fun o ho => hS o (List.mem_append_right _ ho)) hg1]
      exact gleichAuf_schreibSlot hg1 _ _ _ _ _ _
  | assignThru p t ht f i e hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ (p.orte ++ i.orte ++ e.orte) (p.orte ++ i.orte ++ e.orte)
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))⟩
      rw [eval_gleichAuf i (fun o ho => hS o (List.mem_append_left _ (List.mem_append_right _ ho)))
          hg1,
        eval_gleichAuf e (fun o ho => hS o (List.mem_append_right _ ho)) hg1]
      exact gleichAuf_schreibSlot hg1 _ _ _ _ _ _
  | assignSlotRef r t ht ho f e hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ (r.orte ++ e.orte) (r.orte ++ e.orte)
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))⟩
      rw [eval_gleichAuf r (fun o ho => hS o (List.mem_append_left _ ho)) hg1,
        eval_gleichAuf e (fun o ho => hS o (List.mem_append_right _ ho)) hg1]
      exact gleichAuf_schreibSlot hg1 _ _ _ _ _ _
  | assignGlob g e hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ e.orte e.orte
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _))⟩
      rw [eval_gleichAuf e hS hg1]
      exact gleichAuf_schreibGlob hg1 _ _ _ _
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ (i.orte ++ e.orte) (i.orte ++ e.orte)
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibBytes _ _ _ _ _ _ _))⟩
      rw [eval_gleichAuf i (fun o ho => hS o (List.mem_append_left _ ho)) hg1,
        eval_gleichAuf e (fun o ho => hS o (List.mem_append_right _ ho)) hg1]
      exact gleichAuf_schreibBytes t f hf _ _ _ _ hg1
  | assignVar x e =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ e.orte e.orte
      refine ⟨_, ?_, hg1, spur_laenge_erw (Erw.lese _ _ _)⟩
      simp only [execStmt]
      rw [eval_gleichAuf e hS hg1]
  | shift t f hτ i von nach hn he hw hL =>
      simp only [stmtOrteP] at hS
      have hg1 := hg.lese Λ Λ (.inl t :: i.orte) (.inl t :: i.orte)
      have hi := eval_gleichAuf i (fun o ho => hS o (List.mem_cons_of_mem _ ho)) hg1 ρ
      have ht : (σ.lese Λ (.inl t :: i.orte)).slots t = (W.lese Λ (.inl t :: i.orte)).slots t :=
        hg1.1 t (hS _ List.mem_cons_self)
      simp only [execStmt] at h
      split at h
      · rename_i hvon
        simp only [Ausgang.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨_, ?_, gleichAuf_schreibSlot hg1 _ Λ Λ _ _ _,
          spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ Λ _ _ _))⟩
        simp only [execStmt]
        rw [hi, ht, if_pos hvon]
      · cases h
  | regWrite r hk' e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hg.lese Λ Λ e.orte e.orte, spur_laenge_erw (Erw.lese _ _ _)⟩
  | transition r hk' m hm hl maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hg, Nat.le_succ _⟩
  | publish g e payload hp hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ e.orte e.orte
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _))⟩
      rw [eval_gleichAuf e hS hg1]
      exact gleichAuf_schreibGlob hg1 _ _ _ _
  | advances m a h' hs =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hg, Nat.le_refl _⟩
  | retires m s' h' a =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hg, Nat.le_refl _⟩
  | ret e hp => simp only [execStmt] at h; cases h
  | retWhy r hp => simp only [execStmt] at h; cases h
  | leave h' => simp only [execStmt] at h; cases h
  | next h' => simp only [execStmt] at h; cases h
  | axiomCall => simp only [Stmt.kOk, Bool.false_eq_true] at hk
  | callInd => simp only [Stmt.kOk, Bool.false_eq_true] at hk
  | traverse => simp only [Stmt.kOk, Bool.false_eq_true] at hk
  | retry => simp only [Stmt.kOk, Bool.false_eq_true] at hk
  | forever => simp only [Stmt.kOk, Bool.false_eq_true] at hk
  | _ => simp only [Stmt.istBlatt, Bool.false_eq_true] at hb

/-! ## 3. The frame semantics with the logic outcome -/

/-- What a frame's residue still produces, sequentially: a return, a logic
    failure (with its cause), or anything else. -/
inductive ZErg (V : Vertrag D) where
  | zurueck (σ : World D) (v : ErgVal D V.erg)
  | logik (e : Logik D)
  | sonst

/-- Frame results that agree up to the trace. -/
def ZErg.gleich {V : Vertrag D} : ZErg V → ZErg V → Prop
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .logik e, .logik e' => e = e'
  | .sonst, .sonst => True
  | _, _ => False

theorem ZErg.gleich_refl {V : Vertrag D} (r : ZErg V) : r.gleich r := by
  cases r <;> simp only [gleich, SG, and_self]

theorem ZErg.gleich_symm {V : Vertrag D} {r r' : ZErg V} (h : r.gleich r') : r'.gleich r := by
  cases r <;> cases r' <;> simp_all [ZErg.gleich, SG]

theorem ZErg.gleich_trans {V : Vertrag D} {r r' r'' : ZErg V} (h1 : r.gleich r')
    (h2 : r'.gleich r'') : r.gleich r'' := by
  cases r <;> cases r' <;> cases r'' <;> simp_all [ZErg.gleich, SG]

theorem ZErg.gleich_of_eq {V : Vertrag D} {r r' : ZErg V} (h : r = r') : r.gleich r' := by
  subst h; exact ZErg.gleich_refl _

/-- The frame result of an end outcome. -/
def zErg {V : Vertrag D} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → ZErg V
  | .zurueck σ v => .zurueck σ v
  | .logik e => .logik e
  | _ => .sonst

theorem zErg_schrumpf {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (o : EndAusgang V l (τ :: Γ)) : zErg o.schrumpf = zErg o := by
  cases o <;> rfl

section SemZ

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- **The frame semantics.** A residue run sequentially with the handler
    `R`: an end block by `execEnd`, `dann b k` by `execBlock b` and then
    `k`, `schrumpf` drops a binding, `frei L` releases the lock of its
    `locks`. Loop shims and waiting residues are outside (`sonst`). -/
def semZ : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → World D →
    Env D Γ → ZErg V
  | _, _, _, .ende e, σ, ρ => zErg (execEnd O passes R e σ ρ)
  | _, _, _, .dann b k, σ, ρ =>
      match execBlock O passes R b σ ρ with
      | .ok σ' ρ' => semZ k σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .schrumpf k, σ, ρ => semZ k σ ρ.tail
  | _, _, _, .frei L k, σ, ρ => semZ k (σ.gibt L) ρ
  | _, _, _, .trav .., _, _ => .sonst
  | _, _, _, .travRest .., _, _ => .sonst
  | _, _, _, .wieder .., _, _ => .sonst
  | _, _, _, .wiederRest .., _, _ => .sonst
  | _, _, _, .ewig .., _, _ => .sonst
  | _, _, _, .ewigRest .., _, _ => .sonst
  | _, _, _, .wartet .., _, _ => .sonst
  | _, _, _, .wartetSonst .., _, _ => .sonst
  | _, _, _, .abbruch .., _, _ => .sonst
  | _, _, _, .leer, _, _ => .sonst

/-- Continue with `k` after an outcome. -/
def nachZ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (o : Ausgang V l Γ)
    (k : GRest D V l Γ Λ) : ZErg V :=
  match o with
  | .ok σ ρ => semZ O passes R k σ ρ
  | .zurueck σ v => .zurueck σ v
  | .logik e => .logik e
  | _ => .sonst

variable {l : Bool} {Γ : Ctx}

theorem semZ_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann b k) σ ρ = nachZ O passes R (execBlock O passes R b σ ρ) k := by
  simp only [semZ, nachZ]

theorem nachZ_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    nachZ O passes R (execBlock O passes R (.cons s rest) σ ρ) k =
      nachZ O passes R (execStmt O passes R s σ ρ) (.dann rest k) := by
  simp only [execBlock]
  generalize execStmt O passes R s σ ρ = o
  cases o <;> simp only [nachZ, semZ_dann]

theorem nachZ_schrumpf {τ : Ty} {Λ : List (Res D)} (o : Ausgang V l (τ :: Γ))
    (k : GRest D V l Γ Λ) :
    nachZ O passes R o.schrumpf k = nachZ O passes R o (.schrumpf k) := by
  cases o <;> simp only [Ausgang.schrumpf, nachZ, semZ]

theorem nachZ_zuAusgang {Λ : List (Res D)} (o : EndAusgang V l Γ) (k : GRest D V l Γ Λ) :
    nachZ O passes R o.zuAusgang k = zErg o := by
  cases o <;> rfl

theorem zErg_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    zErg (execEnd O passes R (.cons s rest) σ ρ) =
      nachZ O passes R (execStmt O passes R s σ ρ) (.dann .nil (.ende rest)) := by
  simp only [execEnd]
  generalize execStmt O passes R s σ ρ = o
  cases o <;> simp only [zErg, nachZ, semZ, execBlock]

theorem nachZ_frei {Λ : List (Res D)} (o : Ausgang V l Γ) (L : D.Lock)
    (k : GRest D V l Γ Λ) :
    (nachZ O passes R o (.frei L k)).gleich (nachZ O passes R (o.mapWelt (·.gibt L)) k) := by
  cases o with
  | ok σ ρ => exact ZErg.gleich_refl _
  | zurueck σ v => exact ⟨⟨rfl, rfl⟩, rfl⟩
  | logik e => exact ZErg.gleich_refl _
  | _ => trivial

/-! ### The residue step lemmas, one per rule of the fragment -/

theorem semZ_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semZ O passes R (.ende rest) σ' ρ' = semZ O passes R (.ende (.cons s rest)) σ ρ := by
  simp only [semZ, execEnd, h]

theorem semZ_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semZ O passes R (.dann rest k) σ' ρ' = semZ O passes R (.dann (.cons s rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons s rest), nachZ_cons, h]
  rfl

theorem semZ_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann (.cons s .nil) (.ende rest)) σ ρ =
      semZ O passes R (.ende (.cons s rest)) σ ρ := by
  rw [semZ_dann, nachZ_cons]
  exact (zErg_cons O passes R s rest σ ρ).symm

theorem semZ_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R k σ ρ = semZ O passes R (.dann .nil k) σ ρ := by
  simp only [semZ, execBlock]

theorem semZ_iteWahr {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semZ O passes R (.dann t (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semZ O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt, hw, if_true]

theorem semZ_iteFalsch {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semZ O passes R (.dann e (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semZ O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt, hw, Bool.false_eq_true, if_false]

theorem semZ_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semZ O passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) =
      semZ O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt, hv]
  rw [nachZ_schrumpf]

theorem semZ_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semZ O passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ =
      semZ O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt, hv]

theorem semZ_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (τ : Ty) (b : Block D V l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some τ, b, nutz⟩) :
    semZ O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semZ O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semZ_dann O passes R b _ _ _).trans (nachZ_schrumpf O passes R _ _).symm

end SemZ
end Gabbro.Grammatik
