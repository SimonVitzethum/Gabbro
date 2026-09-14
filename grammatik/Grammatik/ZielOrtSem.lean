/-
  File:      Grammatik/ZielOrtSem.lean
  Subject:   THE SEQUENTIAL SIDE OF `ziel_ort` -- agreement on a footprint,
             locality of the sequential semantics, and the frame semantics
             `semZ` that keeps the logic outcome (for the caller duty).

  `ziel_ort` (`ZielOrtBeweis.lean`) replays each frame of the concurrent
  machine G by the SEQUENTIAL semantics of its body, started at the frame's
  entry world. Between the frame's own steps other threads move memory,
  but only OUTSIDE the frame's footprint (the rely, `ZielOrt.lean`); so the
  sequential world and the machine world AGREE ON THE FOOTPRINT
  (`GleichAuf`), not everywhere. This file provides:

  1. `GleichAuf S σ W`: agreement of two worlds on the carriers `S`, and
     the locality of expressions (`eval`, `evalArgs`, `evalErg` depend on
     their carriers only), of writes (a write of the same value at the
     same place keeps agreement) and of every leaf the fragment admits
     (`blatt_lokal`).
  2. `semZ`: the frame semantics of a residue, like `semK`
     (`RufUmkehrRufG.lean`) but keeping the logic outcome `logik e`, which
     the caller duty of `KoerperGut` (no failed `requires` at a call) is
     about; `ZErg.gleich` (equality up to the trace); and the residue step
     lemmas for every rule of the fragment.
  3. `GRest.okZ`: the residues `ziel_ort` follows (in the fragment `kOk`,
     reading only inside a given footprint).
-/
import Grammatik.ZielOrt

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
  | keine => rfl
  | wert e => exact eval_gleichAuf e hsub h ρ

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
        simp [World.storeSlot]
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
    simp [World.schreibGlob, World.merke, World.storeGlob]
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
  | assignDurch p t ht f i e hw hL =>
      simp only [stmtOrteP] at hS
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg1 := hg.lese Λ Λ (p.orte ++ i.orte ++ e.orte) (p.orte ++ i.orte ++ e.orte)
      refine ⟨_, rfl, ?_, spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))⟩
      rw [eval_gleichAuf i (fun o ho => hS o (List.mem_append_left _ (List.mem_append_right _ ho)))
          hg1,
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
  | schreibBytes t f hf n i hlo hhi e hw hL =>
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
  | uebergang t f hτ i von nach hn he hw hL =>
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
  | regSchreib r hk' e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hg.lese Λ Λ e.orte e.orte, spur_laenge_erw (Erw.lese _ _ _)⟩
  | transition r hk' m hm hl maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hg, Nat.le_refl _⟩
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
  | retGrund r hp => simp only [execStmt] at h; cases h
  | leave h' => simp only [execStmt] at h; cases h
  | next h' => simp only [execStmt] at h; cases h
  | axiomCall => simp [Stmt.kOk] at hk
  | callInd => simp [Stmt.kOk] at hk
  | traverse => simp [Stmt.kOk] at hk
  | retry => simp [Stmt.kOk] at hk
  | forever => simp [Stmt.kOk] at hk
  | _ => simp [Stmt.istBlatt] at hb

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
  cases r <;> simp [ZErg.gleich, SG]

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

theorem semZ_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semZ O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semZ O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semZ_dann O passes R b _ _ _).trans (nachZ_schrumpf O passes R _ _).symm

theorem semZ_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semZ O passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semZ O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact semZ_dann O passes R b _ _ _

theorem semZ_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ =
      semZ O passes R (.dann (.cons (.onGrund r arms) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt]
  rw [execGrund_wahlW O passes R arms]

theorem semZ_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann body (.dann rest k)) σ ρ =
      semZ O passes R (.dann (.cons (.breaking i body) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt]

theorem semZ_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    (semZ O passes R (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ).gleich
      (semZ O passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ) := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt]
  exact nachZ_frei O passes R _ L _

theorem semZ_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) :
    semZ O passes R k (σ.gibt L) ρ = semZ O passes R (.frei L k) σ ρ := rfl

theorem semZ_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semZ O passes R k σ ρ = semZ O passes R (.schrumpf k) σ (.cons v ρ) := rfl

theorem semZ_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semZ O passes R (.ende (.bind e rest)) σ ρ := by
  simp only [semZ, execEnd]
  rw [zErg_schrumpf]

theorem semZ_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semZ O passes R (.dann (.bind e rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock]
  rw [nachZ_schrumpf]

theorem semZ_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) =
      semZ O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semZ_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_pos h, nachZ_schrumpf, semZ_dann]

/-- An end block run as a block in front of any continuation means the end
    block (it never ends normally). -/
theorem semZ_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann e.alsBlock.2 (.abbruch k)) σ ρ = semZ O passes R (.ende e) σ ρ := by
  rw [semZ_dann, Endblock.execBlock_alsBlock, nachZ_zuAusgang]
  rfl

theorem semZ_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semZ O passes R (.ende sonst) (σ.lese Λ e.orte) ρ =
      semZ O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semZ_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_neg h, nachZ_zuAusgang]
  rfl

theorem semZ_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semZ O passes R (.dann rest k) (σ.lese Λ c.orte) ρ =
      semZ O passes R (.dann (.pruefung c sonst rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hw, if_true]

theorem semZ_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semZ O passes R (.ende sonst) (σ.lese Λ c.orte) ρ =
      semZ O passes R (.dann (.pruefung c sonst rest) k) σ ρ := by
  rw [semZ_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachZ_zuAusgang]
  rfl

theorem semZ_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semZ O passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock]
  rw [nachZ_schrumpf]

theorem semZ_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semZ O passes R (.dann (.gleit op a b lo hi rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semZ O passes R (.dann (.gleitLit q lo hi rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semZ O passes R (.dann (.gleitVon e lo hi rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semZ O passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semZ O passes R (.ende sonst) (σ.lese Λ e.orte) ρ =
      semZ O passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semZ_dann]
  simp only [execBlock, hn]
  rw [nachZ_zuAusgang]
  rfl

theorem semZ_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := rfl

theorem semZ_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semZ, execEnd, execStmt, zErg]

theorem semZ_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semZ_dann, nachZ_cons]
  rfl

/-! ### Calls: the answer of the handler decides -/

theorem semZ_rufDann {Λ Λ'' : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l Γ (nach D g Λ) Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semZ O passes R (.dann (.cons (.call g args hp hr) rest) k) σ ρ =
      semZ O passes R (.dann rest k) σ1 ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt, h]
  rfl

theorem semZ_ruf {Λ : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D V l Γ (nach D g Λ)) (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semZ O passes R (.ende (.cons (.call g args hp hr) rest)) σ ρ =
      semZ O passes R (.ende rest) σ1 ρ := by
  simp only [semZ, execEnd, execStmt, h]

theorem semZ_bindCall {Λ Λ' : List (Res D)} {τ : Ty} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semZ O passes R (.dann (.bindCall g args he hp hr rest) k) σ ρ =
      semZ O passes R (.dann rest (.schrumpf k)) σ1 (.cons (ergWert he v1) ρ) := by
  rw [semZ_dann]
  simp only [execBlock, h]
  rw [nachZ_schrumpf, semZ_dann]

theorem semZ_rufDann_logik {Λ Λ'' : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l Γ (nach D g Λ) Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (e : Logik D)
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .logik e) :
    semZ O passes R (.dann (.cons (.call g args hp hr) rest) k) σ ρ = .logik e := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt, h]
  rfl

theorem semZ_ruf_logik {Λ : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D V l Γ (nach D g Λ)) (σ : World D) (ρ : Env D Γ) (e : Logik D)
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .logik e) :
    semZ O passes R (.ende (.cons (.call g args hp hr) rest)) σ ρ = .logik e := by
  simp only [semZ, execEnd, execStmt, h]
  rfl

theorem semZ_bindCall_logik {Λ Λ' : List (Res D)} {τ : Ty} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (e : Logik D)
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .logik e) :
    semZ O passes R (.dann (.bindCall g args he hp hr rest) k) σ ρ = .logik e := by
  rw [semZ_dann]
  simp only [execBlock, h]
  rfl

end SemZ

/-! ## 4. The residues the replay follows -/

/-- A residue in the fragment (`kOk`) whose blocks read, and whose calls
    rely on contracts, only inside the footprint `S`. Loop shims and
    `wartetSonst` are outside. -/
def GRest.okZ (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.kOk = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.kOk = true ∧ blockOrteP P b ⊆ S ∧ k.okZ P S
  | _, _, _, .schrumpf k => k.okZ P S
  | _, _, _, .frei _ k => k.okZ P S
  | _, _, _, .wartet b k => b.kOk = true ∧ blockOrteP P b ⊆ S ∧ k.okZ P S
  | _, _, _, .trav .. => False
  | _, _, _, .travRest .. => False
  | _, _, _, .wieder .. => False
  | _, _, _, .wiederRest .. => False
  | _, _, _, .ewig .. => False
  | _, _, _, .ewigRest .. => False
  | _, _, _, .wartetSonst .. => False
  | _, _, _, .abbruch k => k.okZ P S

theorem teil_append {α : Type} {a b S : List α} (h : a ++ b ⊆ S) : a ⊆ S ∧ b ⊆ S :=
  ⟨fun _ hx => h (List.mem_append_left _ hx), fun _ hx => h (List.mem_append_right _ hx)⟩

theorem teil_von_append {α : Type} {a b S : List α} (ha : a ⊆ S) (hb : b ⊆ S) : a ++ b ⊆ S :=
  fun _ hx => (List.mem_append.mp hx).elim (fun h => ha h) (fun h => hb h)

section OkZ

variable {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okZ_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okZ P S) :
    s.kOk = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okZ P S := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.kOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okZ_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okZ P S) :
    s.kOk = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okZ P S := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.kOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

/-- The chosen arm of `onTag` is in the fragment and reads inside the arms. -/
theorem armWahlG_orteP {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    blockOrteP P (armWahlG arms v).2.1 ⊆ armsOrteP P arms
  | _, .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩ => fun _ hx => List.mem_append_left _ hx
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩ => fun _ hx =>
      List.mem_append_right _ (armWahlG_orteP rest _ hx)

theorem armWahlG_orteP' {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) {c : Option (Int × Int)}
    {b : Block D V l (ArmCtx Γ c) Λ Λ'} {nutz : Nutzlast c}
    (hw : armWahlG arms v = ⟨c, b, nutz⟩) : blockOrteP P b ⊆ armsOrteP P arms := by
  have h := armWahlG_orteP (P := P) arms v
  rw [hw] at h
  exact h

theorem grundWahlG_orteP {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    blockOrteP P (grundWahlG arms r) ⊆ grundArmsOrteP P arms
  | _, .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩ => fun _ hx => List.mem_append_left _ hx
  | _, .cons _ rest, ⟨_ + 1, _⟩ => fun _ hx =>
      List.mem_append_right _ (grundWahlG_orteP rest _ hx)

end OkZ

/-! ## CUTS:

  What is proved: agreement on a footprint (`GleichAuf`) and the locality
  of `eval`/`evalArgs`/`evalErg`, of slot/global/byte writes and of every
  leaf of the fragment (`blatt_lokal`); the frame semantics `semZ` with
  its residue step lemmas for every rule of the fragment, including the
  call lemmas for a normal answer and for a logic answer; the residue
  predicate `GRest.okZ` with its inversions.

  What is NOT here: loops, abrupt exits, the error channel, indirect calls,
  axioms and the oracle forms have no step lemma (`semZ` gives their
  residues no meaning); `ziel_ort` does not need them because
  `programmImFragment` keeps every reachable residue inside the fragment.
-/

#print axioms Gabbro.Grammatik.blatt_lokal
#print axioms Gabbro.Grammatik.semZ_locks
#print axioms Gabbro.Grammatik.semZ_bindCall
#print axioms Gabbro.Grammatik.semZ_rufDann_logik

end Gabbro.Grammatik
