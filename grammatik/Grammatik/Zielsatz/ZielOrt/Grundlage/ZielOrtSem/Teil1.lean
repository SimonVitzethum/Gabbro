module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
  | _, _, _, .verbrauch .., _, _ => .sonst
  | _, _, _, .verbrauchRest .., _, _ => .sonst
  | _, _, _, .wieder .., _, _ => .sonst
  | _, _, _, .wiederRest .., _, _ => .sonst
  | _, _, _, .ewig .., _, _ => .sonst
  | _, _, _, .ewigRest .., _, _ => .sonst
  | _, _, _, .wartet .., _, _ => .sonst
  | _, _, _, .wartetSonst .., _, _ => .sonst
  | _, _, _, .abbruch .., _, _ => .sonst
  | _, _, _, .rueckBereit .., _, _ => .sonst
  | _, _, _, .zurueckgekehrt (.inl v), σ, _ => .zurueck σ v
  | _, _, _, .zurueckgekehrt (.inr _), _, _ => .sonst
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
