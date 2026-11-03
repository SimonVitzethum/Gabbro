module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG
public import Grammatik.Speichermodell.Maschine.GXMaschine

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Shifting the counters -/

/-- Every `ewig` counter of the residue `j` higher; nothing else changes. -/
def GRest.plus (j : Nat) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    GRest D V l Γ Λ → GRest D V l Γ Λ
  | _, _, _, .ende e => .ende e
  | _, _, _, .dann b k => .dann b (k.plus j)
  | _, _, _, .schrumpf k => .schrumpf (k.plus j)
  | _, _, _, .frei L k => .frei L (k.plus j)
  | _, _, _, .trav t inv body ks k => .trav t inv body ks (k.plus j)
  | _, _, _, .travRest t inv body ks k => .travRest t inv body ks (k.plus j)
  | _, _, _, .verbrauch t member edge inv bound mass body rest k =>
      .verbrauch t member edge inv bound mass body rest (k.plus j)
  | _, _, _, .verbrauchRest t member edge inv bound mass body rest vor k =>
      .verbrauchRest t member edge inv bound mass body rest vor (k.plus j)
  | _, _, _, .wieder n bis body ueber k => .wieder n bis body ueber (k.plus j)
  | _, _, _, .wiederRest n bis body ueber k => .wiederRest n bis body ueber (k.plus j)
  | _, _, _, .ewig a n inv body k => .ewig a (n + j) inv body (k.plus j)
  | _, _, _, .ewigRest a n inv body k => .ewigRest a (n + j) inv body (k.plus j)
  | _, _, _, .wartet rest k => .wartet rest (k.plus j)
  | _, _, _, .wartetSonst n err rest k => .wartetSonst n err rest (k.plus j)
  | _, _, _, .abbruch k => .abbruch (k.plus j)
  | _, _, _, .rueckBereit sc k => .rueckBereit sc (k.plus j)
  | _, _, _, .zurueckgekehrt a => .zurueckgekehrt a
  | _, _, _, .aufraeumen a remaining => .aufraeumen a remaining
  | _, _, _, .leer => .leer

/-- A frame with its residue shifted. -/
def RufRahmenG.plus (j : Nat) (r : RufRahmenG D) : RufRahmenG D :=
  ⟨r.f, r.rho, r.s0, ⟨r.rest.1, r.rest.2.1, r.rest.2.2.1, r.rest.2.2.2.1, r.rest.2.2.2.2.plus j⟩⟩

/-- A thread with every frame shifted. -/
def RufFadenG.plus (j : Nat) (z : RufFadenG D) : RufFadenG D :=
  ⟨z.stapel.map (RufRahmenG.plus j), z.kopf.plus j, z.spur, z.log⟩

/-- A machine with every thread shifted. -/
def RufMaschineG.plus (j : Nat) (M : RufMaschineG D) : RufMaschineG D :=
  ⟨M.speicher, fun t => (M.faeden t).plus j, M.lauf, M.start⟩

/-- A thread machine with its machine-G state shifted. -/
def FadenMaschine.plus (j : Nat) (K : FadenMaschine D) : FadenMaschine D :=
  ⟨K.m.plus j, K.lebt, K.wartet, K.rang, K.uhr⟩

@[simp] theorem RufMaschineG.plus_speicher (j : Nat) (M : RufMaschineG D) :
    (M.plus j).speicher = M.speicher := by rfl
@[simp] theorem RufMaschineG.plus_lauf (j : Nat) (M : RufMaschineG D) : (M.plus j).lauf = M.lauf := by rfl
@[simp] theorem RufMaschineG.plus_start (j : Nat) (M : RufMaschineG D) : (M.plus j).start = M.start := by rfl
@[simp] theorem RufMaschineG.plus_faeden (j : Nat) (M : RufMaschineG D) (t : Faden) :
    (M.plus j).faeden t = (M.faeden t).plus j := by rfl
@[simp] theorem RufFadenG.plus_spur (j : Nat) (z : RufFadenG D) : (z.plus j).spur = z.spur := by rfl
@[simp] theorem RufFadenG.plus_log (j : Nat) (z : RufFadenG D) : (z.plus j).log = z.log := by rfl
@[simp] theorem RufFadenG.plus_stapel (j : Nat) (z : RufFadenG D) :
    (z.plus j).stapel = z.stapel.map (RufRahmenG.plus j) := by rfl
@[simp] theorem RufFadenG.plus_kopf (j : Nat) (z : RufFadenG D) : (z.plus j).kopf = z.kopf.plus j := by rfl
@[simp] theorem RufRahmenG.plus_f (j : Nat) (r : RufRahmenG D) : (r.plus j).f = r.f := by rfl
@[simp] theorem RufRahmenG.plus_rho (j : Nat) (r : RufRahmenG D) : (r.plus j).rho = r.rho := by rfl
@[simp] theorem RufRahmenG.plus_s0 (j : Nat) (r : RufRahmenG D) : (r.plus j).s0 = r.s0 := by rfl

theorem RufMaschineG.plus_weltVon (j : Nat) (M : RufMaschineG D) (t : Faden) :
    (M.plus j).weltVon t = M.weltVon t := by rfl

/-- A residue with its context, shifted, read through its own equation. -/
theorem sigmaRest_plus (j : Nat) {V : Vertrag D}
    {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {g : GRest D V l Γ Λ} (h : x = ⟨l, Γ, Λ, ρ, g⟩) :
    (⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.plus j⟩ :
      Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) = ⟨l, Γ, Λ, ρ, g.plus j⟩ := by
  subst h; rfl

theorem RufRahmenG.plus_rest {j : Nat} {r : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {g : GRest D (vertragVon D r.f) l Γ Λ} (h : r.rest = ⟨l, Γ, Λ, ρ, g⟩) :
    (r.plus j).rest = ⟨l, Γ, Λ, ρ, g.plus j⟩ :=
  sigmaRest_plus j h

theorem rufUpdateG_plus (j : Nat) (m : Faden → RufFadenG D) (f : Faden) (z : RufFadenG D) :
    (fun t => (rufUpdateG m f z t).plus j) = rufUpdateG (fun t => (m t).plus j) f (z.plus j) := by
  funext t
  by_cases h : t = f
  · subst h; simp only [rufUpdateG, ↓reduceIte]
  · simp only [rufUpdateG, h, ↓reduceIte]

theorem GRest.plus_zero {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : GRest D V l Γ Λ),
    g.plus 0 = g
  | _, _, _, .ende _ => rfl
  | _, _, _, .dann _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .schrumpf k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .frei _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .trav .. => by rename_i k; simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .travRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .wieder .. => by rename_i k; simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .wiederRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .ewig .. => by rename_i k; simp only [GRest.plus, GRest.plus_zero k, Nat.add_zero]
  | _, _, _, .ewigRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k, Nat.add_zero]
  | _, _, _, .wartet _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .wartetSonst _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .abbruch k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .rueckBereit _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .zurueckgekehrt _ => rfl
  | _, _, _, .aufraeumen _ _ => rfl
  | _, _, _, .leer => rfl

theorem GRest.plus_plus (i j : Nat) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ), (g.plus i).plus j = g.plus (i + j)
  | _, _, _, .ende _ => rfl
  | _, _, _, .dann _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .schrumpf k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .frei _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .trav .. => by rename_i k; simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .travRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .wieder .. => by rename_i k; simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .wiederRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .ewig .. => by rename_i k; simp only [GRest.plus, GRest.plus_plus i j k, Nat.add_assoc]
  | _, _, _, .ewigRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k, Nat.add_assoc]
  | _, _, _, .wartet _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .wartetSonst _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .abbruch k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .rueckBereit _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .zurueckgekehrt _ => rfl
  | _, _, _, .aufraeumen _ _ => rfl
  | _, _, _, .leer => rfl

theorem GRest.plus_wartend (j : Nat) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ), (g.plus j).wartend = g.wartend
  | _, _, _, .ende _ | _, _, _, .dann .. | _, _, _, .schrumpf _ | _, _, _, .frei .. | _, _, _, .trav ..
  | _, _, _, .travRest .. | _, _, _, .verbrauch .. | _, _, _, .verbrauchRest .. | _, _, _, .wieder .. | _, _, _, .wiederRest .. | _, _, _, .ewig ..
  | _, _, _, .ewigRest .. | _, _, _, .wartet .. | _, _, _, .wartetSonst .. | _, _, _, .abbruch _ | _, _, _, .rueckBereit ..
  | _, _, _, .zurueckgekehrt _ => rfl
  | _, _, _, .aufraeumen _ _ => rfl
  | _, _, _, .leer => rfl

/-- Shifting loop counters does not change the source return selected. -/
theorem GRest.plus_scopedWert (j : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) : (r.plus j).scopedWert = r.scopedWert := by
  cases r with
  | dann b _ =>
      cases b with
      | cons s _ => cases s <;> rfl
      | _ => rfl
  | _ => rfl

theorem GRest.plus_scopedGrund (j : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) : (r.plus j).scopedGrund = r.scopedGrund := by
  cases r with
  | dann b _ =>
      cases b with
      | cons s _ => cases s <;> rfl
      | _ => rfl
  | _ => rfl

/-- Caller resumption shifts only the suspended continuation, in either answer channel. -/
private theorem antwortRestG_plus (j : Nat) {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) :
    antwortRestG g a ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.plus j⟩ =
      (antwortRestG g a c).map (fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.plus j⟩) := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;> first
  | rfl
  | (simp only [antwortRestG, GRest.plus]
     split <;> simp_all only [Option.map, ↓reduceDIte])

/-- Returning a saved answer commutes with shifting the suspended counters. -/
theorem rufAntwortG_plus (j : Nat) {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (h : rufAntwortG z vor σ a = some z') : rufAntwortG (z.plus j) vor σ a = some (z'.plus j) := by
  obtain ⟨st, kopf, spur, log⟩ := z
  cases st with
  | nil =>
      simp only [rufAntwortG, Option.some.injEq] at h
      subst z'
      rfl
  | cons c st =>
      cases hr : antwortRestG kopf.f a c.rest with
      | none => simp only [rufAntwortG, hr, Option.bind] at h
      | some rest =>
          have hplus := antwortRestG_plus j kopf.f a c.rest
          rw [hr] at hplus
          simp only [Option.map] at hplus
          simp only [rufAntwortG, hr, Option.bind, Option.some.injEq] at h
          subst z'
          simp only [RufFadenG.plus, RufRahmenG.plus, rufAntwortG, List.map_cons, hplus, Option.bind]

/-! ## 2. The budget decides nothing but the budget -/

/-- **A leaf runs the same at every budget** (it contains no loop). -/
theorem execStmt_blatt_passes (O : Orakel D) (p q : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (h : s.istBlatt = true) (σ : World D) (ρ : Env D Γ) :
    execStmt O p R s σ ρ = execStmt O q R s σ ρ := by
  cases s <;> simp only [Stmt.istBlatt, Bool.false_eq_true] at h <;> rfl

/-- The start machine has no counter. -/
theorem rufStartG_plus (j : Nat) (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    (RufStartG P sp init).plus j = RufStartG P sp init := by
  simp only [RufMaschineG.plus, RufStartG, RufFadenG.plus, RufRahmenG.plus, GRest.plus, List.map_nil]

theorem RufRahmenG.plus_wartend (j : Nat) (r : RufRahmenG D) : (r.plus j).wartend = r.wartend :=
  GRest.plus_wartend j _

theorem GRest.plus_anRueck (j : Nat) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ), (g.plus j).anRueck = g.anRueck
  | _, _, _, .dann b _ => by
      cases b with
      | cons s _ => cases s <;> rfl
      | _ => rfl
  | _, _, _, .ende _ | _, _, _, .schrumpf _ | _, _, _, .frei .. | _, _, _, .trav ..
  | _, _, _, .travRest .. | _, _, _, .verbrauch .. | _, _, _, .verbrauchRest .. | _, _, _, .wieder .. | _, _, _, .wiederRest .. | _, _, _, .ewig ..
  | _, _, _, .ewigRest .. | _, _, _, .wartet .. | _, _, _, .wartetSonst .. | _, _, _, .abbruch _ | _, _, _, .rueckBereit ..
  | _, _, _, .zurueckgekehrt _ => rfl
  | _, _, _, .aufraeumen _ _ => rfl
  | _, _, _, .leer => rfl

theorem fertigG_plus (j : Nat) (M : RufMaschineG D) (t : Faden) : FertigG (M.plus j) t ↔ FertigG M t := by
  unfold FertigG
  refine and_congr ?_ ?_
  · simp only [RufMaschineG.plus_faeden, RufFadenG.plus_stapel, List.map_eq_nil_iff]
  · exact Eq.to_iff (congrArg (· = true) (GRest.plus_anRueck j (M.faeden t).kopf.rest.2.2.2.2))

/-! ## 3. Every step at budget `p` is a step at budget `p + j` -/

/-- The successor machine of every step, shifted: the update of the acting thread, shifted. -/
theorem RufMaschineG.plus_update (j : Nat) (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    RufMaschineG.plus j ⟨sp, rufUpdateG m f z, la, st⟩ =
      ⟨sp, rufUpdateG (fun t => (m t).plus j) f (z.plus j), la, st⟩ := by
  simp only [RufMaschineG.plus, rufUpdateG_plus]

/- **A step at budget `p` is a step at budget `p + j`** of the shifted machines. -/

end Gabbro.Grammatik
