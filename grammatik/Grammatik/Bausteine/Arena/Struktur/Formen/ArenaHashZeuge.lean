/-
  File:      Grammatik/ArenaHashZeuge.lean
  Subject:   WITNESSES AND A PLANTED DEFECT FOR THE EXECUTED HASH FORMS (PLAN-DYNAMIC.md section 8a.1, third pass), on a
             concrete declaration with TWO tables: the arena (four slots, payload `0`, free link `1`, chain link `2`) and a
             bucket table (two slots, one field `0`: the head of the chain). Words: counter, committed word, free head.

  The world `wh`: slot `3` on the free list, bucket `0` holds the chain `1`, bucket `1` is empty, slots `0` and `2` are live
  and on no bucket.
    * `push_zeuge`    -- `hash_push_zug` on a real world: slot `2` becomes the head of bucket `1`; the hypotheses hold, the
                         head and the link are read back;
    * `pop_zeuge`     -- `hash_pop_zug`: bucket `0` loses its head `1`, which is live and on no bucket;
    * `push_defekt`   -- the planted defect: slot `1`, already the head of bucket `0`, is pushed into bucket `1` too: the
                         chains overlap and the model rejects the world.
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaHashZug

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace HashZeuge

/-- Two tables (`false`: the arena, four slots; `true`: the buckets, two slots), three fields, three words. -/
@[reducible] def FD3 : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun t => if t then 2 else 4
  Feld := fun _ => Fin 3
  decFeld := fun _ => inferInstance
  typ := fun t f => if t then .int 0 4 else if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some false | 1 => some true | _ => none
  Glob := Fin 3
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun _ => true
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

def FA3 : FreiForm FD3 where
  tab := false
  feld := 0
  zaehl := 0
  hz := by decide
  hpos := by decide
  komm := 1
  hk := by decide
  hzwei := by decide
  kopf := 2
  hkopf := by decide
  nxt := 1
  hnxt := by decide
  hk1 := by decide
  hk2 := by decide
  hf := by decide

def LL3 : LinkFeld FA3 where
  f := 2
  hf := by decide
  h1 := by decide
  h2 := by decide

/-- The bucket heads: field `0` of the bucket table. -/
def HB3 : BucketKopf FA3 where
  bt := true
  hf := 0
  hty := by decide
  hbt := by decide

/-- A clamped number, so that a value can be named without a proof. -/
def zc (v : Int) : Zahl 0 4 := ⟨max 0 (min 4 v), by omega, by omega⟩

/-- A world from the counter, the free head, the free links, the chain links and the bucket heads. -/
def wd3 (st kopf : Int) (nx ln hd : Int → Int) : World FD3 where
  slots := fun t k f =>
    if ht : t = true then (by
      subst ht
      have : FD3.typ true f = .int 0 4 := by simp
      rw [this]; exact zc (hd k))
    else if h0 : f = 0 then (by
      have ht' : t = false := by simpa using ht
      subst ht'
      have : FD3.typ false f = .int 0 255 := by simp [h0]
      rw [this]; exact (⟨0, by decide, by decide⟩ : Zahl 0 255))
    else if h1 : f = 1 then (by
      have ht' : t = false := by simpa using ht
      subst ht'
      have : FD3.typ false f = .int 0 4 := by simp [h0]
      rw [this]; exact zc (nx k))
    else (by
      have ht' : t = false := by simpa using ht
      subst ht'
      have : FD3.typ false f = .int 0 4 := by simp [h0]
      rw [this]; exact zc (ln k))
  globs := fun g => if g = 0 then zc st else if g = 1 then zc st else zc kopf
  spur := []

def nxN : Int → Int := fun _ => 4
def lnW : Int → Int := fun _ => 4
/-- Bucket `0` holds the chain `1`; bucket `1` is empty. -/
def hdW : Int → Int := fun b => if b = 0 then 1 else 4

/-- Slot `3` on the free list; the chain `1` in bucket `0`; slots `0` and `2` live, on no bucket. -/
def wh : World FD3 := wd3 4 3 nxN lnW hdW

theorem stand_wh : FA3.stand wh = 4 := rfl
theorem kopf_wh : FA3.kopfSt wh = 3 := rfl
theorem naechst_wh (j : Int) : FA3.naechst wh j = 4 := rfl
theorem ll_wh (j : Int) : LL3.wert wh j = 4 := by show max 0 (min 4 (lnW j)) = 4; unfold lnW; decide
theorem hd_wh (b : Int) : HB3.wert wh b = hdW b := by
  show max 0 (min 4 (hdW b)) = hdW b
  unfold hdW; split <;> omega

theorem kette_wh : FA3.Kette wh 3 [3] :=
  FreiForm.Kette.cons 3 (by decide) (by decide) [] (by rw [naechst_wh]; exact FreiForm.Kette.nil)

theorem freiOk_wh : FA3.FreiOk wh := by
  refine ⟨[3], by rw [kopf_wh]; exact kette_wh, by decide, ?_⟩
  intro i hi; simp at hi; subst hi; rw [stand_wh]; omega

theorem aufListe_wh (i : Int) : FA3.AufListe wh i ↔ i = 3 := by
  constructor
  · rintro ⟨L, hL, hm⟩
    rw [kopf_wh] at hL
    have := FreiForm.Kette.eindeutig hL kette_wh
    subst this; simpa using hm
  · rintro rfl
    exact ⟨[3], by rw [kopf_wh]; exact kette_wh, by simp⟩

theorem lebt_wh (i : Int) : FA3.Lebt wh i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 3) := by
  unfold FreiForm.Lebt
  rw [aufListe_wh, stand_wh]

/-- Bucket `0` is the chain `1`, bucket `1` is empty. -/
theorem kette0_wh : KetteF 4 (LL3.wert wh) (HB3.wert wh 0) [1] := by
  rw [hd_wh]
  refine KetteF.cons 1 (by decide) (by decide) [] ?_
  rw [ll_wh]
  exact KetteF.nil

theorem kette1_wh : KetteF 4 (LL3.wert wh) (HB3.wert wh 1) [] := by
  rw [hd_wh]
  exact KetteF.nil

/-- **The scenario world meets the hash invariant:** two buckets, each a chain of live slots, disjoint. -/
theorem hashOk_wh : HashOk LL3 HB3 wh := by
  refine ⟨fun b hb0 hb1 => ?_, fun b b' hb0 hb1 hb0' hb1' hne j hj hj' => ?_⟩
  · have hb : b = 0 ∨ b = 1 := by
      have h2 : b < 2 := hb1
      omega
    rcases hb with rfl | rfl
    · refine ⟨[1], kette0_wh, by decide, ?_⟩
      intro i hi; simp at hi; subst hi; exact (lebt_wh 1).mpr (by decide)
    · exact ⟨[], kette1_wh, by decide, by simp⟩
  · have hb : b = 0 ∨ b = 1 := by have h2 : b < 2 := hb1; omega
    have hb' : b' = 0 ∨ b' = 1 := by have h2 : b' < 2 := hb1'; omega
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · obtain ⟨L, hL, hm⟩ := hj'
      have := KetteF.eindeutig hL kette1_wh
      subst this; simp at hm
    · obtain ⟨L, hL, hm⟩ := hj
      have := KetteF.eindeutig hL kette1_wh
      subst this; simp at hm
    · exact absurd rfl hne

/-! ### The contract, the oracle and the environments of the bodies -/

def FV3 : Vertrag FD3 where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem fdarf3 (t : FD3.Tab) : darf FD3 t ([] : List (Res FD3)) := by
  intro w hw; cases hw

def o3 : Orakel FD3 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => false

def r3 : ∀ f : FD3.Fn, World FD3 → Env FD3 (FD3.params f) → RufAusgang f := fun _ _ _ => .logik .vorzustand

/-- The context of a push: the bucket, then the slot. -/
abbrev GP : Ctx := [Ty.index (FD3.count HB3.bt), Ty.index (FD3.count FA3.tab)]

/-- The environment: bucket `bk`, slot `sl`. -/
def rhoP (bk sl : Int) (h1 : 0 ≤ bk) (h2 : bk ≤ 1) (h3 : 0 ≤ sl) (h4 : sl ≤ 3) : Env FD3 GP :=
  .cons (⟨bk, h1, h2⟩ : Wert FD3 (Ty.index (FD3.count HB3.bt))) (.cons (⟨sl, h3, h4⟩ : Wert FD3 (Ty.index (FD3.count FA3.tab))) .nil)

/-- Push the slot into the bucket. -/
def pushK : Block FD3 FV3 false GP [] [] :=
  Block.hashPush LL3 HB3 (.here : Var GP _) (.there .here : Var GP _) rfl (fdarf3 _) rfl (fdarf3 _) .nil

/-- Slot `2` is on no bucket. -/
theorem nicht_auf_2 : ∀ b', 0 ≤ b' → b' < FD3.count HB3.bt →
    ¬ Auf (FD3.count FA3.tab) (LL3.wert wh) (HB3.wert wh b') 2 := by
  intro b' hb0 hb1 hj
  have h2 : b' < 2 := hb1
  have hb : b' = 0 ∨ b' = 1 := by omega
  rcases hb with rfl | rfl
  · obtain ⟨L, hL, hm⟩ := hj
    have := KetteF.eindeutig hL kette0_wh
    subst this; simp at hm
  · obtain ⟨L, hL, hm⟩ := hj
    have := KetteF.eindeutig hL kette1_wh
    subst this; simp at hm

/-- The environment: bucket `0`, slot `2`. -/
def rP02 : Env FD3 GP := rhoP 0 2 (by decide) (by decide) (by decide) (by decide)

theorem rP02_b : (rP02.get (.here : Var GP _)).n = 0 := rfl
theorem rP02_x : (rP02.get (.there .here : Var GP _)).n = 2 := rfl

/-- **`hash_push_zug` on a real world, run:** slot `2` becomes the head of bucket `0`, linked to the old head `1`; the hash
    invariant holds afterwards. -/
theorem push_zeuge :
    ∃ σ' : World FD3, execBlock (V := FV3) o3 0 r3 pushK wh rP02 = .ok σ' rP02 ∧
      HashOk LL3 HB3 σ' ∧ HB3.wert σ' 0 = 2 ∧ LL3.wert σ' 2 = 1 := by
  obtain ⟨σ', he, -, hh, -, -, hh1, hl1⟩ := hash_push_zug o3 0 r3 LL3 HB3 (V := FV3) (l := false) (Γ := GP) (Λ := [])
    (Λ' := []) (.here : Var GP _) (.there .here : Var GP _) rfl (fdarf3 _) rfl (fdarf3 _) .nil wh rP02
    freiOk_wh hashOk_wh (by rw [rP02_x]; exact (lebt_wh 2).mpr (by decide))
    (by rw [rP02_x]; exact nicht_auf_2)
  refine ⟨σ', he, hh, by rw [← rP02_b]; exact hh1.trans rP02_x, ?_⟩
  rw [rP02_x] at hl1
  rw [hl1, rP02_b, hd_wh]
  rfl

/-- The context of a pop: the bucket. -/
abbrev GB : Ctx := [Ty.index (FD3.count HB3.bt)]

def vollB : Endblock FD3 FV3 false GB [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)

def popK : Block FD3 FV3 false GB [] [] :=
  Block.hashPop LL3 HB3 (.here : Var GB _) (fdarf3 _) rfl (fdarf3 _) vollB .nil

/-- The environment: bucket `0`. -/
def rB0 : Env FD3 GB := .cons (⟨0, by decide, by decide⟩ : Wert FD3 (Ty.index (FD3.count HB3.bt))) .nil

theorem rB0_b : (rB0.get (.here : Var GB _)).n = 0 := rfl

/-- **`hash_pop_zug` on a real world, run:** bucket `0` loses its head `1`; the binder holds it; it is live and on no bucket. -/
theorem pop_zeuge :
    ∃ (σ' : World FD3) (k : Wert FD3 (Ty.index (FD3.count FA3.tab))),
      execBlock (V := FV3) o3 0 r3 popK wh rB0 = .ok σ' rB0 ∧ k.n = 1 ∧ HashOk LL3 HB3 σ' ∧ FA3.Lebt σ' k.n ∧
      (∀ b', 0 ≤ b' → b' < FD3.count HB3.bt → ¬ Auf (FD3.count FA3.tab) (LL3.wert σ') (HB3.wert σ' b') k.n) := by
  have hne : HB3.wert wh (rB0.get (.here : Var GB _)).n < FD3.count FA3.tab := by
    rw [rB0_b, hd_wh]; decide
  obtain ⟨σ', k, he, hkn, hh, -, -, hl, hnb⟩ := hash_pop_zug o3 0 r3 LL3 HB3 (V := FV3) (l := false) (Γ := GB)
    (Λ := []) (Λ' := []) (.here : Var GB _) (fdarf3 _) rfl (fdarf3 _) vollB .nil wh rB0 freiOk_wh hashOk_wh hne
  refine ⟨σ', k, he, ?_, hh, hl, hnb⟩
  rw [hkn, rB0_b, hd_wh]; rfl

/-! ### The planted defect: a slot on two buckets -/

def schiebOk : Bool :=
  match execBlock (V := FV3) o3 0 r3 pushK wh (rhoP 1 1 (by decide) (by decide) (by decide) (by decide)) with
  | .ok σ' _ => decide (HB3.wert σ' 0 = 1 ∧ HB3.wert σ' 1 = 1 ∧ LL3.wert σ' 1 = 4)
  | _ => false

theorem schiebOk_wahr : schiebOk = true := by decide +kernel

/-- **A slot pushed into a second bucket while it heads the first breaks the hash table:** both chains contain slot `1`.
    (The hypothesis `hnot` of `hash_push_zug`, "the slot is on no bucket", is what the checker's `N586` establishes.) -/
theorem push_defekt :
    ∃ (σ' : World FD3) (ρ' : Env FD3 GP),
      execBlock (V := FV3) o3 0 r3 pushK wh (rhoP 1 1 (by decide) (by decide) (by decide) (by decide)) = .ok σ' ρ' ∧
      ¬ HashOk LL3 HB3 σ' := by
  have hd := schiebOk_wahr
  unfold schiebOk at hd
  revert hd
  generalize hx : execBlock (V := FV3) o3 0 r3 pushK wh (rhoP 1 1 (by decide) (by decide) (by decide) (by decide)) = o
  cases o with
  | ok σ' ρ =>
    intro hd
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h0, h1, hl⟩ := hd
    refine ⟨σ', ρ, rfl, ?_⟩
    · intro hh
      have hmem : ∀ b, b = 0 ∨ b = 1 → Auf (FD3.count FA3.tab) (LL3.wert σ') (HB3.wert σ' b) 1 := by
        intro b hb
        have hb' : HB3.wert σ' b = 1 := by rcases hb with rfl | rfl; exact h0; exact h1
        rw [hb']
        exact ⟨[1], KetteF.cons 1 (by decide) (by decide) [] (by rw [hl]; exact KetteF.nil), by simp⟩
      exact hh.2 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) 1 (hmem 0 (Or.inl rfl))
        (hmem 1 (Or.inr rfl))
  | zurueck _ _ => intro hd; exact absurd hd (by simp)
  | why _ _ => intro hd; exact absurd hd (by simp)
  | leave _ _ _ => intro hd; exact absurd hd (by simp)
  | next _ _ _ => intro hd; exact absurd hd (by simp)
  | logik _ => intro hd; exact absurd hd (by simp)
  | hardware _ => intro hd; exact absurd hd (by simp)

end HashZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.HashZeuge.hashOk_wh
#print axioms Gabbro.Grammatik.HashZeuge.push_zeuge
#print axioms Gabbro.Grammatik.HashZeuge.pop_zeuge
#print axioms Gabbro.Grammatik.HashZeuge.push_defekt
