module
public import Bruecke.Kette.Quelle
public import Bruecke.Pruefung
public import Grammatik.Parser.Elab.UebersetzePipeline
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


/-!
# Finding F2, measured: without a rank of the call graph the bridge would be FALSE

Three functions over one table `T` (two slots, field `v : 0 .. 10`), in the parser's fragment:

    fn h()  ensures false               { h(); }
    fn g()  ensures T.slots[0].v == 7   { h(); }
    fn f()  ensures T.slots[1].v == 5   { g(); }

Every duty GabbroV states for them HOLDS (`alle_pflichten`): a duty assumes the callees'
contracts for EVERY entry state (`Contract`), and no environment keeps `h`'s (`ensures false`) or
`g`'s (a claim about a slot `g` does not write) -- so each duty is true by vacuity. Premise (b) of
the goal theorem FAILS (`nicht_koerperGutR`): its handler class asks a callee's contract only
where the call is made, and a handler may answer `g` normally where slot 0 happens to be 7 -- then
`f` returns with slot 1 at 0. The rank check refuses the unit (`rang_faellt`: `h` calls itself).
-/

namespace Gabbro.Bruecke.Zyklus

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Bruecke

def uZ : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("v", (0, 10))], breiten := [] }],
    locks := [],
    fns := [
      { name := "f", params := [], kinds := [], res := none, held := [], puts := [],
        gives := [.cmp "==" (.tab "T" "v" (.lit 1)) (.lit 5)], body := [.call "g" []],
        ret := .empty, decreases := none, measureConstants := [] },
      { name := "g", params := [], kinds := [], res := none, held := [], puts := [],
        gives := [.cmp "==" (.tab "T" "v" (.lit 0)) (.lit 7)], body := [.call "h" []],
        ret := .empty, decreases := none, measureConstants := [] },
      { name := "h", params := [], kinds := [], res := none, held := [], puts := [],
        gives := [.fls], body := [.call "h" []], ret := .empty, decreases := none, measureConstants := [] }] }

theorem low_some : (lowerAllg uZ).toOption.isSome = true := by decide +kernel

def PZ : Programm (declOf uZ) := ((lowerAllg uZ).toOption.get low_some).1
def fsZ : List (declOf uZ).Fn := ((lowerAllg uZ).toOption.get low_some).2

theorem lowZ : lowerAllg uZ = .ok (PZ, fsZ) := except_ok_get low_some

theorem getragenZ : GetragenG uZ (fun _ => True) :=
  getragenG_of_bools (by decide) (by decide) (by decide)

/-- The rank check refuses the unit: `h` calls itself. -/
theorem rang_faellt : rangB uZ (rangAuto uZ) = false := by decide

/-- ... and no rank exists at all. -/
theorem kein_rang : ∀ rk, ¬ Rang uZ rk := by
  intro rk h
  have := h ⟨2, by decide⟩ "h" [] (by decide)
  exact Nat.lt_irrefl _ this

/-! ## Every duty holds -- by vacuity -/

def fnF : UFn := uZ.fns[0]'(by decide)
def fnG : UFn := uZ.fns[1]'(by decide)
def fnH : UFn := uZ.fns[2]'(by decide)

/-- The zero state: well-typed, every precondition true. -/
def t0 : Gabbro.Body.State := ⟨fun _ => .int 0, fun _ => .absent⟩

theorem wf_t0 : wfU uZ t0 := by
  intro p sh hp
  cases p with
  | slot c k fld =>
    obtain ⟨t, _, hf⟩ := slotShape_tabIdx _ c fld sh hp
    have ht : t = ⟨0, by decide⟩ := Fin.ext (by have := t.isLt; simp [uZ] at this; omega)
    subst ht
    by_cases hv : fld = "v"
    · subst hv
      have e : sh = .intIn 0 10 := by
        have h2 : ((uZ.tabs.get ⟨0, by decide⟩).cols.find? (fun q => q.1 == "v")).map
            (fun q => Gabbro.Body.Shape.intIn q.2.1 q.2.2) = some (.intIn 0 10) := rfl
        rw [h2] at hf
        exact (Option.some.inj hf).symm
      subst e
      rfl
    · have h2 : (uZ.tabs.get ⟨0, by decide⟩).cols.find? (fun q => q.1 == fld) = none := by
        show [("v", ((0 : Int), (10 : Int)))].find? (fun q => q.1 == fld) = none
        simp only [List.find?]
        have : ("v" == fld) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hv e.symm
        rw [this]
      rw [h2] at hf
      cases hf
  | field c n => simp [shapeOfU] at hp
  | global n => simp [shapeOfU] at hp

/-- No environment keeps `h`'s contract: its promise is `false`. -/
theorem h_unhaltbar (ρ : Gabbro.Body.Env)
    (hc : Gabbro.Body.Contract ρ "h" (preProp (wfU uZ) fnH) (postP uZ fnH)) : False := by
  have := hc t0 ⟨wf_t0, rfl⟩
  simp [postP, postU, ensList, ensClause, ensExpr, clauseProp, clauseAux, chain, andAll,
    resultClause, fnH, uZ, Gabbro.Body.eval] at this

/-- No environment keeps `g`'s contract with its (empty) frame: `g` promises slot 0 is 7 without
    writing it, and at the zero state it is 0. -/
theorem g_unhaltbar (ρ : Gabbro.Body.Env)
    (hc : Gabbro.Body.Contract ρ "g" (preProp (wfU uZ) fnG) (postP uZ fnG))
    (hf : Gabbro.Body.Frame ρ "g" fnG.puts) : False := by
  have := hc t0 ⟨wf_t0, rfl⟩
  have hw : (ρ "g" t0).1.world (.slot "T" 0 "v") = .int 0 :=
    hf t0 _ (by simp [fnG, uZ, Gabbro.Body.Place.carrier])
  simp [postP, postU, ensList, ensClause, ensExpr, ensSide, sideExpr, slotPlace, opOf, idxExpr, clauseProp,
    clauseAux, chain, andAll, resultClause, fnG, uZ, Gabbro.Body.eval, hw, Gabbro.Body.binop] at this

theorem suche_g : fnSuch uZ "g" = some fnG := rfl
theorem suche_h : fnSuch uZ "h" = some fnH := rfl

/-- **Every duty GabbroV states for the unit holds.** -/
theorem alle_pflichten : ∀ c : Fin uZ.fns.length, ∃ body, zuBody uZ (fnAt uZ c) = some body ∧
    meetsU uZ (wfU uZ) (fnAt uZ c) body := by
  intro c
  match c with
  | ⟨0, _⟩ =>
    refine ⟨_, rfl, fun ρ s _ _ => ?_⟩
    show hyps uZ (wfU uZ) ρ ["g"] _
    simp only [hyps, suche_g]
    intro hc hf
    exact (g_unhaltbar ρ hc hf).elim
  | ⟨1, _⟩ =>
    refine ⟨_, rfl, fun ρ s _ _ => ?_⟩
    show hyps uZ (wfU uZ) ρ ["h"] _
    simp only [hyps, suche_h]
    intro hc _
    exact (h_unhaltbar ρ hc).elim
  | ⟨2, _⟩ =>
    refine ⟨_, rfl, fun ρ s _ _ => ?_⟩
    show hyps uZ (wfU uZ) ρ ["h"] _
    simp only [hyps, suche_h]
    intro hc _
    exact (h_unhaltbar ρ hc).elim

/-! ## Premise (b) fails -/

def fI : (declOf uZ).Fn := ⟨0, by decide⟩
def gI : (declOf uZ).Fn := ⟨1, by decide⟩
def tT : (declOf uZ).Tab := ⟨0, by decide⟩
def vF : (declOf uZ).Feld tT := ⟨0, by decide⟩

theorem typZ : ∀ (t : (declOf uZ).Tab) (f : (declOf uZ).Feld t), (declOf uZ).typ t f = .int 0 10 := by
  intro t f
  have ht : t = tT := Fin.ext (by have := t.isLt; simp [uZ] at this; show t.val = 0; omega)
  subst ht
  have hf : f = vF := Fin.ext (by
    have h1 : f.val < 1 := f.isLt
    show f.val = 0
    omega)
  subst hf
  rfl

/-- The world where slot 0 holds 7 and slot 1 holds 0. -/
def σ7 : World (declOf uZ) where
  slots := fun t k f => (typZ t f).symm ▸
    (if k = 0 then (⟨7, by decide, by decide⟩ : Zahl 0 10) else ⟨0, by decide, by decide⟩)
  globs := fun g => nomatch g
  spur := []

theorem σ7_0 : ((σ7.slots tT 0 vF : Zahl 0 10)).n = 7 := rfl
theorem σ7_1 : ((σ7.slots tT 1 vF : Zahl 0 10)).n = 0 := rfl

def O0 : Orakel (declOf uZ) where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- **The handler**: `g` answers normally, leaving the world as it is, exactly where slot 0 holds 7
    -- where `g`'s contract is met; every other call is a hardware stop. -/
def RZ : ∀ f : (declOf uZ).Fn, World (declOf uZ) → Env (declOf uZ) ((declOf uZ).params f) →
    RufAusgang f :=
  fun f σ _ => if h : f = gI then h ▸ (if ((σ.slots tT 0 vF : Zahl 0 10)).n = 7 then
      (RufAusgang.ok σ () : RufAusgang gI) else .hardware .ieee) else .hardware .ieee

theorem rz_ok {f : (declOf uZ).Fn} {σ σ' : World (declOf uZ)} {ρ : Env (declOf uZ) ((declOf uZ).params f)}
    {v : ErgVal (declOf uZ) ((declOf uZ).erg f)} (h : RZ f σ ρ = .ok σ' v) :
    f = gI ∧ σ' = σ ∧ ((σ.slots tT 0 vF : Zahl 0 10)).n = 7 := by
  unfold RZ at h
  split at h
  · rename_i hf
    subst hf
    split at h
    · rename_i h7
      cases h
      exact ⟨rfl, rfl, h7⟩
    · cases h
  · cases h

theorem rz_nlogik (f : (declOf uZ).Fn) (σ : World (declOf uZ)) (ρ : Env (declOf uZ) ((declOf uZ).params f))
    (e : Logik (declOf uZ)) : RZ f σ ρ ≠ .logik e := by
  unfold RZ
  split
  · rename_i hf
    subst hf
    split <;> (intro h; cases h)
  · intro h; cases h

theorem gesenktZ : Gesenkt uZ PZ := gesenkt_of (fun c => getragenZ.ohneReq c True.intro)
  (fun c => getragenZ.ohneTransition c True.intro) lowZ

theorem tabZ : tabIdx uZ.tabs "T" = .ok tT := rfl

theorem feldZ : ∃ fh : FieldHit uZ tT, fieldHit uZ tT "v" = .ok fh ∧ fh.idx = vF :=
  ⟨_, rfl, rfl⟩

/-- The Body place of slot `k` holds the G slot `k`, in any related world. -/
theorem platz {σ : World (declOf uZ)} {w : Gabbro.Body.World} (hW : WRel uZ σ w) (k : Int) :
    w (.slot "T" k "v") = .int ((σ.slots tT k vF : Zahl 0 10)).n := by
  obtain ⟨fh, hfh, hidx⟩ := feldZ
  rw [wrel_lies_k uZ hW "T" tT tabZ "v" fh hfh k, hidx]
  rfl

/-- The handler keeps every contract at its place (and every frame): `g`'s answer is the world
    it was asked in, where slot 0 holds 7. -/
theorem rz_respektiert : RespektiertRahmen PZ RZ := by
  refine ⟨fun f σ ρ _ σ' v h => ?_, fun f σ ρ σ' v h => ?_⟩
  · obtain ⟨hf, hs, h7⟩ := rz_ok h
    subst hf
    rw [hs]
    have hW := wrel_enc uZ σ (fun _ => .int 0)
    refine (post_iff gesenktZ gI (getragenZ.art gI True.intro) getragenZ.tab (getragenZ.frei gI True.intro) (getragenZ.olds gI True.intro)
      (getragenZ.post gI True.intro) (getragenZ.boolErg gI True.intro) getragenZ.boolTab σ σ ρ v (eintritt uZ gI σ ρ) (eintritt uZ gI σ ρ) hW
      (eintritt_lrel gI σ ρ) hW).mp ?_
    have hv := platz hW 0
    rw [h7] at hv
    have hwf := wf_of_wrel uZ getragenZ.boolTab hW
    simp [postU, ensList, ensClause, ensExpr, ensSide, sideExpr, slotPlace, opOf, idxExpr, clauseProp,
      clauseAux, chain, andAll, resultClause, fnAt, gI, uZ, Gabbro.Body.eval, Gabbro.Body.binop,
      eintritt] at hv ⊢
    exact ⟨hwf, hv⟩
  · obtain ⟨_, hs, _⟩ := rz_ok h
    rw [hs]
    exact ⟨Rahmen.refl _ _ _, rfl⟩

theorem rz_ohneV : OhneVorbedingung RZ := fun g σ ρ e h _ _ => absurd h (rz_nlogik g σ ρ e)

theorem rahmenO0 : RahmenO O0 := fun a => nomatch a

theorem regLokal0 : RegLokal O0 := ⟨(fun r => nomatch r), (fun g => nomatch g)⟩

/-- **Premise (b) FAILS for `f`**: from the world where slot 0 holds 7 and slot 1 holds 0, with
    the handler above, `f`'s body returns -- and `f`'s `ensures` (slot 1 is 5) is false there. -/
theorem nicht_koerperGutR : ¬ KoerperGutR PZ 0 fI := by
  intro hK
  obtain ⟨b0, hb0, hPb⟩ := gesenktZ.rumpf fI
  change lowBody uZ fI [.call "g" []] .empty = .ok b0 at hb0
  obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ := lowBody_cons_ok fI .empty (.call "g" []) [] rfl hb0
  simp only [lowBodyAt, List.length_nil, lowBodyF] at hrest
  have hx : stmtBody uZ (fnAt uZ fI) (.call "g" []) =
      some (.call "g" [] [] (.lit (.bool true))) := rfl
  let ρ₀ : Env (declOf uZ) (ctxOf uZ fI) := .nil
  have hW0 : WRel uZ σ7 (eintritt uZ fI σ7 .nil).world := wrel_enc uZ σ7 _
  have hL0 : LRel (fnAt uZ fI) 0 ρ₀ (eintritt uZ fI σ7 .nil).local' := fun p j hj => by
    simp [fnAt, fI, uZ, paramPos] at hj
  obtain ⟨callee, σr, envA, hname, _, hsl, _, _, _, hcases, _⟩ :=
    lowCall_sim fI (show lowCall uZ fI "g" [] = .ok ⟨Λ', gst⟩ from hgst) hx (getragenZ.art fI True.intro) getragenZ.tab (fun c => getragenZ.namen c True.intro) (fun c => (getragenZ.art c True.intro).2.1) O0 0 RZ σ7 ρ₀ _ hW0 hL0
  have hcallee : callee = gI := by
    rcases callee with ⟨_ | _ | _ | n, hc⟩
    · simp [fnAt, uZ] at hname
    · rfl
    · simp [fnAt, uZ] at hname
    · exact absurd hc (by simp [uZ])
  subst hcallee
  have h7 : ((σr.slots tT 0 vF : Zahl 0 10)).n = 7 := by rw [hsl]; rfl
  have hR : RZ gI σr envA = .ok σr () := by
    unfold RZ; rw [dif_pos rfl]; simp only [h7, ↓reduceIte]
  rcases hcases with ⟨σ', v, hR', hex⟩ | ⟨e, hR', _⟩ | ⟨e, hR', _⟩
  · rw [hR] at hR'
    cases hR'
    have hrun : execEnd O0 0 RZ (Endblock.cons gst rest) σ7 ρ₀ = execEnd O0 0 RZ rest σr ρ₀ := by
      simp only [execEnd, hex]
    obtain ⟨σ'', v'', hend, hsl'', _⟩ := lowEnd_sim fI (show lowEndF uZ fI .empty (Λ := Λ') = .ok rest from hrest) (rfl : endBody uZ (fnAt uZ fI) .empty = some [])
      (getragenZ.art fI True.intro) getragenZ.tab O0 0 RZ σr ρ₀ _ (wrel_slots uZ hsl hW0) hL0
    have hX := execEnd_heq (V := verOf uZ fI) O0 0 RZ (ctxParams_eq uZ fI).symm
      (anfangRes_eq uZ fI).symm (PZ.rumpf fI) (Endblock.cons gst rest) hPb σ7 .nil ρ₀ HEq.rfl
    have hmain := (zurueck_heq (ctxParams_eq uZ fI).symm _ _ hX σ'' v'').mpr (hrun.trans hend)
    have hens := (hK O0 rahmenO0 regLokal0 RZ rz_respektiert rz_ohneV σ7 .nil
      (reqAmEintritt_wahr gesenktZ fI σ7 .nil)).1 σ'' v'' hmain
    let s1 : Gabbro.Body.State := ⟨enc uZ σ'' (fun _ => .int 0), (eintritt uZ fI σ7 .nil).local'⟩
    have hW1 : WRel uZ σ'' s1.world := wrel_enc uZ σ'' _
    have hpost := (post_iff gesenktZ fI (getragenZ.art fI True.intro) getragenZ.tab (getragenZ.frei fI True.intro)
      (getragenZ.olds fI True.intro) (getragenZ.post fI True.intro) (getragenZ.boolErg fI True.intro) getragenZ.boolTab σ7 σ'' .nil v'' _ s1 hW0
      (eintritt_lrel fI σ7 .nil) hW1).mpr hens
    have h1 := platz hW1 1
    have h0 : ((σ''.slots tT 1 vF : Zahl 0 10)).n = 0 := by rw [hsl'', hsl]; rfl
    rw [h0] at h1
    simp [postU, ensList, ensClause, ensExpr, ensSide, sideExpr, slotPlace, opOf, idxExpr,
      clauseProp, clauseAux, chain, andAll, resultClause, fnAt, fI, uZ, Gabbro.Body.eval,
      Gabbro.Body.binop, s1] at hpost h1
    rw [hpost.2] at h1
    cases h1
  · rw [hR] at hR'; cases hR'
  · rw [hR] at hR'; cases hR'

#print axioms alle_pflichten
#print axioms nicht_koerperGutR

end Gabbro.Bruecke.Zyklus
