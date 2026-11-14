module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Bruecke.Anweisung.Zweig.Strecke
public import Bruecke.Kette.Mass.Abstieg
public import Bruecke.Kette.Mass.Senkung
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Pipeline
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
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
@[expose] public section

/-!
# Witness: the measure computed from `decreases` clauses carries recursion

    fn down(k : 0..9) decreases k { if 0 < k { down(0); } }
    fn ping(k : 0..9) decreases k { if 0 < k { pong(0); } }
    fn pong(k : 0..9) decreases k { if 0 < k { ping(0); } }
    fn top(k : 0..9)  decreases k { if 0 < k { down(9); } }

as the elaborated unit (a lowered-unit witness, not a measured source-parser acceptance claim).
The measure is NOT chosen here: it is `massQuelle unit`, the call-graph rank and the value of
each function's `decreases` clause. Every duty is the source duty `meetsUQ`, turned into the
measure duty `meetsUM` by `meetsUM_of_meetsUQ`:

* the cycle calls (`down → down`, `ping → pong → ping`) are admitted by the `decreases` value,
  `0` below the entry value `k > 0`;
* the acyclic call `top → down` is admitted by the computed rank alone: `down` does not reach
  `top` (`top_kein_zyklus`), while its source value does NOT fall (`top_wert_steigt`: the call
  enters `down` with `k = 9`) -- so the rank is doing real work, not the clause.

The exported canonical measure of the lowered unit equals the Body source value at the
bridge's entry (`wert_zeuge`), and `bruecke_nutzer_M` delivers premise (b) of the goal theorem
for the whole unit (`nutzer_quelle_zeuge`).
-/

namespace Gabbro.Bruecke.MassQuelleZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

/-- `fn name(k : 0..9) decreases k { if 0 < k { callee(arg); } }` -/
def fnRuf (name callee : String) (arg : Int) : UFn :=
  { name := name, params := [("k", .int 0 9)], kinds := [.int], res := none,
    held := [], puts := [], gives := [],
    body := [.ifBeg (.cmp "<" (.lit 0) (.param "k")), .call callee [.val (.lit arg)], .ifElse,
      .blkEnd],
    ret := .empty, decreases := some (.variable "k") }

def down : UFn := fnRuf "down" "down" 0
def ping : UFn := fnRuf "ping" "pong" 0
def pong : UFn := fnRuf "pong" "ping" 0
def top : UFn := fnRuf "top" "down" 9

def unit : UProg := { tabs := [], locks := [], fns := [down, ping, pong, top] }

/-- The Body translation of `fnRuf _ g arg`. -/
def rumpf (g : String) (arg : Int) : List Gabbro.Body.Stmt :=
  [.ite (.bin .lt (.lit (.int 0)) (.name "k"))
    [.call g ["k"] [.lit (.int arg)] (.hasShape "k" (.intIn 0 9))] []]

/-! ## 1. The unit, lowered with its measures -/

theorem callees : calleesOf down = ["down"] ∧ calleesOf ping = ["pong"] ∧
    calleesOf pong = ["ping"] ∧ calleesOf top = ["down"] := ⟨by cbv, by cbv, by cbv, by cbv⟩

theorem suche : fnSuch unit "down" = some down ∧ fnSuch unit "ping" = some ping ∧
    fnSuch unit "pong" = some pong ∧ fnSuch unit "top" = some top :=
  ⟨by cbv, by cbv, by cbv, by cbv⟩

theorem lesen : zuBodyZ unit down = some (rumpf "down" 0) ∧
    zuBodyZ unit ping = some (rumpf "pong" 0) ∧ zuBodyZ unit pong = some (rumpf "ping" 0) ∧
    zuBodyZ unit top = some (rumpf "down" 9) := ⟨by cbv, by cbv, by cbv, by cbv⟩

theorem selbst : ∀ c : Fin unit.fns.length, fnSuch unit (fnAt unit c).name = some (fnAt unit c) := by
  rintro ⟨index, bound⟩
  have small : index < 4 := bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl
  all_goals cbv

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply lowering_ok_mass
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 4 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl
    all_goals refine ⟨?_, ?_, ?_⟩ <;> cbv

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1

def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

theorem getragen : GetragenG unit (fun _ => True) :=
  getragenG_of_bools (by cbv) (by cbv) (by cbv)

theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 4 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl
    all_goals cbv
  · intro n
    rcases n with _ | _ | _ | _ | n <;> constructor <;> cbv

/-! ## 2. The computed measure on the unit -/

/-- The value of `k` at an entry. -/
def kWert (t : Gabbro.Body.State) : Nat :=
  match t.local' "k" with
  | .int n => n.toNat
  | _ => 0

/-- **The computed source value is `k`** for every function whose clause is `decreases k`. -/
theorem quellZahl_eq {n : String} {gf : UFn} (hgf : fnSuch unit n = some gf)
    (hp : gf.params = [("k", .int 0 9)]) (hd : gf.decreases = some (.variable "k"))
    (t : Gabbro.Body.State) : quellZahl unit n t = kWert t := by
  have hpos : paramPos gf.params "k" = .ok 0 := by
    rw [hp]
    simp [paramPos]
  unfold quellZahl kWert
  rw [hgf]
  simp only [massTupel, hd, quellWert, nameU, hpos]
  cases t.local' "k" <;> rfl

theorem fnRuf_quell (name callee : String) (arg : Int)
    (h : fnSuch unit name = some (fnRuf name callee arg)) (t : Gabbro.Body.State) :
    quellZahl unit name t = kWert t := quellZahl_eq h rfl rfl t

/-- Everything `down` reaches is `down`. -/
theorem nur_down {a b : String} (h : ErreichtU unit a b) : a = "down" → b = "down" := by
  induction h with
  | kante hf hg =>
    intro ha
    subst ha
    rw [suche.1] at hf
    cases hf
    rw [callees.1] at hg
    simpa using hg
  | weiter _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)

/-- **`top → down` is an acyclic edge**: `down` never reaches `top`. -/
theorem top_kein_zyklus : ¬ ZyklusU unit "top" "down" := by
  unfold ZyklusU UnterU
  rintro (h | h)
  · exact absurd h (by simp)
  · exact absurd (nur_down h rfl) (by simp)

/-- **Non-degeneracy**: on the edge `top → down` the source value does not fall -- the call
    enters `down` with `k = 9`, at least `top`'s own entry value. Only the rank admits it. -/
theorem top_wert_steigt (s t : Gabbro.Body.State) (n : Int) (hs : s.local' "k" = .int n)
    (hn : n ≤ 9) (ht : t.local' "k" = .int 9) :
    ¬ quellZahl unit "down" t < quellZahl unit "top" s := by
  rw [fnRuf_quell "down" "down" 0 suche.1, fnRuf_quell "top" "down" 9 suche.2.2.2]
  simp only [kWert, hs, ht]
  omega

theorem pre_eq (name callee : String) (arg : Int) :
    preExpr (fnRuf name callee arg) = .hasShape "k" (.intIn 0 9) := by cbv

theorem post_eq (name callee : String) (arg : Int) (s s' : Gabbro.Body.State)
    (r : Option Gabbro.Body.Value) :
    (postU unit (wfU unit) (fnRuf name callee arg) s s' r).getD False = wfU unit s' := rfl

/-! ## 3. The source duties -/

/-- **The source duty of every function of the unit**, under the guard `unterQ` of its callee:
    for `0 < k` the call enters with `k = arg`; for `k = 0` nothing runs. -/
theorem rumpf_meets (name g : String) (arg : Int) (h0 : 0 ≤ arg) (h9 : arg ≤ 9) (gf : UFn)
    (hgf : fnSuch unit g = some gf) (hcal : calleesOf (fnRuf name g arg) = [g])
    (hpreg : preExpr gf = .hasShape "k" (.intIn 0 9))
    (hpostg : ∀ s s' r, (postU unit (wfU unit) gf s s' r).getD False = wfU unit s')
    (hguard : ∀ s t : Gabbro.Body.State, 0 < kWert s → kWert t = arg.toNat →
      unterQ unit (fnRuf name g arg) s g t) :
    meetsUQ unit (wfU unit) (fnRuf name g arg) (rumpf g arg) := by
  intro ρ s hW hp
  rw [hcal]
  simp only [hypsM, hgf]
  intro hC _
  rw [pre_eq] at hp
  have hk : (s.local' "k").hasShape (.intIn 0 9) = true := by
    simpa only [Gabbro.Body.eval, Option.some.injEq, Gabbro.Body.Value.bool.injEq] using hp
  show ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ (rumpf g arg) s) = some s' ∧
    (postU unit (wfU unit) (fnRuf name g arg) s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρ (rumpf g arg) s))).getD False
  cases hv : s.local' "k" with
  | int n =>
    rw [hv] at hk
    have hn : 0 ≤ n ∧ n ≤ 9 := by simpa using hk
    by_cases hpos : 0 < n
    · let t : Gabbro.Body.State :=
        ⟨s.world, Gabbro.Body.bindAll ["k"] [.int arg] (fun _ => .absent)⟩
      have htk : t.local' "k" = .int arg := by
        simp [t, Gabbro.Body.bindAll, Gabbro.Body.bindLocal]
      have hpt : Gabbro.Body.eval t (.hasShape "k" (.intIn 0 9)) = some (.bool true) := by
        simp [Gabbro.Body.eval, htk, Gabbro.Body.Value.hasShape_int_intIn, h0, h9]
      have hks : 0 < kWert s := by
        simp only [kWert, hv]
        omega
      have hkt : kWert t = arg.toNat := by
        simp only [kWert, htk]
      have hw : (postU unit (wfU unit) gf t (ρ g t).1 (ρ g t).2).getD False :=
        hC t ⟨hguard s t hks hkt, hW, by rw [hpreg]; exact hpt⟩
      rw [hpostg] at hw
      let s' : Gabbro.Body.State := ⟨(ρ g t).1.world, s.local'⟩
      have hcall : Gabbro.Body.step ρ
          (.call g ["k"] [.lit (.int arg)] (.hasShape "k" (.intIn 0 9))) s = .running s' := by
        change (match Gabbro.Body.eval t (.hasShape "k" (.intIn 0 9)) with
          | some (.bool true) => Gabbro.Body.Outcome.running s'
          | _ => .stuck) = .running s'
        rw [hpt]
      have hc : Gabbro.Body.eval s (.bin .lt (.lit (.int 0)) (.name "k")) =
          some (.bool true) := by
        simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, hpos]
      have run : Gabbro.Body.exec ρ (rumpf g arg) s = .running s' := by
        simp only [rumpf, Gabbro.Body.exec, step_ite_wahr ρ hc, hcall]
      refine ⟨s', ?_, ?_⟩
      · rw [run] <;> rfl
      · rw [post_eq]
        exact hw
    · have hc : Gabbro.Body.eval s (.bin .lt (.lit (.int 0)) (.name "k")) =
          some (.bool false) := by
        simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, hpos]
      have run : Gabbro.Body.exec ρ (rumpf g arg) s = .running s := by
        simp only [rumpf, Gabbro.Body.exec, step_ite_falsch ρ hc]
      refine ⟨s, ?_, ?_⟩
      · rw [run] <;> rfl
      · rw [post_eq]
        exact hW
  | _ =>
    rw [hv] at hk
    simp at hk

/-- A cycle call with `k = 0` from an entry with `k > 0`: the `decreases` value falls. -/
theorem guard_zyklus (name g callee : String) (hname : fnSuch unit name = some (fnRuf name g 0))
    (hg : fnSuch unit g = some (fnRuf g callee 0)) :
    ∀ s t : Gabbro.Body.State, 0 < kWert s → kWert t = (0 : Int).toNat →
      unterQ unit (fnRuf name g 0) s g t := by
  intro s t hs ht
  refine Or.inr ?_
  show quellZahl unit g t < quellZahl unit name s
  rw [fnRuf_quell g callee 0 hg, fnRuf_quell name g 0 hname, ht]
  exact hs

/-- The acyclic call `top → down`: admitted by the rank. -/
theorem guard_top : ∀ s t : Gabbro.Body.State, 0 < kWert s → kWert t = (9 : Int).toNat →
    unterQ unit top s "down" t :=
  fun _ _ _ _ => Or.inl top_kein_zyklus

/-- **The measure duties of the unit, under the computed measure.** -/
theorem pflichten : MassPflichtU unit (fun _ => True) (massQuelle unit) := by
  apply massPflichtU_quelle (fun c _ => selbst c)
  intro ⟨c, hc⟩ _
  rcases c with _ | _ | _ | _ | c
  · exact ⟨rumpf "down" 0, lesen.1, rumpf_meets "down" "down" 0 (by omega) (by omega) down
      suche.1 callees.1 (pre_eq _ _ _) (post_eq _ _ _)
      (guard_zyklus "down" "down" "down" suche.1 suche.1)⟩
  · exact ⟨rumpf "pong" 0, lesen.2.1, rumpf_meets "ping" "pong" 0 (by omega) (by omega) pong
      suche.2.2.1 callees.2.1 (pre_eq _ _ _) (post_eq _ _ _)
      (guard_zyklus "ping" "pong" "ping" suche.2.1 suche.2.2.1)⟩
  · exact ⟨rumpf "ping" 0, lesen.2.2.1, rumpf_meets "pong" "ping" 0 (by omega) (by omega) ping
      suche.2.1 callees.2.2.1 (pre_eq _ _ _) (post_eq _ _ _)
      (guard_zyklus "pong" "ping" "pong" suche.2.2.1 suche.2.1)⟩
  · exact ⟨rumpf "down" 9, lesen.2.2.2, rumpf_meets "top" "down" 9 (by omega) (by omega) down
      suche.1 callees.2.2.2 (pre_eq _ _ _) (post_eq _ _ _) guard_top⟩
  · have hh : c + 4 < 4 := hc
    omega

/-! ## 4. The canonical measure, and the whole chain -/

/-- **Preservation on the fixture**: the lowered unit exports a measure, and its canonical value
    at every entry of `down` is the Body source value at the bridge's entry state. -/
theorem wert_zeuge : ∃ ex, Parser.Measures.lowerMeasures unit = .ok ex ∧
    ∀ (σ : World (declOf unit)) (ρ : Env (declOf unit) ((declOf unit).params ⟨0, by decide⟩)),
      ex.mass.wert ⟨0, by decide⟩ σ ρ =
        [quellZahl unit "down" (eintritt unit ⟨0, by decide⟩ σ ρ)] := by
  obtain ⟨ex, hex, _⟩ := Parser.Measures.lowerAllg_measures unit program functions lowered
  refine ⟨ex, hex, fun σ ρ => ?_⟩
  have hN : NamenEindeutig (fnAt unit ⟨0, by decide⟩) := by
    unfold NamenEindeutig
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  rw [← massTupel_eintritt ex ⟨0, by decide⟩ hN σ ρ]
  simp only [quellZahl, suche.1]
  rfl

/-- **All premises of the measure chain hold together under the computed measure** on a unit
    with recursion, mutual recursion and an acyclic call the source value alone does not
    admit, and premise (b) of the goal theorem follows. -/
theorem nutzer_quelle_zeuge :
    nullB unit = true ∧ GetragenG unit (fun _ => True) ∧
    MassPflichtU unit (fun _ => True) (massQuelle unit) ∧
    Zielsatz.NutzerPflicht (einheitAllg unit program (by cbv)) := by
  have hPtr : SchnittstellenPflichtTeil unit (fun _ => True) :=
    fun P fs hlow c _ => interfaces P fs hlow c
  have hOpen : OffenePflicht unit (fun _ => True) := fun c hc => (hc True.intro).elim
  exact ⟨by cbv, getragen, pflichten,
    bruecke_nutzer_M lowered getragen (massQuelle unit) pflichten hPtr hOpen (by cbv)
      (fun _ _ hc => (hc True.intro).elim)⟩

#print axioms nutzer_quelle_zeuge

end Gabbro.Bruecke.MassQuelleZeuge
