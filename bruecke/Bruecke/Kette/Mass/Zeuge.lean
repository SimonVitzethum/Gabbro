module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Bruecke.Anweisung.Zweig.Strecke
import Grammatik.Parser.Stmt.LibraryFixtureProofs
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
# Witness: recursion and mutual recursion carried by the measure duties

    fn down(k : 0..9) { if 0 < k { down(0); } }
    fn ping(k : 0..9) { if 0 < k { pong(0); } }
    fn pong(k : 0..9) { if 0 < k { ping(0); } }

as the elaborated unit (a lowered-unit witness, not a measured source-parser acceptance claim).
`down` calls itself, `ping` and `pong` call each other: the rank gate refuses the unit
(`rang_faellt`, `kein_rang`), and the old duty `meetsU` would assume each function's own
contract. Under the measure `k` (`mass`) every call is made with `k = 0` from an entry with
`0 < k`, so each `meetsUM` duty is proved from the bounded contract alone, the recursive call
is actually taken (non-degenerate), and `bruecke_nutzer_M` delivers premise (b) of the goal
theorem for the whole unit.
-/

namespace Gabbro.Bruecke.MassZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

/-- `fn name(k : 0..9) { if 0 < k { callee(0); } }` -/
def fnRuf (name callee : String) : UFn :=
  { name := name, params := [("k", .int 0 9)], kinds := [.int], res := none,
    held := [], puts := [], gives := [],
    body := [.ifBeg (.cmp "<" (.lit 0) (.param "k")), .call callee [.val (.lit 0)], .ifElse,
      .blkEnd],
    ret := .empty }

def down : UFn := fnRuf "down" "down"
def ping : UFn := fnRuf "ping" "pong"
def pong : UFn := fnRuf "pong" "ping"

def unit : UProg := { tabs := [], locks := [], fns := [down, ping, pong] }

/-- The Body translation of `fnRuf _ g`. -/
def rumpf (g : String) : List Gabbro.Body.Stmt :=
  [.ite (.bin .lt (.lit (.int 0)) (.name "k"))
    [.call g ["k"] [.lit (.int 0)] (.hasShape "k" (.intIn 0 9))] []]

/-! ## 1. The unit is recursive, and lowered -/

theorem rang_faellt : rangB unit (rangAuto unit) = false := by cbv

/-- No call-graph rank exists: `down` calls itself. -/
theorem kein_rang : ∀ rk, ¬ Rang unit rk := by
  intro rk h
  have := h ⟨0, by decide⟩ "down" [.val (.lit 0)] (CallsIn.discard (by decide))
  exact Nat.lt_irrefl _ this

theorem callees : calleesOf down = ["down"] ∧ calleesOf ping = ["pong"] ∧
    calleesOf pong = ["ping"] := ⟨by cbv, by cbv, by cbv⟩

theorem suche : fnSuch unit "down" = some down ∧ fnSuch unit "ping" = some ping ∧
    fnSuch unit "pong" = some pong := ⟨by cbv, by cbv, by cbv⟩

theorem lesen : zuBodyZ unit down = some (rumpf "down") ∧ zuBodyZ unit ping = some (rumpf "pong") ∧
    zuBodyZ unit pong = some (rumpf "ping") := ⟨by cbv, by cbv, by cbv⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals constructor <;> cbv

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1

def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

theorem getragen : GetragenG unit (fun _ => True) :=
  getragenG_of_bools (by cbv) (by cbv) (by cbv)

theorem interfaces : SchnittstellenPflicht unit := by
  apply witness_interfaces_empty
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals cbv
  · intro n
    rcases n with _ | _ | _ | n <;> constructor <;> cbv

/-! ## 2. The measure and the duties -/

/-- The value of `k` at an entry. -/
def kWert (t : Gabbro.Body.State) : Nat :=
  match t.local' "k" with
  | .int n => n.toNat
  | _ => 0

/-- The unit's measure: `k`, for every function (what `decreases k` states). -/
def mass : MassU where
  Wert := Nat
  lt := fun a b => a < b
  wf := Nat.lt_wfRel.wf
  mass := fun _ t => kWert t

theorem pre_eq (name callee : String) :
    preExpr (fnRuf name callee) = .hasShape "k" (.intIn 0 9) := by cbv

theorem post_eq (name callee : String) (s s' : Gabbro.Body.State) (r : Option Gabbro.Body.Value) :
    (postU unit (wfU unit) (fnRuf name callee) s s' r).getD False = wfU unit s' := rfl

/-- **The duty of every function of the unit**, proved under the bounded contract of its
    callee: for `0 < k` the call enters with `k = 0`, strictly below; for `k = 0` nothing runs. -/
theorem rumpf_meets (name g : String) (gf : UFn) (hgf : fnSuch unit g = some gf)
    (hcal : calleesOf (fnRuf name g) = [g])
    (hpreg : preExpr gf = .hasShape "k" (.intIn 0 9))
    (hpostg : ∀ s s' r, (postU unit (wfU unit) gf s s' r).getD False = wfU unit s') :
    meetsUM unit (wfU unit) mass (fnRuf name g) (rumpf g) := by
  intro ρ s hW hp
  rw [hcal]
  simp only [hypsM, hgf]
  intro hC _
  rw [pre_eq] at hp
  have hk : (s.local' "k").hasShape (.intIn 0 9) = true := by
    simpa only [Gabbro.Body.eval, Option.some.injEq, Gabbro.Body.Value.bool.injEq] using hp
  show ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ (rumpf g) s) = some s' ∧
    (postU unit (wfU unit) (fnRuf name g) s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρ (rumpf g) s))).getD False
  cases hv : s.local' "k" with
  | int n =>
    rw [hv] at hk
    have hn : 0 ≤ n ∧ n ≤ 9 := by simpa using hk
    by_cases h0 : 0 < n
    · let t : Gabbro.Body.State :=
        ⟨s.world, Gabbro.Body.bindAll ["k"] [.int 0] (fun _ => .absent)⟩
      have htk : t.local' "k" = .int 0 := by
        simp [t, Gabbro.Body.bindAll, Gabbro.Body.bindLocal]
      have hpt : Gabbro.Body.eval t (.hasShape "k" (.intIn 0 9)) = some (.bool true) := by
        simp [Gabbro.Body.eval, htk, Gabbro.Body.Value.hasShape_int_intIn]
      have hlt : kWert t < kWert s := by
        simp only [kWert, htk, hv]
        omega
      have hw : (postU unit (wfU unit) gf t (ρ g t).1 (ρ g t).2).getD False :=
        hC t ⟨hlt, hW, by rw [hpreg]; exact hpt⟩
      rw [hpostg] at hw
      let s' : Gabbro.Body.State := ⟨(ρ g t).1.world, s.local'⟩
      have hcall : Gabbro.Body.step ρ
          (.call g ["k"] [.lit (.int 0)] (.hasShape "k" (.intIn 0 9))) s = .running s' := by
        change (match Gabbro.Body.eval t (.hasShape "k" (.intIn 0 9)) with
          | some (.bool true) => Gabbro.Body.Outcome.running s'
          | _ => .stuck) = .running s'
        rw [hpt]
      have hc : Gabbro.Body.eval s (.bin .lt (.lit (.int 0)) (.name "k")) =
          some (.bool true) := by
        simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, h0]
      have run : Gabbro.Body.exec ρ (rumpf g) s = .running s' := by
        simp only [rumpf, Gabbro.Body.exec, step_ite_wahr ρ hc, hcall]
      refine ⟨s', ?_, ?_⟩
      · rw [run] <;> rfl
      · rw [post_eq]
        exact hw
    · have hc : Gabbro.Body.eval s (.bin .lt (.lit (.int 0)) (.name "k")) =
          some (.bool false) := by
        simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, h0]
      have run : Gabbro.Body.exec ρ (rumpf g) s = .running s := by
        simp only [rumpf, Gabbro.Body.exec, step_ite_falsch ρ hc]
      refine ⟨s, ?_, ?_⟩
      · rw [run] <;> rfl
      · rw [post_eq]
        exact hW
  | _ =>
    rw [hv] at hk
    simp at hk

theorem pflichten : MassPflichtU unit (fun _ => True) mass := by
  intro ⟨c, hc⟩ _
  rcases c with _ | _ | _ | c
  · exact ⟨rumpf "down", lesen.1,
      rumpf_meets "down" "down" down suche.1 callees.1 (pre_eq _ _) (post_eq _ _)⟩
  · exact ⟨rumpf "pong", lesen.2.1,
      rumpf_meets "ping" "pong" pong suche.2.2 callees.2.1 (pre_eq _ _) (post_eq _ _)⟩
  · exact ⟨rumpf "ping", lesen.2.2,
      rumpf_meets "pong" "ping" ping suche.2.1 callees.2.2 (pre_eq _ _) (post_eq _ _)⟩
  · have hh : c + 3 < 3 := hc
    omega

/-! ## 3. The whole chain -/

/-- **All premises of the measure chain hold together on a recursive and mutually recursive
    unit**, which the rank gate refuses, and premise (b) of the goal theorem follows. -/
theorem nutzer_mass_zeuge :
    rangB unit (rangAuto unit) = false ∧ (∀ rk, ¬ Rang unit rk) ∧
    nullB unit = true ∧ GetragenG unit (fun _ => True) ∧
    MassPflichtU unit (fun _ => True) mass ∧
    Zielsatz.NutzerPflicht (einheitAllg unit program (by cbv)) := by
  have hPtr : SchnittstellenPflichtTeil unit (fun _ => True) :=
    fun P fs hlow c _ => interfaces P fs hlow c
  have hOpen : OffenePflicht unit (fun _ => True) := fun c hc => (hc True.intro).elim
  exact ⟨rang_faellt, kein_rang, by cbv, getragen, pflichten,
    bruecke_nutzer_M lowered getragen mass pflichten hPtr hOpen (by cbv)
      (fun _ _ hc => (hc True.intro).elim)⟩

#print axioms nutzer_mass_zeuge

end Gabbro.Bruecke.MassZeuge
