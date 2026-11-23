module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
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
# The premises of `nutzerA_aus_ziele` hold jointly

For the unit of one function `main` without parameters, result or body: every function's duty
`ZielF` is proved directly over the program the lowering builds (`programm_von`, then the
weakest-precondition rule of its return), the unit has no foreign body, and Stage 0's decision of
the data parts accepts its judged unit for every lowered program, axiom family, memory, entry and
arguments. The run facts are facts of a Stage 0 run and are not instantiated here.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

/-- `impl fn main() { }`. -/
def mainLeer : UFn :=
  { name := "main", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

def einheitLeer : UProg :=
  { tabs := [], locks := [], fns := [mainLeer], axs := [], guests := [], annahmen := [],
    whys := [], sums := [], gestartet := [], roots := [], hands := [], globs := [], regs := [],
    invs := [], zustaende := [], regiert := [], ptrs := [], ptrKeys := [], exportGate := Except.ok (),
    records := [], checks := [], marken := [], spaces := ["normal"], eigner := [], markOrders := [] }

/-- The lowered body of `main` is a return, its postcondition holds everywhere. -/
theorem einheitLeer_senkung (f : Fin einheitLeer.fns.length)
    (w : ∃ v, lowerFnAt einheitLeer f = .ok v) :
    (∃ e h, (lowerAtPair einheitLeer f w).2.1 = Endblock.ret e h) ∧
      ∀ σ₀ σ E, wahr? (eval σ₀ (lowerAtPair einheitLeer f w).1 σ E) = true := by
  match f with
  | ⟨0, _⟩ => exact ⟨by with_unfolding_all exact ⟨_, _, rfl⟩, fun _ _ _ => by with_unfolding_all rfl⟩

theorem einheitLeer_ziel : ∀ f, ZielF einheitLeer (fun _ => []) f := by
  intro f P fs hlow Q sp main args roots gestartet checks passes
  obtain ⟨v, hv, he, hb, hr⟩ := programm_von hlow f
  have hvw : lowerAtPair einheitLeer f ⟨v, hv⟩ = v := lowerAtPair_von f _ hv
  obtain ⟨⟨e, h, hret⟩, hens⟩ := einheitLeer_senkung f ⟨v, hv⟩
  rw [hvw] at hret hens
  have hinv : ∀ σ', InvAmRueck P f σ' := fun σ' i hi => by
    have : i ∈ List.finRange 0 := hi
    cases this
  refine ⟨?_, ?_, ?_⟩ <;>
    intro O' _ _ _ U _ A _ R _ _ σ ρ _ <;>
    show wpEA _ _ _ _ _ _ (P.rumpf f) _ σ ρ <;>
    rw [hb, hret, wpEA_ret]
  · exact ⟨fun σ' w hz => by
      cases hz
      refine ⟨?_, hinv _⟩
      unfold EnsAmRueck
      change wahr? (eval σ (P.ensures f) _ _) = true
      rw [he]
      exact hens _ _ _,
      fun σ' r hz => by cases hz⟩
  · intro g hz; cases hz
  · intro e hz; cases hz

/-- **The premises of `nutzerA_aus_ziele` hold jointly**, and not vacuously: the lowering accepts
    the unit, every function's duty holds, and Stage 0's decision accepts its judged unit. -/
theorem nutzerA_aus_ziele_erfuellbar :
    ∃ u : UProg, (∀ f, ZielF u (fun _ => []) f) ∧ u.fns ≠ [] ∧ u.axs = [] ∧
      (∃ (P : Programm (declOf u)) (fs : List (declOf u).Fn), lowerAllg u = .ok (P, fs)) ∧
      ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn), lowerAllg u = .ok (P, fs) →
        ∀ (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
          (args : Env (declOf u) ((declOf u).params main)),
          entschiedenB (Gabbro.Stage0.OldSource.einheitDer u (restored (fun _ => []) u P) Q sp main args [] [] [])
            (List.finRange u.locks.length) = true := by
  refine ⟨einheitLeer, einheitLeer_ziel, by simp [einheitLeer], rfl, ?_, ?_⟩
  · have hk : (match lowerAllg einheitLeer with | .ok _ => true | .error _ => false) = true := by
      with_unfolding_all rfl
    cases h : lowerAllg einheitLeer with
    | ok p => exact ⟨p.1, p.2, rfl⟩
    | error e => rw [h] at hk; cases hk
  intro P fs hlow Q sp main args
  obtain ⟨v, hv, he, hb, hr⟩ := programm_von hlow main
  have hreq : P.requires main = .tru := by
    rw [hr]
    match main with
    | ⟨0, _⟩ => rfl
  simp only [entschiedenB, Bool.and_eq_true]
  refine ⟨by with_unfolding_all rfl, ?_⟩
  simp only [List.all_eq_true]
  intro a ha'
  simp only [Gabbro.Stage0.OldSource.einheitDer, Gabbro.Stage0.OldSource.einheitVon, List.append_nil,
    List.mem_singleton] at ha'
  subst ha'
  show (checkStartRequires P sp ⟨main, args⟩).toOption.isSome = true
  have hk : (Invarianten.Frag.translate (P.requires main) args).toOption.isSome = true := by
    generalize P.requires main = r at hreq ⊢
    subst hreq
    with_unfolding_all rfl
  cases hc : Invarianten.Frag.translate (P.requires main) args with
  | error e => rw [hc] at hk; cases hk
  | ok enc =>
    refine (checkStartRequires_iff (start := ⟨main, args⟩) hc).mpr ?_
    unfold ReqAmEintritt
    rw [hreq]
    rfl

#print axioms einheitLeer_ziel
#print axioms nutzerA_aus_ziele_erfuellbar

end Gabbro.Bruecke
