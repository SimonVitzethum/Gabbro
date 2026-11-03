module

public import Grammatik.Logik.Ruf.Schnittstellen.Vertrag

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## Conjunct normalisation for pointer-interface contracts (C06, O43)

  A contract side is a conjunction spread over a predicate list
  (`needs`/`gives` at the export) or nested `.and` in one `Expr`.
  `konjunkte` flattens one `Expr .. .bool` to its conjunct list;
  `Einschluss` is the syntactic inclusion of two such lists in one
  context. The per-conjunct reformulation of `PtrZielVerfeinert` below
  is exactly what the export's decidable inclusion discharges, one
  admitted pair at a time. The cross-context syntactic discharge
  (export Bool implies this reformulation through lowering) is the
  next step, not claimed here. -/

/-- Conjunct normal form: right-nested `.and` flattened to a list. -/
def konjunkte {Γ : Ctx} {Λ : List (Res D)} : Expr D Γ Λ .bool → List (Expr D Γ Λ .bool)
  | .and a b => konjunkte a ++ konjunkte b
  | e => [e]

/-- A holds iff every conjunct holds, at the same worlds and environment. -/
theorem konjunkte_holds {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool)
    (s0 s : World D) (ρ : Env D Γ) :
    wahr? (eval s0 e s ρ) = true ↔
      ∀ c ∈ konjunkte e, wahr? (eval s0 c s ρ) = true :=
  match e with
  | .and a b => by
    have iha := konjunkte_holds a s0 s ρ
    have ihb := konjunkte_holds b s0 s ρ
    have hand : wahr? (eval s0 (Expr.and a b) s ρ) =
        (wahr? (eval s0 a s ρ) && wahr? (eval s0 b s ρ)) := rfl
    simp only [konjunkte, List.mem_append, hand, Bool.and_eq_true]
    refine ⟨fun ⟨ha, hb⟩ c hc => ?_, fun h => ⟨?_, ?_⟩⟩
    · rcases hc with hc | hc
      · exact (iha.mp ha) c hc
      · exact (ihb.mp hb) c hc
    · exact iha.mpr (fun c hc => h c (.inl hc))
    · exact ihb.mpr (fun c hc => h c (.inr hc))
  | .tru | .fls | .var .. | .glob .. | .slot .. | .thru .. | .oldG .. | .oldS ..
  | .lt .. | .le .. | .eq .. | .fllt .. | .flle .. | .or .. | .not .. | .istSome ..
  | .forallSlots .. | .existsSlots .. | .reaches .. | .refEq .. | .slotRef ..
  | .arrGet .. | .strEq .. | .strLt .. | .wenn .. | .intBuiltin1 .. | .intBuiltin2 ..
  | .prodGet .. => by simp [konjunkte]

/-- Syntactic inclusion of normalised conjunct lists in one context:
    every goal conjunct occurs among the assumptions. -/
def Einschluss {Γ : Ctx} {Λ : List (Res D)}
    (sup sub : List (Expr D Γ Λ .bool)) : Prop :=
  ∀ c ∈ sub, c ∈ sup

/-- Inclusion discharges each goal conjunct from the assumed ones. -/
theorem einschluss_holds {Γ : Ctx} {Λ : List (Res D)}
    {sup sub : List (Expr D Γ Λ .bool)} (h : Einschluss sup sub)
    {s0 s : World D} {ρ : Env D Γ}
    (hsup : ∀ c ∈ sup, wahr? (eval s0 c s ρ) = true)
    (c : Expr D Γ Λ .bool) (hc : c ∈ sub) :
    wahr? (eval s0 c s ρ) = true :=
  hsup c (h c hc)

/-- Universal refinement, one conjunct at a time: the interface pre
    (as a conjunction) implies the selected target's requires, and the
    target's normal ensures (under the interface pre) exposes every
    interface-post conjunct. Concrete contracts stay intact; no target
    is replaced by an interface stub. -/
theorem ptrZielVerfeinert_konjunkt (P : Programm D) (f : D.Fn) (n : Nat)
    (hf : D.passt f n = true) :
    PtrZielVerfeinert P f n hf ↔
      ((∀ (s0 : World D) (ρ : Env D (D.sigNr n).params),
          (∀ c ∈ konjunkte ((P.ptrVertrag n).pre), wahr? (eval s0 c s0 ρ) = true) →
          ReqAmEintritt P f s0 (umsig hf ρ)) ∧
       (∀ (s0 s1 : World D) (ρ : Env D (D.sigNr n).params) (v : ErgVal D (D.erg f)),
          (∀ c ∈ konjunkte ((P.ptrVertrag n).pre), wahr? (eval s0 c s0 ρ) = true) →
          EnsAmRueck P f s0 s1 (umsig hf ρ) v →
          ∀ d ∈ konjunkte ((P.ptrVertrag n).post),
            wahr? (eval s0 d s1 (ergEnv (D.sigNr n).erg (ptrResult hf v) ρ)) = true)) := by
  unfold PtrZielVerfeinert CallContract.preHolds CallContract.postHolds
  constructor
  · rintro ⟨hpre, hpost⟩
    refine ⟨fun s0 ρ hc => hpre s0 ρ ((konjunkte_holds _ s0 s0 ρ).mpr hc),
      fun s0 s1 ρ v hc hv => ?_⟩
    have hp := hpost s0 s1 ρ v ((konjunkte_holds _ s0 s0 ρ).mpr hc) hv
    exact fun d hd => (konjunkte_holds _ s0 s1 _).mp hp d hd
  · rintro ⟨hpre, hpost⟩
    refine ⟨fun s0 ρ hp => hpre s0 ρ ((konjunkte_holds _ s0 s0 ρ).mp hp),
      fun s0 s1 ρ v hp hv => ?_⟩
    exact (konjunkte_holds _ s0 s1 _).mpr
      (hpost s0 s1 ρ v ((konjunkte_holds _ s0 s0 ρ).mp hp) hv)

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.konjunkte_holds
#print axioms Gabbro.Grammatik.einschluss_holds
#print axioms Gabbro.Grammatik.ptrZielVerfeinert_konjunkt
