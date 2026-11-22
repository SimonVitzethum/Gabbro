module

public import Stage0.Senke.Bild.Ruf.Idle.Foreign
public import Stage0.Senke.Bild.Ruf.Idle.Counters
public import Stage0.Senke.Bild.Ruf.Idle.ByteStores

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

attribute [local reducible] Ty.mapNumbers Ty.mapCases Ty.mapFields Deklaration.mitRuhe

private theorem lowS_resources (passes : Nat) (A : D.Fn → Nat) (L : Lay D)
    (frame : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (same : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) (reserved : Nat) (sc : List D.Lock) :
    lowS passes A L frame ens pr ex (s.nachΛ same) reserved sc =
      lowS passes A L frame ens pr ex s reserved sc := by
  cases same
  rfl

private theorem lowB_resources (passes : Nat) (A : D.Fn → Nat) (L : Lay D)
    (frame : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (same : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') (reserved : Nat) (sc : List D.Lock) :
    lowB passes A L frame ens pr ex (b.vorΛ same) reserved sc =
      lowB passes A L frame ens pr ex b reserved sc := by
  cases same
  rfl

private theorem lowEnd_resources (passes : Nat) (A : D.Fn → Nat) (L : Lay D)
    (frame : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (same : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) (reserved : Nat) (sc : List D.Lock) :
    lowEnd passes A L frame ens pr ex (e.umΛ same) reserved sc =
      lowEnd passes A L frame ens pr ex e reserved sc := by
  cases same
  rfl

private theorem slotStoreC_withIdle (L : Lay D) (table : D.Tab) (field : D.Feld table)
    (dest : Nat) (value index : List II × Nat) :
    slotStoreC L.withIdle table field dest value index = slotStoreC L table field dest value index := by
  have width : valueWords (D.mitRuhe.typ table field) = valueWords (D.typ table field) :=
    valueWords_mapNumbers (· + 1) id _
  simp only [slotStoreC, width, cellAddressC_withIdle]

private theorem globalStoreC_withIdle (L : Lay D) (global : D.Glob) (dest : Nat) (value : List II × Nat) :
    globalStoreC L.withIdle global dest value = globalStoreC L global dest value := by
  simp only [globalStoreC, Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

private theorem signatur_some (fn : D.Fn) : D.mitRuhe.signatur (some fn) = sigR (D.signatur fn) := rfl

private theorem locksCodeT_withIdle (L : Lay D) (address scratch : Nat) (body : List II) (next leave : Int) :
    locksCodeT L.withIdle address scratch body next leave = locksCodeT L address scratch body next leave := rfl

private theorem lockAddress_withIdle (L : Lay D) (lock : D.Lock) : L.withIdle.lk lock = L.lk lock := rfl

/-- The same body lowering is valid after extending the model with
    idle thread slots. Every branch retains the installed code and scratch bound. -/
theorem lowEnd_withIdle (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (frame : FrameLayout)
    (ens : List II × Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    ∀ (pr : List Nat) (ex : Int × Int) (reserved : Nat) (sc : List D.Lock),
      lowEnd passes (fun (f : D.mitRuhe.Fn) => f.elim 0 A) L.withIdle frame.withIdle ens pr ex (ruEnd e) reserved sc =
        lowEnd passes A L frame ens pr ex e reserved sc := by
  let shifted : D.mitRuhe.Fn → Nat := fun f => f.elim 0 A
  apply Endblock.rec
    (motive_1 := fun _ _ _ _ s => ∀ pr ex reserved sc,
      lowS passes shifted L.withIdle frame.withIdle ens pr ex (ruS s) reserved sc =
        lowS passes A L frame ens pr ex s reserved sc)
    (motive_2 := fun _ _ _ _ b => ∀ pr ex reserved sc,
      lowB passes shifted L.withIdle frame.withIdle ens pr ex (ruB b) reserved sc =
        lowB passes A L frame ens pr ex b reserved sc)
    (motive_3 := fun _ _ _ body => ∀ pr ex reserved sc,
      lowEnd passes shifted L.withIdle frame.withIdle ens pr ex (ruEnd body) reserved sc =
        lowEnd passes A L frame ens pr ex body reserved sc)
    (motive_4 := fun _ _ _ _ _ arms =>
      (∀ pr ex tag reserved sc,
        lowTags passes shifted L.withIdle frame.withIdle ens pr ex (ruArms arms) tag reserved sc =
          lowTags passes A L frame ens pr ex arms tag reserved sc) ∧
      (∀ pr ex span tag reserved sc,
        lowSumTags passes shifted L.withIdle frame.withIdle ens pr ex (ruArms arms) span tag reserved sc =
          lowSumTags passes A L frame ens pr ex arms span tag reserved sc))
    (motive_5 := fun _ _ _ _ _ arms => ∀ pr ex tag reserved sc,
      lowGrund passes shifted L.withIdle frame.withIdle ens pr ex (ruGArms arms) tag reserved sc =
        lowGrund passes A L frame ens pr ex arms tag reserved sc)
  all_goals
    intros
    try (apply And.intro <;> intros)
    try simp only [ruS, ruB, ruEnd, ruArms, ruGArms, lowS, lowB, lowEnd, lowTags, lowSumTags, lowGrund,
      lowS_resources, lowB_resources, lowEnd_resources, frei_withIdle, vslot_varR,
      lowE_withIdle, lowA_withIdle, lowErg_withIdle, lowInd_withIdle, lowIndElse_withIdle,
      retC_withIdle, retTop_withIdle, retWhyC_withIdle, retScopedC_withIdle, retWhyScopedC_withIdle,
      FrameLayout.internalResult_withIdle, callC_withIdle, callTop_withIdle, elseTop_withIdle,
      receiveC_withIdle, receiveTop_withIdle, elseC_withIdle, elseTopInd_withIdle,
      slotStoreC_withIdle, globalStoreC_withIdle, plainForeignC_withIdle, fallibleForeignC_withIdle,
      torC_withIdle, torC0_withIdle, counterDepthB_ru, aggregateFits_tyR, valueWords_mapNumbers, *]
    try simp only
      [lowE_withIdle, lowA_withIdle, lowErg_withIdle, lowInd_withIdle, lowIndElse_withIdle,
      lowRetScoped, lowRetWhyScoped, retScopedC_withIdle, retWhyScopedC_withIdle, retTop_withIdle,
      signatur_some, sigNrM, receiveC_withIdle, receiveTop_withIdle, elseC_withIdle,
      elseTop_withIdle, elseTopInd_withIdle, callC_withIdle, slotC_withIdle,
      slotA_withIdle, putBytesL_withIdle, putBytesWideL_withIdle,
      locksCodeT_withIdle, lockAddress_withIdle, sumFits_mapNumbers, Ty.mapCases_length, vertragR,
      lowS_resources, lowB_resources, lowEnd_resources, frei_withIdle, *]
    try simp only [shifted, callC_withIdle]
    try rfl

end Gabbro.Stage0.Senke
