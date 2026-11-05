module

public import Grammatik.Gen.Text.Invers.Funktion
public import Grammatik.Gen.Text.Invers.Ganz.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
variable (z : Spez)
variable {z}

/-- **A whole function read back.** -/
theorem fn_ok (gNr : Nat → Nat) (P : Programm z.deklaration) (f : z.deklaration.Fn) {tabs : List UTab}
    {locks : List ULock} {globs : List UGlob} {whys : List UWhy} {regs : List UReg}
    (hL : LInv z gNr tabs locks globs whys regs) (hM : ∀ m : z.deklaration.Marke, False)
    (koepfe : List UFnKopf) (hK : KInv (z := z) gNr koepfe) (hI : KIdx (z := z) koepfe)
    (zeiger : List String) (zb : Nat) (hzb : ∀ g : z.deklaration.Fn, z.deklaration.sig g < zb)
    (devs : List String) (mitGriff : Bool)
    (hdevs : ∀ d ∈ devs, d = "Dev") (hgriff : mitGriff = true → "Dev" ∈ devs)
    (hreg : ∀ r : z.deklaration.Reg, mitGriff = true)
    (als : List (String × (Int × Int))) (annahmen : List String) (sums : List USum) (zustaende : List UZustand)
    (hs : sums = []) (hzu : ∀ n, uNamedTransition zustaende n = none)
    (hsize : sizeOf (P.rumpf f) < 1000000) (sig : FnSig) (koerper : SAnw)
    (hd : delabFn z P mitGriff f = .ok (.fnT sig koerper)) (ufn : UFn) (hu : uOfFn z gNr P f = some ufn) :
    elabUFunktion [] als tabs locks globs koepfe sig koerper annahmen whys sums devs regs zustaende zeiger zb =
      .ok ufn := by
  obtain ⟨ps, res, req, ens, ss, ende, hps, hres, hreq, hens, hb, rfl, rfl⟩ := delabFn_teile P mitGriff f sig koerper hd
  unfold uOfFn at hu
  simp only at hu
  split at hu
  · simp only [reduceCtorEq] at hu
  rename_i hergOk
  cases hks : (z.deklaration.signatur f).params.mapM artErg with
  | none => simp only [hks, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
  | some ks =>
  simp only [hks, Option.bind_eq_bind, Option.bind_some] at hu
  cases hnd : uOfReq z P f (artListe ks) with
  | none => simp only [hnd, Option.bind_none, reduceCtorEq] at hu
  | some needs =>
  cases hgv : uOfEns z P f (artListe ks) with
  | none => simp only [hnd, hgv, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
  | some gives =>
  cases hbr : uOfEnd z (vertragVon z.deklaration f) gNr (artListe ks) (P.rumpf f) with
  | none => simp only [hnd, hgv, hbr, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
  | some q =>
  obtain ⟨body, r⟩ := q
  simp only [hnd, hgv, hbr, Option.bind_some, Option.some.injEq] at hu
  subst hu
  -- the printed clauses
  have hR := req_ok P f _ req needs hreq hnd
  have hE := ens_ok P f _ ens gives hens hgv
  have hreqF : ∀ k ∈ req, ∃ e, k = .needs e := by
    rcases hR with ⟨rfl, _⟩ | ⟨e, _, rfl, _⟩ <;> simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.mem_cons, or_false, forall_eq, SKlausel.needs.injEq, exists_eq']
  have hensF : ∀ k ∈ ens, ∃ e, k = .gives e := by
    rcases hE with ⟨rfl, _⟩ | ⟨e, _, rfl, _⟩ <;> simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.mem_cons, or_false, forall_eq, SKlausel.gives.injEq, exists_eq']
  have hkl : ∀ k ∈ req ++ ens, KlauselOk k ∧ (∀ args, k ≠ .needs (.call "Held" args)) ∧ (∀ es, k ≠ .effs es) := by
    intro k hk
    simp only [List.mem_append] at hk
    rcases hk with hk | hk
    · rcases hR with ⟨rfl, _⟩ | ⟨e, u, rfl, _, he, hu⟩
      · simp only [List.not_mem_nil] at hk
      · simp only [List.mem_singleton] at hk; subst hk
        have hko := kopfOk_delab (artListe ks) none (sizeOf (P.requires f) + 1) (P.requires f) (by omega)
          e he (Or.inr (by simp only [hu, Option.isSome_some]))
        refine And.intro trivial (And.intro (fun args h => ?_) (fun es h => by cases h))
        cases h; simp only [kopfOk, Bool.false_eq_true] at hko
    · rcases hE with ⟨rfl, _⟩ | ⟨e, u, rfl, _, _, _⟩
      · simp only [List.not_mem_nil] at hk
      · simp only [List.mem_singleton] at hk; subst hk
        exact And.intro trivial (And.intro (fun args h => by cases h) (fun es h => by cases h))
  -- the head
  have hV : KopfVor z gNr P f tabs locks globs whys devs mitGriff req ens :=
    { devsOk := hdevs
      griff := hgriff
      erg := fun t ht => by
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hergOk
        simpa [ht] using hergOk
      held := fun l hl => by
        unfold heldNamen at hl
        obtain ⟨L, _, rfl⟩ := List.mem_map.1 hl
        exact hL.lockFind L
      sperren := fun l hl => by
        unfold lNamen at hl
        obtain ⟨L, _, rfl⟩ := List.mem_map.1 (List.mem_eraseDups.1 hl)
        exact hL.lockFind L
      tab := fun i hi => by
        simp only [tNamen, List.mem_map, List.mem_filter] at hi
        obtain ⟨t, _, rfl⟩ := hi
        obtain ⟨tb, hf, hn, _⟩ := hL.tab t
        exact ⟨tb, hf, hn⟩
      glob := fun i hi => by
        simp only [gNamen, List.mem_map, List.mem_filter] at hi
        obtain ⟨g, _, rfl⟩ := hi
        obtain ⟨gl, hf, _⟩ := hL.glob g
        exact List.any_eq_true.2 ⟨gl, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
      tabsOk := hL.tabsOk
      why := fun h => by
        obtain ⟨w, h1, h2, h3, _⟩ := hL.why f h
        exact ⟨w, h1, h2, h3⟩
      klauseln := hkl }
  have hkopf := kopf_ok z gNr P f tabs locks globs whys devs mitGriff [] als sums zeiger zb ps ks res req ens hps hks hres hV
  have H := fnCtx_sinv hL hM f devs mitGriff ps ks hps hks hdevs (fun r => ⟨hreg r, hgriff (hreg r)⟩) als
    (nFn (fN z f)) annahmen sums zustaende hs zeiger zb hzb hzu
  unfold elabUFunktion
  simp only [hkopf, klauselnVon_measure z P f req ens (fun k hk => (hkl k hk).1) als]
  set ctx := { uCtxVon als [] tabs locks globs (kopfVon z gNr devs f ps ks mitGriff) (nFn (fN z f)) annahmen whys
    sums regs zustaende with zeiger := zeiger, zeigerBasis := zb } with hctx
  erw [elabFn_eq ctx _ _ _ _ rfl, gibt_klauseln _ P f req ens hreqF, braucht_klauseln _ P f req ens hensF]
  -- ensures
  have hG : uSeq (ens.filterMap (gibtF ctx)) = .ok gives := by
    rcases hE with ⟨rfl, rfl⟩ | ⟨e, u, rfl, rfl, he, hu⟩
    · rfl
    · obtain ⟨HE, HO⟩ := ens_einv f hM H
      have := sichert_ok _ _ HE HO (P.ensures f) (Nat.lt_succ_self _) e u he hu
      simp only [gibtF, this, Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, uSeq]
  -- requires
  have hN : uSeq (req.filterMap (brauchtF ctx)) = .ok needs := by
    rcases hR with ⟨rfl, rfl⟩ | ⟨e, u, rfl, rfl, he, hu⟩
    · rfl
    · have hko := kopfOk_delab (artListe ks) none (sizeOf (P.requires f) + 1) (P.requires f) (by omega)
        e he (Or.inr (by simp only [hu, Option.isSome_some]))
      have := bool_ok H.einv (P.requires f) e u he hu
      simp only [brauchtF_needs ctx e hko, this, Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil,
  uSeq]
  -- the body
  obtain ⟨cE, hB, hEnde, _⟩ := (rumpf_satz gNr ctx.tabs koepfe hM hK hI (sizeOf (P.rumpf f) + 1)).2.2 (P.rumpf f) ctx
    (artListe ks) 1000000 ss ende body r (by omega) hsize H hb hbr
  have hFold := delabEnd_foldFree (P.rumpf f) (output := (ss, ende)) hb cE
  have hReturn := expandReturnCall_of_ok cE koepfe ende r hEnde
  simp only [hG, hN, hB, hFold, hReturn, hEnde, List.append_nil]
  congr 1
  simp only [kopfVon, kanalVon]
  congr 1
  by_cases hg : (z.deklaration.signatur f).gruende = 0 <;> simp only [hg, ↓reduceIte, Option.map_none, Option.getD_none, Option.map_some, Option.getD_some]

end Gabbro.Grammatik.Gen.Text
