module

public import Grammatik.Gen.Text.Invers.Funktion
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
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



namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable (z : Spez)

/-- **The elaborated item lists**, described against the accessors of the declaration. -/
structure LInv (gNr : Nat → Nat) (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (whys : List UWhy)
    (regs : List UReg) : Prop where
  glob : ∀ g : z.deklaration.Glob, ∃ gl, globs.find? (fun x => strEq x.name (nGlob (gN z g))) = some gl ∧
    (gl.ty = .bool ↔ z.deklaration.gtyp g = .bool) ∧ gl.var = !z.deklaration.atomar g ∧
    gl.atomic = z.deklaration.atomar g ∧ gl.nutzlast = ((z.deklaration.nutzlast g).map fun h => nGlob (gN z h)) ∧
    (∀ τ, gl.ty ≠ .wert τ) ∧ gl.optNum = none
  tab : ∀ t : z.deklaration.Tab, ∃ tb, tabs.find? (fun x => strEq x.name (nTab (tN z t))) = some tb ∧
    tb.name = nTab (tN z t) ∧ tb.arena = false ∧ tb.count = z.deklaration.count t ∧ tb.opts = [] ∧
    (∀ f : z.deklaration.Feld t, tb.cols.any (fun (g, _) => strEq g (nFeld (show Fin _ from f).val)) = true) ∧
    (∀ f : z.deklaration.Feld t,
      tb.bools.any (fun g => strEq g (nFeld (show Fin _ from f).val)) = decide (z.deklaration.typ t f = .bool))
  tabNr : ∀ t : z.deklaration.Tab, uTabNrAux tabs 0 (nTab (tN z t)) = .ok (tN z t, z.deklaration.count t)
  tabIdx : ∀ t : z.deklaration.Tab, tabs.findIdx? (fun x => strEq x.name (nTab (tN z t))) = some (tN z t)
  tabsOk : ∀ tb ∈ tabs, tb.arena = false ∧ ∃ i, tb.name = nTab i
  wrapsLeer : ∀ tb ∈ tabs, tb.wraps = []
  lockFind : ∀ L : z.deklaration.Lock, ∃ lk, locks.find? (fun x => strEq x.name (nLock (lN z L))) = some lk
  lockGuard : ∀ lk ∈ locks, ∀ t : z.deklaration.Tab, lk.guard.any (strEq · (nTab (tN z t))) = true →
    ∃ L, lk.name = nLock (lN z L) ∧ Sum.inl L ∈ z.deklaration.braucht t
  reg : ∀ r : z.deklaration.Reg, ∃ g, regs.find? (fun g => strEq g.dev "Dev" && strEq g.name (nReg (rN z r))) = some g ∧
    g.dev = "Dev" ∧ g.name = nReg (rN z r) ∧ g.pruefung = none ∧ some g.art = artErg (z.deklaration.rtyp r) ∧
    (g.bool = true ↔ z.deklaration.rtyp r = .bool)
  why : ∀ f : z.deklaration.Fn, z.deklaration.gruende f ≠ 0 → ∃ w,
    whys.findIdx? (fun x => strEq x.name (nGrund (z.deklaration.gruende f))) = some (gNr (z.deklaration.gruende f)) ∧
    whys[gNr (z.deklaration.gruende f)]? = some w ∧ w.cases.length = z.deklaration.gruende f ∧
    ∀ r, r < z.deklaration.gruende f → w.cases.findIdx? (strEq · (nFall r)) = some r

/-- The kinds of the parameters by depth. -/
def artListe (ks : List UParamArt) (d : Nat) : UParamArt := ks.getD d .int

theorem artBei_ok : ∀ (ks : List UParamArt) (d : Nat), d < ks.length → uArtBei ks d = .ok (artListe ks d)
  | [], d, h => by simp only [List.length_nil, Nat.not_lt_zero] at h
  | k :: ks, 0, _ => rfl
  | k :: ks, d + 1, h => by
    simp only [List.length_cons] at h
    simp only [uArtBei, artBei_ok ks d (by omega)]
    rfl

variable {z}

/-- **The context of a function body** satisfies the statement context of its contract. -/
theorem fnCtx_sinv {gNr : Nat → Nat} {tabs : List UTab} {locks : List ULock} {globs : List UGlob}
    {whys : List UWhy} {regs : List UReg} (hL : LInv z gNr tabs locks globs whys regs)
    (hM : ∀ m : z.deklaration.Marke, False) (f : z.deklaration.Fn) (devs : List String) (mitGriff : Bool)
    (ps : List (String × STyp)) (ks : List UParamArt)
    (hps : parListe (optTab z) (z.deklaration.signatur f).params.length 0 (z.deklaration.signatur f).params = .ok ps)
    (hks : (z.deklaration.signatur f).params.mapM artErg = some ks)
    (hdevs : ∀ d ∈ devs, d = "Dev") (hgriff : ∀ r : z.deklaration.Reg, mitGriff = true ∧ "Dev" ∈ devs)
    (als : List (String × (Int × Int))) (name : String) (annahmen : List String) (sums : List USum)
    (zustaende : List UZustand) (hs : sums = []) (zeiger : List String) (zb : Nat)
    (hzb : ∀ g : z.deklaration.Fn, z.deklaration.sig g < zb)
    (hzu : ∀ n, uNamedTransition zustaende n = none) :
    SInv z (vertragVon z.deklaration f)
      { uCtxVon als [] tabs locks globs (kopfVon z gNr devs f ps ks mitGriff) name annahmen whys sums regs zustaende with
        zeiger := zeiger, zeigerBasis := zb }
      (z.deklaration.signatur f).params (Signatur.anfang z.deklaration (z.deklaration.signatur f))
      (artListe ks) where
  var d hd := by
    have hlen := mapM_length artErg _ ks hks
    refine ⟨d, ?_, ?_⟩
    · simp only [uParamNr, uCtxVon, kopfVon]
      exact parNr_ok _ _ 0 (by omega) d (by omega) (by omega)
    · simp only [uCtxVon, kopfVon]
      exact artBei_ok ks d (by omega)
  «meta» d hd j hj := by
    have hlen := mapM_length artErg _ ks hks
    have here : uParamNr
        { uCtxVon als [] tabs locks globs (kopfVon z gNr devs f ps ks mitGriff) name annahmen whys sums regs zustaende with
          zeiger := zeiger, zeigerBasis := zb }
        (nVar ((z.deklaration.signatur f).params.length - 1 - d)) = .ok d := by
      simp only [uParamNr, uCtxVon, kopfVon]
      exact parNr_ok _ _ 0 (by omega) d (by omega) (by omega)
    have : j = d := Except.ok.inj (hj.symm.trans here)
    subst j
    obtain ⟨ty, hty, hm⟩ := ScalarMeta.of_params _ ks hks d hd
    exact ⟨ty, hty, hm⟩
  namen n hn := by
    simp only [uCtxVon, kopfVon, List.mem_map] at hn
    obtain ⟨i, _, rfl⟩ := hn
    exact Or.inl ⟨_, rfl⟩
  lits := rfl
  arrKonst := rfl
  glob := hL.glob
  tab := hL.tab
  wrapsLeer := hL.wrapsLeer
  tabNr := hL.tabNr
  tabIdx := hL.tabIdx
  tabNamen tb hm := (hL.tabsOk tb hm).2
  lockFind := hL.lockFind
  lockGuard := hL.lockGuard
  held L hm := by
    simp only [Signatur.anfang, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨M, hM', he⟩ | ⟨m, _, _⟩
    · cases he
      simp only [uCtxVon, kopfVon]
      apply eindeutig_voll
      exact List.mem_map.2 ⟨L, hM', rfl⟩
    · exact (hM m.1).elim
  muts := rfl
  sums := hs
  resOpt := rfl
  resSum := rfl
  resWhy := rfl
  resTy := rfl
  ergNone h := by
    simp only [vertragVon, Vertrag.vonSig, Deklaration.signatur] at h
    simp only [uCtxVon, kopfVon, Deklaration.signatur, ergBereich, h, reduceCtorEq, decide_false, and_self]
  ergBool h := by
    simp only [vertragVon, Vertrag.vonSig, Deklaration.signatur] at h
    simp only [uCtxVon, kopfVon, Deklaration.signatur, ergBereich, h, decide_true, and_self]
  ergInt lo hi h := by
    simp only [vertragVon, Vertrag.vonSig, Deklaration.signatur] at h
    simp only [uCtxVon, kopfVon, Deklaration.signatur, ergBereich, h, Option.some.injEq, reduceCtorEq,
  decide_false, Option.isSome_some, and_self]
  kanal0 h := by
    simp only [vertragVon, Vertrag.vonSig, Deklaration.signatur] at h
    simp only [uCtxVon, kopfVon, Deklaration.signatur, kanalVon, h, ↓reduceIte]
  griff r := by
    obtain ⟨hm, hd⟩ := hgriff r
    subst hm
    obtain ⟨hf, _⟩ := parListe_ok (optTab z) _ als tabs sums whys [] 0 devs hdevs _ 0 ps ks hps hks
    have hps_none : ∀ p ∈ ps, uGriffTyp devs p.2 = none := by
      intro p hp
      have := (List.filter_eq_self.1 hf) p hp
      simpa using this
    have hdv : (devs.any fun x => strEq x "Dev") = true := List.any_eq_true.2 ⟨"Dev", hd, by decide⟩
    simp only [uCtxVon, kopfVon, mitGriffPs, ite_true]
    rw [griffe_append devs ps _ 0 hps_none]
    simp only [strEq_eq, uGriffe, uGriffTyp, List.any_eq_true, decide_eq_true_eq, exists_eq_right, hd, ↓reduceIte,
  zero_add, List.map_cons, List.map_nil, decide_true, List.find?_cons_of_pos]
  reg := hL.reg
  kanal h := by
    simp only [vertragVon, Vertrag.vonSig] at h ⊢
    obtain ⟨w, h1, h2, _, h4⟩ := hL.why f h
    exact ⟨_, w, by simp only [uCtxVon, kopfVon, kanalVon, h, ↓reduceIte, Deklaration.gruende], h1, h2, h4⟩
  zb := hzb
  transFrei := hzu
  narrowOff := rfl

/-- The `requires`/`ensures` context: the body context with the held resources of `Λ'` (its locks held). -/
theorem SInv.vertragE {V : Vertrag z.deklaration} {ctx : UCtx} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)}
    {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (hΛ : ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ) :
    EInv z ctx Γ Λ' art := by
  have H' : SInv z V ctx Γ Λ' art :=
    { H with held := fun L hL => H.held L (hΛ L hL) }
  exact H'.einv

/-- The `ensures` context with a result: the result is the head of the context, named `result`. -/
theorem EInv.mitErg {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) (τ : Ty) (a : UParamArt) :
    EInvK z ctx (τ :: Γ) Λ (artAuf a art) (some Γ.length) where
  var d hd hk := by
    cases d with
    | zero => simp only [List.length_cons, Nat.add_one_sub_one, Nat.sub_zero, ne_eq, not_true_eq_false] at hk
    | succ d =>
      simp only [List.length_cons] at hd
      have := H.var d (by omega) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
      have e : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
      simp only [List.length_cons, e]
      exact this
  namen := H.namen
  lits := H.lits
  arrKonst := H.arrKonst
  glob := H.glob
  tab := H.tab
  wrapsLeer := H.wrapsLeer
  tabNr := H.tabNr
  waechter := H.waechter

theorem ergOk_mitErg {V : Vertrag z.deklaration} {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)}
    {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (τ : Ty) (hτ : V.erg = some τ) :
    ErgOk ctx (τ :: Γ) (some Γ.length) := by
  intro n hn
  simp only [Option.some.injEq] at hn
  subst hn
  have h' : (τ :: Γ).reverse[Γ.length]? = some τ := by simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil,
  zero_add, Nat.lt_add_one, getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero]
  refine ⟨by simp only [List.length_cons, Nat.lt_add_one], fun lo hi h => ?_, fun h => ?_⟩
  · rw [h'] at h
    simp only [Option.some.injEq] at h
    subst h
    exact (H.ergInt lo hi hτ).1
  · rw [h'] at h
    simp only [Option.some.injEq] at h
    subst h
    exact (H.ergBool hτ).2

/-- The kinds of the `ensures` context: the result (when there is one) first. -/
def artErgAuf (erg : Option Ty) (art : Nat → UParamArt) : Nat → UParamArt :=
  match erg with
  | none => art
  | some _ => artAuf .int art

variable (z) in
/-- The `requires` the elaborator reads. -/
def uOfReq (P : Programm z.deklaration) (f : z.deklaration.Fn) (art : Nat → UParamArt) : Option (List UEns) :=
  if istTru z (P.requires f) then some [] else (uOfB z art none (P.requires f)).map fun u => [u]

variable (z) in
/-- The `ensures` the elaborator reads. -/
def uOfEns (P : Programm z.deklaration) (f : z.deklaration.Fn) (art : Nat → UParamArt) : Option (List UEns) :=
  if istTru z (P.ensures f) then some [] else
    (uOfB z (artErgAuf (z.deklaration.signatur f).erg art) ((z.deklaration.signatur f).erg.map fun _ =>
      (z.deklaration.signatur f).params.length) (P.ensures f)).map fun u => [u]

variable (z) in
/-- **The function the elaborator reads**, computed from the model. -/
def uOfFn (gNr : Nat → Nat) (P : Programm z.deklaration) (f : z.deklaration.Fn) : Option UFn := do
  let S := z.deklaration.signatur f
  let np := S.params.length
  if !(S.erg.all fun t => (artErg t).isSome) then none else
  let ks ← S.params.mapM artErg
  let art : Nat → UParamArt := artListe ks
  let needs ← uOfReq z P f art
  let gives ← uOfEns z P f art
  let (body, r) ← uOfEnd z (vertragVon z.deklaration f) gNr art (P.rumpf f)
  some { name := nFn (fN z f), params := ((List.range' 0 np).map fun i => nVar (np - 1 - i)).zip S.params,
         kinds := ks, res := ergBereich S.erg, resBool := decide (S.erg = some .bool), gruende := S.gruende,
         held := uEindeutig (heldNamen z f), puts := uEindeutig ((tNamen z f).map nTab),
         gputs := uEindeutig ((gNamen z f).map nGlob), gives, needs, body, ret := r }

/-- A printed function, in its pieces. -/
theorem delabFn_teile (P : Programm z.deklaration) (mitGriff : Bool) (f : z.deklaration.Fn) (sig : FnSig)
    (koerper : SAnw) (hd : delabFn z P mitGriff f = .ok (.fnT sig koerper)) :
    ∃ ps res req ens ss ende,
      parListe (optTab z) (z.deklaration.signatur f).params.length 0 (z.deklaration.signatur f).params = .ok ps ∧
      delabRes z f = .ok res ∧ delabReq z P f = .ok req ∧ delabEns z P f = .ok ens ∧
      delabEnd z (vertragVon z.deklaration f) (P.rumpf f) = .ok (ss, ende) ∧
      sig = { art := "impl", name := nFn (fN z f), params := mitGriffPs ps mitGriff, res,
              fehler := if (z.deklaration.signatur f).gruende = 0 then none
                else some (nGrund (z.deklaration.signatur f).gruende),
              klauseln := klauselnVon z P f req ens } ∧
      koerper = .block ss ende := by
  unfold delabFn at hd
  cases hps : parListe (optTab z) (z.deklaration.signatur f).params.length 0 (z.deklaration.signatur f).params with
  | error _ => simp only [bind, Except.bind, hps, reduceCtorEq] at hd
  | ok ps =>
  cases hres : delabRes z f with
  | error _ => simp only [bind, Except.bind, hps, hres, reduceCtorEq] at hd
  | ok res =>
  cases hreq : delabReq z P f with
  | error _ => simp only [bind, Except.bind, hps, hres, hreq, reduceCtorEq] at hd
  | ok req =>
  cases hens : delabEns z P f with
  | error _ => simp only [bind, Except.bind, hps, hres, hreq, hens, reduceCtorEq] at hd
  | ok ens =>
  cases hb : delabEnd z (vertragVon z.deklaration f) (P.rumpf f) with
  | error _ => simp only [bind, Except.bind, hps, hres, hreq, hens, hb, reduceCtorEq] at hd
  | ok q =>
  obtain ⟨ss, ende⟩ := q
  simp only [hps, hres, hreq, hens, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    SItemTief.fnT.injEq] at hd
  exact ⟨ps, res, req, ens, ss, ende, rfl, rfl, rfl, rfl, rfl, hd.1.symm, hd.2.symm⟩

/-- The printed `requires` and its reading. -/
theorem req_ok (P : Programm z.deklaration) (f : z.deklaration.Fn) (art : Nat → UParamArt) (req : List SKlausel)
    (needs : List UEns) (hd : delabReq z P f = .ok req) (hu : uOfReq z P f art = some needs) :
    (req = [] ∧ needs = []) ∨ ∃ e u, req = [.needs e] ∧ needs = [u] ∧ delabE z none (P.requires f) = .ok e ∧
      uOfB z art none (P.requires f) = some u := by
  unfold delabReq at hd
  unfold uOfReq at hu
  by_cases h : istTru z (P.requires f) = true
  · simp only [h, ite_true, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hd hu
    exact Or.inl ⟨hd.symm, hu.symm⟩
  · simp only [h, Bool.false_eq_true, ite_false] at hd hu
    cases he : delabE z none (P.requires f) with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok e =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    cases hb : uOfB z art none (P.requires f) with
    | none => simp only [hb, Option.map_none, reduceCtorEq] at hu
    | some u =>
    simp only [hb, Option.map_some, Option.some.injEq] at hu
    exact Or.inr ⟨e, u, hd.symm, hu.symm, rfl, rfl⟩

/-- The printed `ensures` and its reading. -/
theorem ens_ok (P : Programm z.deklaration) (f : z.deklaration.Fn) (art : Nat → UParamArt) (ens : List SKlausel)
    (gives : List UEns) (hd : delabEns z P f = .ok ens) (hu : uOfEns z P f art = some gives) :
    (ens = [] ∧ gives = []) ∨ ∃ e u, ens = [.gives e] ∧ gives = [u] ∧
      delabE z ((z.deklaration.signatur f).erg.map fun _ => (z.deklaration.signatur f).params.length)
        (P.ensures f) = .ok e ∧
      uOfB z (artErgAuf (z.deklaration.signatur f).erg art) ((z.deklaration.signatur f).erg.map fun _ =>
        (z.deklaration.signatur f).params.length) (P.ensures f) = some u := by
  unfold delabEns at hd
  unfold uOfEns at hu
  by_cases h : istTru z (P.ensures f) = true
  · simp only [h, ite_true, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hd hu
    exact Or.inl ⟨hd.symm, hu.symm⟩
  · simp only [h, Bool.false_eq_true, ite_false] at hd hu
    cases he : delabE z ((z.deklaration.signatur f).erg.map fun _ => (z.deklaration.signatur f).params.length)
        (P.ensures f) with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok e =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    cases hb : uOfB z (artErgAuf (z.deklaration.signatur f).erg art) ((z.deklaration.signatur f).erg.map fun _ =>
        (z.deklaration.signatur f).params.length) (P.ensures f) with
    | none => simp only [hb, Option.map_none, reduceCtorEq] at hu
    | some u =>
    simp only [hb, Option.map_some, Option.some.injEq] at hu
    exact Or.inr ⟨e, u, hd.symm, hu.symm, rfl, rfl⟩

/-- The two clause readers of `elabFn`, named. -/
def gibtF (ctx : UCtx) : SKlausel → Option (Except String UEns)
  | .gives e => some (uSichert ctx e)
  | _ => none

def brauchtF (ctx : UCtx) : SKlausel → Option (Except String UEns)
  | .needs (.call "Held" _) => none
  | .needs e => some (uBool ctx e)
  | _ => none

theorem elabFn_eq (ctx : UCtx) (koepfe : List UFnKopf) (kl : List SKlausel) (ss : List SAnw) (ende : Option SEnde)
    (hsp : ctx.specs = []) :
    elabFn ctx koepfe kl (.block ss ende) =
      match uSeq (kl.filterMap (gibtF ctx)) with
      | .error e => .error e
      | .ok gives =>
        match uSeq (kl.filterMap (brauchtF ctx)) with
        | .error e => .error e
        | .ok needs =>
          match uAnwReihe ctx.tabs koepfe 1000000 ctx ss with
          | .error e => .error e
          | .ok (body, ctxE) =>
            match expandFoldEnd ctxE ende with
            | .error e => .error e
            | .ok (beforeEnd, ctxEnd, ending) =>
              match expandReturnCall ctxEnd koepfe ending with
              | .error e => .error e
              | .ok (beforeCall, ctxReturn, returning) =>
                match uEnde ctxReturn returning with
                | .error e =>
                  if returning.isNone && (match ss.getLast? with | some s => uEndetTief 64 s | none => false) then
                    .ok (gives, needs, body, .keins)
                  else .error e
                | .ok r => .ok (gives, needs, body ++ beforeEnd ++ beforeCall, r) := by
  unfold elabFn elabKlauseln
  simp only [hsp, List.isEmpty_nil, ↓reduceIte]
  have givesReader : (fun clause : SKlausel => match clause with
      | .gives e => some (uSichert ctx e)
      | _ => none) = gibtF ctx := by
    funext clause
    cases clause <;> rfl
  have needsReader : (fun clause : SKlausel => match clause with
      | .needs (.call "Held" _) => none
      | .needs e => some (uBool ctx e)
      | _ => none) = brauchtF ctx := by
    funext clause
    rfl
  erw [givesReader, needsReader]
  cases hg : uSeq (kl.filterMap (gibtF ctx)) <;>
    cases hn : uSeq (kl.filterMap (brauchtF ctx)) <;>
    simp only [hg, hn] <;> rfl

theorem brauchtF_needs (ctx : UCtx) (e : SExpr) (h : kopfOk e = true) : brauchtF ctx (.needs e) = some (uBool ctx e) := by
  cases e with
  | call c args => simp only [kopfOk, Bool.false_eq_true] at h
  | _ => rfl

theorem gibt_klauseln (ctx : UCtx) (P : Programm z.deklaration) (f : z.deklaration.Fn) (req ens : List SKlausel)
    (hreq : ∀ k ∈ req, ∃ e, k = .needs e) :
    (klauselnVon z P f req ens).filterMap (gibtF ctx) = ens.filterMap (gibtF ctx) := by
  unfold klauselnVon heldKlausel effKlausel
  have hr : req.filterMap (gibtF ctx) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro k hk; obtain ⟨e, rfl⟩ := hreq k hk; rfl
  simp only [List.filterMap_append, hr, List.nil_append]
  split <;> split <;> simp only [gibtF, List.filterMap_nil, List.append_nil, List.nil_append, List.filterMap_cons] <;> rfl

theorem braucht_klauseln (ctx : UCtx) (P : Programm z.deklaration) (f : z.deklaration.Fn) (req ens : List SKlausel)
    (hens : ∀ k ∈ ens, ∃ e, k = .gives e) :
    (klauselnVon z P f req ens).filterMap (brauchtF ctx) = req.filterMap (brauchtF ctx) := by
  unfold klauselnVon heldKlausel effKlausel
  have hr : ens.filterMap (brauchtF ctx) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro k hk; obtain ⟨e, rfl⟩ := hens k hk; rfl
  simp only [List.filterMap_append, hr, List.append_nil]
  split <;> split <;> simp only [brauchtF, List.filterMap_nil, List.nil_append, List.append_nil, List.append_right_eq_self, List.filterMap_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.filterMap_cons_none]

/-- The `ensures` context of a function. -/
theorem ens_einv (f : z.deklaration.Fn) {ctx : UCtx} {art : Nat → UParamArt}
    (hM : ∀ m : z.deklaration.Marke, False)
    (H : SInv z (vertragVon z.deklaration f) ctx (z.deklaration.signatur f).params
      (Signatur.anfang z.deklaration (z.deklaration.signatur f)) art) :
    EInvK z ctx (ErgCtx (z.deklaration.signatur f).params (z.deklaration.signatur f).erg)
      (vertragVon z.deklaration f).ende (artErgAuf (z.deklaration.signatur f).erg art)
      ((z.deklaration.signatur f).erg.map fun _ => (z.deklaration.signatur f).params.length) ∧
    ErgOk ctx (ErgCtx (z.deklaration.signatur f).params (z.deklaration.signatur f).erg)
      ((z.deklaration.signatur f).erg.map fun _ => (z.deklaration.signatur f).params.length) := by
  have hΛ : ∀ L, Res.held L ∈ (vertragVon z.deklaration f).ende →
      Res.held L ∈ Signatur.anfang z.deklaration (z.deklaration.signatur f) := by
    intro L hL
    simp only [Vertrag.ende, vertragVon, Vertrag.vonSig, List.mem_append, List.mem_map] at hL
    simp only [Signatur.anfang, List.mem_append, List.mem_map]
    rcases hL with ⟨M, hM', he⟩ | ⟨m, _, _⟩
    · exact Or.inl ⟨M, hM', he⟩
    · exact (hM m.1).elim
  have E := H.vertragE hΛ
  cases herg : (z.deklaration.signatur f).erg with
  | none => exact ⟨E, ergOk_none _ _⟩
  | some τ =>
    exact ⟨E.mitErg τ .int, ergOk_mitErg H τ (by simpa [vertragVon, Vertrag.vonSig] using herg)⟩

end Gabbro.Grammatik.Gen.Text
