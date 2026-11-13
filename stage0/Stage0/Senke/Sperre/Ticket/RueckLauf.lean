/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/RueckLauf.lean
  Subject:   The scoped returns with REAL releases (lock stage 3), at the return site: the value return
              `ce ++ retScopedC …` (`Ticket/Code.lean`) evaluates the result while every scope is held, saves it in
              the internal slots, checks ensures and the owed invariants on the world while every scope is still
              held (a failure stops with 102 or 103 holding them, as the model's `returnFault`, which `gibt`
              does not change, `returnFault_gibt_foldl`), gives the scopes in their order (`gibTs_run0`, scratch
              from `retTop`), then publishes and returns: `RetZR … scopes` (`retScopedT_ok`). The reason return
              `retWhyScopedC` gives the scopes and runs the reason code: `RetWhyR … scopes` (`retWhyScopedT_ok`).
              The world of both is the model's: `scopes.foldl World.gibt` of the world at the return. The four
              cases of the statement simulation (`retScoped_case`, `retWhyScoped_case` and their end-block forms):
              lowered only under exactly the enclosing scopes `sc`, they return under the pending releases `sc`.
-/
module
public import Stage0.Senke.Sperre.Ticket.Gabe
public import Stage0.Senke.Anweisung.Faelle.RueckgabeScoped
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- A normal return under pending releases keeps its meaning on the released world (`gibt` changes only the
    trace). -/
theorem RetZR_gibt_foldl {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {Hs : List D.Lock} {t : T} {m : Runner.Mem} {σ1 : World D}
    {v : ErgVal D (D.erg f)} (Ls : List D.Lock)
    (h : RetZR L P f σ0 ρ0 fp K rp cfp Hs t m σ1 v) :
    RetZR L P f σ0 ρ0 fp K rp cfp Hs t m (Ls.foldl World.gibt σ1) v := by
  have hf := returnFault_gibt_foldl (P := P) (f := f) σ0 σ1 ρ0 v Ls
  unfold RetZR at h ⊢
  rw [hf]
  by_cases hc : returnFault P f σ0 σ1 ρ0 v ≠ 0
  · rw [if_pos hc] at h ⊢
    exact h
  · rw [if_neg hc] at h ⊢
    obtain ⟨m', s, a, pub, world⟩ := h
    refine ⟨m', s, a, pub, ?_⟩
    obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ1 Ls
    have hws : (owedWorld P f ((Ls.foldl World.gibt σ1).lese (vertragVon D f).ende
        (P.ensures f).orte)).slots =
        (owedWorld P f (σ1.lese (vertragVon D f).ende (P.ensures f).orte)).slots :=
      owedWorld_gibt_slots _ _ hs
    have hwg : (owedWorld P f ((Ls.foldl World.gibt σ1).lese (vertragVon D f).ende
        (P.ensures f).orte)).globs =
        (owedWorld P f (σ1.lese (vertragVon D f).ende (P.ensures f).orte)).globs :=
      owedWorld_gibt_globs _ _ hg
    obtain ⟨ws, wg, wwr⟩ := world
    refine ⟨fun t f k hk => ?_, fun g => ?_, wwr⟩
    · have hv := ws t f k hk
      rwa [hws]
    · have hv := wg g
      rwa [hwg]

/-- **The scoped value return on the released world's values**: from the return site, with the scopes `Hs` held
    (none twice), the code `ce ++ retScopedC …` returns under the pending releases `Hs`. -/
theorem retScopedT_ok0 {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo reserved : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {H Hs : List D.Lock}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f
      (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg)
    {ce : List II} {te : Nat}
    (he : lowErg L e (frei Γ reserved) reserved = some (ce, te))
    (hK : max te (max tens (retTop (functionFrame P f) + 18)) ≤ Ks)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (ce ++ retScopedC L (functionFrame P f) (frei Γ reserved) cens Hs) ρ reserved)
    (hlo : lo ≤ frei Γ reserved) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K)
    (hWa : WeltAt m L σ) (hu : Umf L A C dv m fp Ks K H) (hnd : Hs.Nodup) (hHs : ∀ M, M ∈ Hs → M ∈ H) :
    RetZR L P f σ0 ρ0 fp K rp cfp Hs ⟨pc, fp⟩ m (σ.lese Λ e.orte)
      (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  have hks := hW.ks
  have hrt : retTop (functionFrame P f) = lo + returnWords (D.erg f) (D.gruende f) + 8 := by
    subst hlo0
    rfl
  have result : (functionFrame P f).result = D.erg f := rfl
  have internal : (functionFrame P f).internalResult = lo := hlo0.symm
  have parameterEnd : frei (D.params f) (functionFrame P f).ensReserved = lo := internal
  have lower : 4 ≤ lo := by rw [hlo0]; exact functionFrame_lo4 P f
  have area := resultWords_le_returnWords (D.erg f) (D.gruende f)
  have positive := resultWords_pos (D.erg f)
  have hpS : PreS L m pc fp Ks (frei Γ reserved)
      (ce ++ retScopedC L (functionFrame P f) (frei Γ reserved) cens Hs) ρ reserved :=
    ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hp.frame hks, hp.code,
      codeFar_sub2 hp.far hks, hp.env, trivial, wstab_true _ _⟩
  have small := hpS.small
  have hkS : Kopf L f m fp Ks rp cfp ρ0 P σ0 := by
    refine ⟨hk.r0, hk.r1, hk.env, ?_, hk.entry⟩
    rw [internal]
    omega
  -- the result, while every scope is held
  have hspan := lowErg_span (reserved := reserved) e _ _ _ he
  have hpw := PreS.welt hpS.left (Nat.le_refl Ks) hWa hW.lay hW.lo
  obtain ⟨m1, s1, a1, value1⟩ := lowErg_ok (same := rfl) (reserved := reserved)
    (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) hW.lay e _ ce te he (by omega) m pc ρ hpw
  have world1 := hpw.wstab m m1 hWa (a1.mono (Nat.zero_le _))
  have hp1 := hpS.next a1 (Nat.le_refl _) (by omega)
  have hq : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp Ks (frei Γ reserved)
      (copyWords (resultWords (D.erg f)) lo (frei Γ reserved) ++
        (cens ++ (gibTs L (retTop (functionFrame P f)) Hs ++ publishC (functionFrame P f)))) ρ reserved := by
    simpa only [retScopedC, result, internal, List.append_assoc] using hp1
  -- saved in the internal slots
  obtain ⟨m2, s2, a2exact, value2⟩ := copyResult_run (L := L) hq.frame hpS.small
    (by omega) (by simpa only [resultWords_vertragVon] using
      (show frei Γ reserved + resultWords (vertragVon D f).erg ≤ Ks by omega))
    (Or.inl hlo) (codeAt_left hq.code)
    (by simpa only [copyWords_length] using hq.left.far) value1
  have a2 : Agree fp lo Ks m1 m2 := Agree.widen a2exact (by omega)
  have frame2 := hq.frame.agree a2
  have far2 := codeFar_tail (a := copyWords (resultWords (D.erg f)) lo (frei Γ reserved)) hq.far
  have code2 := (codeAt_right hq.code).agree a2 far2
  simp only [copyWords_length] at code2 far2
  have kept2 := hkS.agree ((a1.mono hlo).trans a2) hpS.frame (by omega)
  have world2 := weltAt_stab hW.lay hW.lo m1 m2 world1 (a2.mono (Nat.zero_le _))
  have contextSize := frei_ergCtx (D.params f) (functionFrame P f).ensReserved (D.erg f)
  rw [parameterEnd] at contextSize
  have ensEnv := envAt_ergEnv kept2.env (by rw [parameterEnd]; exact value2)
  have ensPre : PreS L m2 _ fp Ks (lo + returnWords (D.erg f) (D.gruende f)) cens
      (ergEnv (D.erg f) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ0)
      (functionFrame P f).ensReserved :=
    ⟨by omega, hpS.small, frame2, codeAt_left code2,
      codeFar_left (by rw [← List.length_append]; exact far2), ensEnv, trivial, wstab_true _ _⟩
  -- ensures and owed invariants, while every scope is held
  have postRun := lowPost_ok P f σ0 (σ.lese Λ e.orte) ρ0
    (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)
    hens (by omega) (by simp only [FB]; omega) hW.lay hW.lo m2 _ ensPre world2 kept2.entry
  unfold RetZR
  by_cases hc : returnFault P f σ0 (σ.lese Λ e.orte) ρ0
      (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ≠ 0
  · rw [if_pos hc] at postRun ⊢
    exact Stops.prefix (s1.trans s2) postRun
  · rw [if_neg hc] at postRun ⊢
    obtain ⟨m3, s3, a3⟩ := postRun
    have frame3 := frame2.agree a3
    have far3 := codeFar_tail (a := cens) far2
    have code3 := (codeAt_right code2).agree a3 far3
    have value3 := value2.agree a3 frame2 (by omega) (by omega)
    have kept3 := kept2.agree a3 frame2 (by omega)
    have world3 := weltAt_stab hW.lay hW.lo m2 m3 world2 (a3.mono (Nat.zero_le _))
    -- the releases, innermost first, with scratch above the saved result
    have before : Agree fp lo Ks m m3 := ((a1.mono hlo).trans a2).trans (a3.mono (by omega))
    have hy3 : TicketSync m3 L fp Ks H := hu.sync.agree before (by have := hu.hiK; omega)
    have hK' : KetteOK L fp (retTop (functionFrame P f)) :=
      ⟨by have := hW.lo; have := hW.ord; omega, hW.lay.2.2, hu.sync.lay, hu.sync.sye, hu.sync.dis⟩
    obtain ⟨m4, s4, a4, hfin⟩ := gibTs_run0 hK' (by omega)
      (codeFar_sub2 (Ks := retTop (functionFrame P f) + 18) far3 (by omega)) hnd
      (frameOK_sub frame3 (by omega)) (fun Lk k hk => hy3.wr Lk k hk) code3
      (fun Lk h => hy3.mine (hHs Lk h))
    have far4 := codeFar_tail (a := gibTs L (retTop (functionFrame P f)) Hs) far3
    have code4 := a4.codeAt hK' (codeAt_right code3) far4
    have frame4 : FrameOK m4 fp Ks :=
      ⟨frame3.lt, fun i hi => by rw [a4.rd]; exact frame3.rd i hi,
        fun i hi => by rw [a4.wr]; exact frame3.wr i hi⟩
    have value4 := a4.resultAt hK' value3 (by omega)
    have head0 : m4.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp := by
      rw [a4.rd_low hK' (i := 0) (by omega)]
      exact kept3.r0
    have head1 : m4.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp := by
      rw [a4.rd_low hK' (i := 1) (by omega)]
      exact kept3.r1
    have topPublish : retTop (functionFrame P f) ≤ Ks := by omega
    -- the publication of the saved result and `ret`, reading only the frame
    obtain ⟨m5, published, changed, returned, mirror, normal⟩ :=
      publishResult_run (functionFrame P f) frame4 hpS.small topPublish code4 far4
        (by rw [internal]; exact value4) head0 head1
    have world4 := a4.weltAt hK' world3 hW.lay (by have := hW.lo; omega)
    have world5 := weltAt_stab hW.lay hW.lo m4 m5 world4 (changed.mono (Nat.zero_le _))
    have aPre : AgreeW L fp 2 K m m3 := (agreeW_of (Agree.widen before hks)).mono (by omega)
    have aPost : AgreeW L fp 2 K m4 m5 := agreeW_of (Agree.widen changed hks)
    refine ⟨m5, s1.trans (s2.trans (s3.trans (s4.trans published))),
      AgreeWR.ofKette hu.sync hHs hK' hW.ord hu.hiK (by omega) (by omega) aPre a4 aPost hfin,
      ⟨returned, mirror, normal⟩, ?_⟩
    exact owedWorld_at P f _ m5 world5

/-- **The scoped value return** (`Stmt.retScoped e R` with `R.scopes = Hs`), on the model's world: the released
    `Hs.foldl World.gibt` of the world after the result's reads. -/
theorem retScopedT_ok {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo reserved : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {H Hs : List D.Lock}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f
      (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg)
    {ce : List II} {te : Nat}
    (he : lowErg L e (frei Γ reserved) reserved = some (ce, te))
    (hK : max te (max tens (retTop (functionFrame P f) + 18)) ≤ Ks)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (ce ++ retScopedC L (functionFrame P f) (frei Γ reserved) cens Hs) ρ reserved)
    (hlo : lo ≤ frei Γ reserved) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K)
    (hWa : WeltAt m L σ) (hu : Umf L A C dv m fp Ks K H) (hnd : Hs.Nodup) (hHs : ∀ M, M ∈ Hs → M ∈ H) :
    RetZR L P f σ0 ρ0 fp K rp cfp Hs ⟨pc, fp⟩ m (Hs.foldl World.gibt (σ.lese Λ e.orte))
      (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) :=
  RetZR_gibt_foldl Hs (retScopedT_ok0 hlo0 hens e he hK m pc σ ρ hp hlo hk hW hWa hu hnd hHs)

/-- **The scoped reason return** (`Stmt.retWhyScoped r R` with `R.scopes = Hs`): the scopes given, then the reason
    code; on the model's world `Hs.foldl World.gibt σ`. -/
theorem retWhyScopedT_ok {P : Programm D} {σ0 : World D} {reserved : Nat} {f : D.Fn} {fp : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {ρ0 : Env D (D.params f)} {Γ : Ctx} {m : Runner.Mem} {pc : Runner.W}
    {σ : World D} {ρ : Env D Γ} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {H Hs : List D.Lock}
    (r : Fin (D.gruende f)) (hlo0 : lo = (functionFrame P f).internalResult)
    (hK : retTop (functionFrame P f) + 18 ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved) (retWhyScopedC L (functionFrame P f) r.val Hs) ρ reserved)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ)
    (hu : Umf L A C dv m fp Ks K H) (hnd : Hs.Nodup) (hHs : ∀ M, M ∈ Hs → M ∈ H) :
    RetWhyR L f fp K rp cfp Hs ⟨pc, fp⟩ m (Hs.foldl World.gibt σ) r := by
  have hks := hW.ks
  have hrt : retTop (functionFrame P f) = lo + returnWords (D.erg f) (D.gruende f) + 8 := by
    subst hlo0
    rfl
  have lower : 4 ≤ lo := by rw [hlo0]; exact functionFrame_lo4 P f
  have small := hp.small
  have hK' : KetteOK L fp (retTop (functionFrame P f)) :=
    ⟨by have := hW.top; have := hW.ord; omega, hW.lay.2.2, hu.sync.lay, hu.sync.sye, hu.sync.dis⟩
  have hc0 : CodeAt m pc (gibTs L (retTop (functionFrame P f)) Hs ++ retWhyC (functionFrame P f) r.val) :=
    hp.code
  have hf0 : CodeFar pc (gibTs L (retTop (functionFrame P f)) Hs ++ retWhyC (functionFrame P f) r.val).length
      fp K := hp.far
  obtain ⟨m1, s1, a1, hfin⟩ := gibTs_run0 hK' (by omega)
    (codeFar_sub2 (Ks := retTop (functionFrame P f) + 18) hf0 (by omega)) hnd
    (frameOK_sub hp.frame (by omega)) (fun Lk k hk => hu.sync.wr Lk k hk) hc0
    (fun Lk h => hu.sync.mine (hHs Lk h))
  have far1 := codeFar_tail (a := gibTs L (retTop (functionFrame P f)) Hs) hf0
  have code1 := a1.codeAt hK' (codeAt_right hc0) far1
  have frame1 : FrameOK m1 fp K :=
    ⟨hp.frame.lt, fun i hi => by rw [a1.rd]; exact hp.frame.rd i hi,
      fun i hi => by rw [a1.wr]; exact hp.frame.wr i hi⟩
  have pre1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * (gibTs L (retTop (functionFrame P f)) Hs).length)) fp K
      (frei ([] : Ctx) 0) (retWhyC (functionFrame P f) r.val) (Env.nil : Env D []) 0 :=
    ⟨Nat.le_refl _, hp.small, frame1, code1, far1, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have hk1 : Kopf L f m1 fp K rp cfp ρ0 P σ0 := a1.kopf hk hK' (by rw [← hlo0]; omega)
  have hWa1 : WeltAt m1 L (Hs.foldl World.gibt σ) :=
    WeltAt_gibt_foldl (a1.weltAt hK' hWa hW.lay (by have := hW.lo; omega))
  obtain ⟨m', s2, a2, value, mirror, flag, world⟩ :=
    retWhy_ok (σ := Hs.foldl World.gibt σ) r hlo0 (by omega) pre1 hk1 hW hWa1
  exact ⟨m', s1.trans s2, AgreeWR.ofKette hu.sync hHs hK' hW.ord hu.hiK (by omega) (by omega)
    (AgreeW.refl L fp 2 K m) a1 a2 hfin, value, mirror, flag, world⟩

section Faelle

variable {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
  {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
  {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
  {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
  {reserved : Nat} {pr : List Nat} {ex : Int × Int} {H sc : List D.Lock}
  {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- **The case of `Stmt.retScoped e Rr`** of the statement simulation: lowered only when its cleanup names exactly the
    enclosing scopes `sc` (none twice), it returns under the pending releases `sc`. -/
theorem retScoped_case (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {e : ErgExpr D Γ Λ (D.erg f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} (hsc : ∀ M ∈ sc, M ∈ H) :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc
      (show Stmt D (vertragVon D f) l Γ Λ Λ from .retScoped e Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 hu hk hWa hpr
  simp only [lowS, lowRetScoped] at h
  split at h
  · next hc =>
    obtain ⟨hsc0, hnd⟩ := hc
    subst hsc0
    simp only [← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hcode⟩ := h
    simp only [Prod.mk.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    simp only [execStmt, Sim]
    change max te (max tens (retTop (functionFrame P f) + 18)) + cap ≤ Ks at hK
    exact retScopedT_ok (reserved := reserved) hlo0 hens e he (by omega) m pc σ ρ hp hlo2 hk hW hWa hu hnd hsc
  · cases h

/-- **The case of `Stmt.retWhyScoped r Rr`**: as `retScoped_case`, for the reason return. -/
theorem retWhyScoped_case (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {r : Fin (D.gruende f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} (hsc : ∀ M ∈ sc, M ∈ H) :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc
      (show Stmt D (vertragVon D f) l Γ Λ Λ from .retWhyScoped r Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 hu hk hWa hpr
  simp only [lowS, lowRetWhyScoped] at h
  split at h
  · next hc =>
    obtain ⟨hsc0, hnd⟩ := hc
    subst hsc0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    change max (frei Γ reserved) (retTop (functionFrame P f) + 18) + cap ≤ Ks at hK
    exact retWhyScopedT_ok r hlo0 (by omega) hp hk hW hWa hu hnd hsc
  · cases h

/-- **The end-block case of `retScoped e Rr`**: as `retScoped_case`, for `Ret`. -/
theorem endRetScoped_case (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31)
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {e : ErgExpr D Γ Λ (D.erg f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} (hsc : ∀ M ∈ sc, M ∈ H) :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc
      (show Endblock D (vertragVon D f) l Γ Λ from .retScoped e Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, lowRetScoped] at h
  split at h
  · next hc =>
    obtain ⟨hsc0, hnd⟩ := hc
    subst hsc0
    simp only [← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hcode⟩ := h
    simp only [Prod.mk.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    simp only [execEnd, Ret]
    change max te (max tens (retTop (functionFrame P f) + 18)) + cap ≤ Ks at hK
    exact retScopedT_ok (reserved := reserved) hlo0 hens e he (by omega) m pc σ ρ hp hlo hk hW hWa hu hnd hsc
  · cases h

/-- **The end-block case of `retWhyScoped r Rr`**: as `retWhyScoped_case`, for `Ret`. -/
theorem endRetWhyScoped_case (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31)
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {r : Fin (D.gruende f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} (hsc : ∀ M ∈ sc, M ∈ H) :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc
      (show Endblock D (vertragVon D f) l Γ Λ from .retWhyScoped r Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, lowRetWhyScoped] at h
  split at h
  · next hc =>
    obtain ⟨hsc0, hnd⟩ := hc
    subst hsc0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execEnd, Ret]
    change max (frei Γ reserved) (retTop (functionFrame P f) + 18) + cap ≤ Ks at hK
    exact retWhyScopedT_ok r hlo0 (by omega) hp hk hW hWa hu hnd hsc
  · cases h

end Faelle

end Gabbro.Stage0.Senke
