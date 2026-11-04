/-
  Scoped returns lower like ordinary returns; the scope release is ghost.

  `Stmt/Endblock.retScoped` emits exactly the code of `ret` (`lowErg` plus the
  shared `retC` epilogue), `retWhyScoped` exactly the code of `retWhy`
  (`retWhyC`): the release of `R.scopes` is ghost at Stage-0 level, as it is at
  Code level (`lowerRet`/`lowerWhy` with `Rep.gibt_foldl`). `execStmt/execEnd`
  releases the scopes innermost first (`List.foldl World.gibt`: the trace gets
  one `gibt` per scope with the last release on top), and the simulation keeps
  the released world through the fold: `WeltAt` and `returnFault` see only
  slots and globals (`World.gibt_foldl_speicher`, `eval_spurfrei`), so no
  runtime release or invariant check is emitted -- the same release behaviour
  as the `locks` exit, which performs `gibt` without a check. Emitting `gibC`
  per scope would change lock words and break the `AgreeW` of `RetZ`/`RetWhy`;
  the static scope duties stay with the checker and `ScopesOkProg`. The emission
  helpers live in `Faelle/Hilfen.lean`; the `lowS`/`lowEnd` equations come from
  `Stage0.Senke.Anweisung`.
-/
module
public import Stage0.Senke.Anweisung
public import Stage0.Senke.Anweisung.Faelle.Kontext
public import Stage0.Senke.Anweisung.Faelle.Hilfen
public import Stage0.Senke.Rueckkehr.Normal
public import Stage0.Senke.Rueckkehr.Reason
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Return
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Ruf.RufLogik
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D}

section Freigabe

variable {P : Programm D} {f : D.Fn}

/-- Releasing scopes keeps every world cell: the fold is trace-only. -/
theorem WeltAt_gibt_foldl {m : Runner.Mem} {σ : World D} {Ls : List D.Lock}
    (h : WeltAt m L σ) : WeltAt m L (Ls.foldl World.gibt σ) := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ Ls
  obtain ⟨hslots, hglobs, hwr⟩ := h
  refine ⟨fun t f k hk => ?_, fun g => ?_, hwr⟩
  · have hv := hslots t f k hk
    rwa [hs]
  · have hv := hglobs g
    rwa [hg]

/-- The owed-invariant read phase sees the same slots after a release fold. -/
theorem owedWorld_gibt_slots (postA postB : World D)
    (hps : postA.slots = postB.slots) :
    (owedWorld P f postA).slots = (owedWorld P f postB).slots := by
  simp only [owedWorld]
  rw [foldl_lese_slots, foldl_lese_slots]
  exact hps

/-- The owed-invariant read phase sees the same globals after a release fold. -/
theorem owedWorld_gibt_globs (postA postB : World D)
    (hpg : postA.globs = postB.globs) :
    (owedWorld P f postA).globs = (owedWorld P f postB).globs := by
  simp only [owedWorld]
  rw [foldl_lese_globs, foldl_lese_globs]
  exact hpg

/-- The reason-search outcome is unchanged by a release fold. -/
theorem owedFailure_gibt (wa wb : World D)
    (hws : wa.slots = wb.slots) (hwg : wa.globs = wb.globs) :
    owedFailure P f wa = owedFailure P f wb := by
  unfold owedFailure
  have hfind : ∀ is : List D.Inv,
      (is.find? fun i => schuldet f i && !wahr? (eval wa (P.invariante i) wa .nil)) =
      (is.find? fun i => schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      have hi : (schuldet f i && !wahr? (eval wa (P.invariante i) wa .nil)) =
          (schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) := by
        rw [eval_spurfrei (P.invariante i) wa wb wa wb hws hwg hws hwg .nil]
      by_cases h : (schuldet f i && !wahr? (eval wa (P.invariante i) wa .nil)) = true
      · have h2 : (schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) = true := by
          rw [← hi]; exact h
        rw [List.find?_cons_of_pos (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wa (P.invariante j) wa .nil)) (a := i) (l := is) h,
            List.find?_cons_of_pos (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wb (P.invariante j) wb .nil)) (a := i) (l := is) h2]
      · have h2 : ¬(schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) = true := by
          intro hcon; apply h; rw [hi]; exact hcon
        rw [List.find?_cons_of_neg (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wa (P.invariante j) wa .nil)) (a := i) (l := is) h,
            List.find?_cons_of_neg (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wb (P.invariante j) wb .nil)) (a := i) (l := is) h2, ih]
  exact hfind D.invs

/-- The normal-return fault code is unchanged by a release fold. -/
theorem returnFault_lese_congr (σ0 : World D) (ρ : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (postA postB : World D)
    (hps : postA.slots = postB.slots) (hpg : postA.globs = postB.globs) :
    (if wahr? (eval σ0 (P.ensures f) postA (ergEnv (D.erg f) v ρ)) = false then 102
      else if (owedFailure P f (owedWorld P f postA)).isSome then 103 else 0) =
    (if wahr? (eval σ0 (P.ensures f) postB (ergEnv (D.erg f) v ρ)) = false then 102
      else if (owedFailure P f (owedWorld P f postB)).isSome then 103 else 0) := by
  have hens : wahr? (eval σ0 (P.ensures f) postA (ergEnv (D.erg f) v ρ)) =
      wahr? (eval σ0 (P.ensures f) postB (ergEnv (D.erg f) v ρ)) :=
    congrArg wahr? (eval_spurfrei (P.ensures f) σ0 σ0 postA postB rfl rfl hps hpg _)
  have hws := owedWorld_gibt_slots (P := P) (f := f) postA postB hps
  have hwg := owedWorld_gibt_globs (P := P) (f := f) postA postB hpg
  have hf := owedFailure_gibt (P := P) (f := f) _ _ hws hwg
  rw [hens, hf]

/-- The normal-return fault code survives the scope release. -/
theorem returnFault_gibt_foldl (σ0 σ1 : World D) (ρ : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (Ls : List D.Lock) :
    returnFault P f σ0 (Ls.foldl World.gibt σ1) ρ v =
      returnFault P f σ0 σ1 ρ v := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ1 Ls
  have hps : ((Ls.foldl World.gibt σ1).lese (vertragVon D f).ende
      (P.ensures f).orte).slots =
      (σ1.lese (vertragVon D f).ende (P.ensures f).orte).slots := hs
  have hpg : ((Ls.foldl World.gibt σ1).lese (vertragVon D f).ende
      (P.ensures f).orte).globs =
      (σ1.lese (vertragVon D f).ende (P.ensures f).orte).globs := hg
  exact returnFault_lese_congr (P := P) (f := f) σ0 ρ v _ _ hps hpg

/-- A normal scoped return simulates like the ordinary return on the released world. -/
theorem RetZ_gibt_foldl {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {t : T} {m : Runner.Mem} {σ1 : World D}
    {v : ErgVal D (D.erg f)} (Ls : List D.Lock)
    (h : RetZ L P f σ0 ρ0 fp K rp cfp t m σ1 v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t m (Ls.foldl World.gibt σ1) v := by
  have hf := returnFault_gibt_foldl (P := P) (f := f) σ0 σ1 ρ0 v Ls
  simp only [RetZ, hf] at h ⊢
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

/-- A reason scoped return simulates like the ordinary reason return on the released world. -/
theorem RetWhy_gibt_foldl {fp : Runner.W} {K : Nat} {rp cfp : Runner.W}
    {t : T} {m : Runner.Mem} {σ1 : World D} {r : Fin (D.gruende f)}
    (Ls : List D.Lock)
    (h : RetWhy L f fp K rp cfp t m σ1 r) :
    RetWhy L f fp K rp cfp t m (Ls.foldl World.gibt σ1) r := by
  simp only [RetWhy] at h ⊢
  obtain ⟨m', s, a, value, mirror, flag, world⟩ := h
  exact ⟨m', s, a, value, mirror, flag, WeltAt_gibt_foldl world⟩

end Freigabe

theorem retScoped_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {e : ErgExpr D Γ Λ (D.erg f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .retScoped e Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ hk hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon, lowRetScoped, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [execStmt, Sim]
  change max te (max tens (retTop (functionFrame P f))) + cap ≤ Ks at hK
  exact RetZ_gibt_foldl Rr.scopes (ret_ok (reserved := reserved) hlo0 hens e he (by omega) m pc σ ρ hp hlo2 hk hW hWa)

theorem retWhyScoped_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : Fin (D.gruende f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .retWhyScoped r Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ hk hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon, lowRetWhyScoped, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [execStmt, Sim]
  change max (frei Γ reserved) (retTop (functionFrame P f)) + cap ≤ Ks at hK
  exact RetWhy_gibt_foldl Rr.scopes (retWhy_ok r hlo0 (by omega) hp hk hW hWa)

theorem endRetScoped_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {e : ErgExpr D Γ Λ (D.erg f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .retScoped e Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp hlo _ hk hWa hpr
  simp only [lowEnd, ← hlo0, resultWords_vertragVon, lowRetScoped, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [execEnd, Ret]
  change max te (max tens (retTop (functionFrame P f))) + cap ≤ Ks at hK
  exact RetZ_gibt_foldl Rr.scopes (ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo hk hW hWa)

theorem endRetWhyScoped_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : Fin (D.gruende f)} {Rr : RueckRessourcen D (vertragVon D f) Λ} :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .retWhyScoped r Rr) reserved := by
  intro c top h hK _ hW m pc σ ρ hp hlo _ hk hWa hpr
  simp only [lowEnd, ← hlo0, resultWords_vertragVon, lowRetWhyScoped, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [execEnd, Ret]
  change max (frei Γ reserved) (retTop (functionFrame P f)) + cap ≤ Ks at hK
  exact RetWhy_gibt_foldl Rr.scopes (retWhy_ok r hlo0 (by omega) hp hk hW hWa)

end Gabbro.Stage0.Senke
