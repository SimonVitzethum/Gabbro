/-
  File:      Grammatik/RennfreiVoll.lean
  Subject:   DATA-RACE FREEDOM ON THE CALL MACHINE G, FULL FORM -- reads
             included, any distance, the release/acquire pair named by run
             index.

  `RennfreiG.lean` covers adjacent double writes (`rennfrei_g_nah`). Here:

  * An ACCESS of a step to a carrier `c` is a recorded access event on the
    acting thread's trace delta (`zugriffe`, read or write: every read of the
    semantics goes through `World.lese`, which records `zugriff t false Λ h`
    for every carrier of the read footprint; every write records its event)
    or a change of `c` in shared memory.
  * One trace invariant over every reachable machine (`SpurInv`): every
    thread trace is consistent (`Konsistent`) and every access event on it is
    good (`Ereignis.gut`: it carries its carrier's guards in its static `Λ`,
    and that `Λ`'s locks are held). It holds at the start and every step
    keeps it (`schritt_delta`, one case analysis over the 70 step rules).
  * From it: the acting thread holds every lock guard of every carrier its
    step accesses, before the step and after it (`zugriff_haelt`).
  * The ordering lemma over run indices (`sperre_ordnet`): two different
    threads holding one lock at steps `i < j` -- the first releases it at
    some step `r`, the second acquires it at some step `a`, with
    `i < r < a < j`, both steps recorded as `gibt L` / `nimmt L` events.
  * The theorem `rennfrei_g_voll` and the race notion `DatenRasse` (two
    accesses by different threads, at least one a write, NOT ordered by a
    release/acquire of a guard) with `keine_datenrasse_g`.
-/
import Grammatik.RennfreiG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Trace deltas of one step -/

/-- The trace delta of an ACCESS step: the new trace is `X ++ s`, every
    access event of `X` is old or good, consistency is kept, `X` takes no
    lock, and the held locks are unchanged. -/
def ZugriffsDelta (s s' : List (Ereignis D)) : Prop :=
  ∃ X : List (Ereignis D), s' = X ++ s ∧
    (∀ e ∈ X, e.istZugriff = true → e ∈ s ∨ e.gut) ∧
    (Konsistent s → Konsistent s') ∧ (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ X) ∧
    offen s' = offen s

/-- The trace delta of a LOCK step: the new trace is `X ++ s` with no access
    event in `X`, consistency kept. -/
def SperrDelta (s s' : List (Ereignis D)) : Prop :=
  ∃ X : List (Ereignis D), s' = X ++ s ∧ (∀ e ∈ X, e.istZugriff = false) ∧
    (Konsistent s → Konsistent s')

theorem zugriffsDelta_refl (s : List (Ereignis D)) : ZugriffsDelta s s :=
  ⟨[], rfl, fun _ he => absurd he List.not_mem_nil, id,
    fun _ _ h => absurd h List.not_mem_nil, rfl⟩

theorem zugriffsDelta_brav {σ σ' : World D} (hB : Brav σ σ') (neu : List (Ereignis D))
    (hneu : σ'.spur = neu ++ σ.spur) (hk : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
    ZugriffsDelta σ.spur σ'.spur :=
  ⟨neu, hneu, fun e he _ => hB.2.1 e (by rw [hneu]; exact List.mem_append_left _ he), hB.2.2, hk,
    hB.1⟩

theorem leseEv_zugriff (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    NurZugriff (leseEv σ Λ os) := by
  intro e he
  simp only [leseEv, List.mem_map] at he
  obtain ⟨o, _, rfl⟩ := he
  cases o <;> rfl

theorem zugriffsDelta_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob))
    (ho : ∀ o ∈ os, OrtDarf Λ o) (hh : HeldIn Λ σ.haelt) :
    ZugriffsDelta σ.spur (σ.lese Λ os).spur :=
  zugriffsDelta_brav (gut_lese (W := fun _ => true) (G := fun _ => true) σ Λ os ho hh).2
    (leseEv σ Λ os) rfl (kein_nimmt (leseEv_zugriff σ Λ os))

theorem sperrDelta_nimmt (s : List (Ereignis D)) (L : D.Lock) :
    SperrDelta s (Ereignis.nimmt L (offen s) :: s) :=
  ⟨[Ereignis.nimmt L (offen s)], rfl, fun e he => by
    rw [List.mem_singleton] at he; subst he; rfl, fun hk => konsistent_cons rfl hk⟩

theorem sperrDelta_gibt (s : List (Ereignis D)) (L : D.Lock) :
    SperrDelta s (Ereignis.gibt L :: s) :=
  ⟨[Ereignis.gibt L], rfl, fun e he => by
    rw [List.mem_singleton] at he; subst he; rfl, fun hk => konsistent_cons trivial hk⟩

/-- The static holdings of a residue give the held set of the thread world. -/
theorem heldIn_weltVon {M : RufMaschineG D} {f : Faden} {Λ : List (Res D)}
    (h : HeldIn Λ (offen (M.faeden f).spur)) : HeldIn Λ (M.weltVon f).haelt :=
  h

/-! ## 2. Every step moves the acting thread's trace by one of the two deltas -/

section Delta

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The trace delta of one step.** Every step of thread `f` either is an
    access step (`ZugriffsDelta`: no lock taken, held locks unchanged, new
    access events good) or a lock step (`SperrDelta`: only lock events, and
    shared memory unchanged). The lock steps are exactly `dannLocks`,
    `freiGib` and the two `frei` peels. -/
theorem schritt_delta (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    ZugriffsDelta (M.faeden f).spur (M'.faeden f).spur ∨
      (SperrDelta (M.faeden f).spur (M'.faeden f).spur ∧ M'.speicher = M.speicher) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      simp only [rufUpdateG_self]
      left
      have hw : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' := by
        rw [hstep]; rfl
      exact zugriffsDelta_brav ((Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ)
        σ' hw).2 neu hneu hkein
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      simp only [rufUpdateG_self]
      left
      have hw : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' := by
        rw [hstep]; rfl
      exact zugriffsDelta_brav ((Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ)
        σ' hw).2 neu hneu hkein
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      simp only [rufUpdateG_self]
      exact Or.inr ⟨sperrDelta_nimmt _ L, trivial⟩
  | freiGib l Γ Λ L k ρ hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr ⟨sperrDelta_gibt _ L, trivial⟩
  | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr ⟨sperrDelta_gibt _ L, trivial⟩
  | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr ⟨sperrDelta_gibt _ L, trivial⟩
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      simp only [rufUpdateG_self]
      left
      rw [hs₁, leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact zugriffsDelta_lese _ Λ _ (Expr.orte_darf inv)
        (fun L hL => hΛ L (Block.held_mono rest L hL))
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      left
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact zugriffsDelta_refl _
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      left
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact zugriffsDelta_refl _
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      left
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact zugriffsDelta_refl _
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      left
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact zugriffsDelta_refl _
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      left
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact zugriffsDelta_refl _
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      simp only [rufUpdateG_self]
      left
      subst hs₂ hs₁
      have ho : ∀ o ∈ (Sum.inr g :: neuE.orte), OrtDarf Λ o := by
        intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hL
        · exact Expr.orte_darf neuE o ho
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _ ho hΛ
      have hs := gut_schreibGlob (W := fun _ => true) (G := fun _ => true)
        ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)) g Λ
        (eval ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)) neuE
          ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte))
          (.cons (((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)).globs g) ρ)) rfl hL
        (hl.heldIn hΛ)
      refine zugriffsDelta_brav (hl.2.trans hs.2)
        (Ereignis.gzugriff g true Λ ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)).haelt ::
          leseEv (M.weltVon f) Λ (Sum.inr g :: neuE.orte)) rfl ?_
      intro L h hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
      · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      left
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
      have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        hd hgd hh1
      have e2 : σ₂ = (O.wirkt a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
          L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
        fun t hwr L hL => hh1 L (hd t hwr _ hL)
      have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
          L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
        fun g hwr L hL => hh1 L (hgd g hwr _ hL)
      obtain ⟨_, _, hcond⟩ := hO a ((M.weltVon f).lese Λ args.orte)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
      obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
      have hB : Brav (M.weltVon f) σ₂ := by
        have := hl.2.trans ha.2
        simp only [axiomAntwort] at this
        rw [e2]
        exact this
      refine zugriffsDelta_brav hB
        (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
          leseEv (M.weltVon f) Λ args.orte) (by rw [e2, hspur, List.append_assoc]; rfl) ?_
      intro L h hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
      · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
  | _ =>
      simp only [rufUpdateG_self]
      subst_vars
      left
      first
        | exact zugriffsDelta_refl _
        | exact zugriffsDelta_lese _ _ _ (Expr.orte_darf _) (heldIn_weltVon (by assumption))
        | exact zugriffsDelta_lese _ _ _ (Args.orte_darf _) (heldIn_weltVon (by assumption))
        | exact zugriffsDelta_lese _ _ _ (ErgExpr.orte_darf _) (heldIn_weltVon (by assumption))
        | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Args.orte_darf _))
            (heldIn_weltVon (by assumption))
        | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Expr.orte_darf _))
            (heldIn_weltVon (by assumption))
        | exact zugriffsDelta_lese _ _ _
            (fun o ho => by
              rw [List.mem_singleton] at ho
              subst ho
              assumption)
            (heldIn_weltVon (by assumption))

end Delta

/-! ## 3. The trace invariant over every reachable machine -/

/-- **The trace invariant**: every thread trace is consistent and every
    access event on it is good. -/
def SpurInv (M : RufMaschineG D) : Prop :=
  ∀ t : Faden, Konsistent (M.faeden t).spur ∧
    ∀ e ∈ (M.faeden t).spur, e.istZugriff = true → e.gut

theorem nimmtAlle_inv : ∀ (Ls : List D.Lock) (s : List (Ereignis D)), Konsistent s →
    Konsistent (nimmtAlle Ls s) ∧ ∀ e ∈ nimmtAlle Ls s, e ∈ s ∨ e.istZugriff = false
  | [], s, hk => ⟨hk, fun e he => Or.inl he⟩
  | L :: Ls, s, hk => by
      obtain ⟨hk', hm⟩ := nimmtAlle_inv Ls (Ereignis.nimmt L (offen s) :: s)
        (konsistent_cons rfl hk)
      refine ⟨hk', fun e he => ?_⟩
      rcases hm e he with he | he
      · rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr rfl
        · exact Or.inl he
      · exact Or.inr he

theorem start_spur (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
  show (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).spur = startSpur (init t).1
  cases init t
  rfl

theorem spurInv_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) : SpurInv (RufStartG P sp init) := by
  intro t
  rw [start_spur]
  obtain ⟨hk, hm⟩ := nimmtAlle_inv (D.haelt (init t).1) [] konsistent_nil
  refine ⟨hk, fun e he hz => ?_⟩
  rcases hm e he with he | he
  · exact absurd he List.not_mem_nil
  · rw [he] at hz; cases hz

theorem spurInv_schritt {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (hI : SpurInv M) : SpurInv M' := by
  intro t
  by_cases ht : t = f
  · subst ht
    obtain ⟨hk, hg⟩ := hI t
    rcases schritt_delta hO hs with ⟨X, e, hX, hK, _, _⟩ | ⟨⟨X, e, hX, hK⟩, _⟩
    · refine ⟨hK hk, fun ev hev hz => ?_⟩
      rw [e] at hev
      rcases List.mem_append.mp hev with hev | hev
      · rcases hX ev hev hz with h | h
        · exact hg ev h hz
        · exact h
      · exact hg ev hev hz
    · refine ⟨hK hk, fun ev hev hz => ?_⟩
      rw [e] at hev
      rcases List.mem_append.mp hev with hev | hev
      · rw [hX ev hev] at hz; cases hz
      · exact hg ev hev hz
  · rw [rufSchrittG_fremd hs t ht]
    exact hI t

theorem spurInv_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : SpurInv M := by
  induction hr with
  | start => exact spurInv_start P sp init
  | schritt M M' u _ hs ih => exact spurInv_schritt hO hs ih

/-! ## 4. Accesses and the events of one step -/

/-- The events one step of `f` prepended to `f`'s trace (newest first). -/
def ereignisse (M M' : RufMaschineG D) (f : Faden) : List (Ereignis D) :=
  (M'.faeden f).spur.take ((M'.faeden f).spur.length - (M.faeden f).spur.length)

theorem zugriffe_ereignisse (M M' : RufMaschineG D) (f : Faden) :
    zugriffe M M' f = (ereignisse M M' f).filterMap zugriffVon := rfl

theorem ereignisse_eq {M M' : RufMaschineG D} {f : Faden} {X : List (Ereignis D)}
    (e : (M'.faeden f).spur = X ++ (M.faeden f).spur) : ereignisse M M' f = X := by
  unfold ereignisse
  rw [e, List.length_append, Nat.add_sub_cancel]
  exact List.take_left

/-- A step ACCESSES the carrier `c`: it records an access event on `c`
    (read or write), or it changes `c` in shared memory. -/
def ZugriffG (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  (∃ w : Bool, (c, w) ∈ zugriffe M M' f) ∨ ¬ TraegerGleich M'.speicher M.speicher c

/-- A step WRITES `c`: it records a write event on `c`, or changes `c`. -/
def SchreibG (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  (c, true) ∈ zugriffe M M' f ∨ ¬ TraegerGleich M'.speicher M.speicher c

/-- A step READS `c`: its read footprint contains `c` (a recorded read
    event, as every `World.lese` of the step records one per carrier). -/
def LiestG (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  (c, false) ∈ zugriffe M M' f

theorem zugriffVon_some {e : Ereignis D} {c : D.Tab ⊕ D.Glob} {w : Bool}
    (h : zugriffVon e = some (c, w)) :
    (∃ t Λ hh, e = Ereignis.zugriff t w Λ hh ∧ c = Sum.inl t) ∨
      (∃ g Λ hh, e = Ereignis.gzugriff g w Λ hh ∧ c = Sum.inr g) := by
  cases e with
  | zugriff t w' Λ hh =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨t, Λ, hh, rfl, rfl⟩
  | gzugriff g w' Λ hh =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨g, Λ, hh, rfl, rfl⟩
  | nimmt => simp [zugriffVon] at h
  | gibt => simp [zugriffVon] at h

/-- Without a `nimmt` in `Y`, a lock open after `Y` was open before. -/
theorem offen_ohne_nimmt (L : D.Lock) : ∀ (Y s : List (Ereignis D)),
    (∀ (L' : D.Lock) (h : List D.Lock), Ereignis.nimmt L' h ∉ Y) → L ∈ offen (Y ++ s) →
      L ∈ offen s
  | [], _, _, h => h
  | e :: Y, s, hY, h => by
      have ih := offen_ohne_nimmt L Y s (fun L' h' hm => hY L' h' (List.mem_cons_of_mem _ hm))
      cases e with
      | zugriff => exact ih (by simpa [offen] using h)
      | gzugriff => exact ih (by simpa [offen] using h)
      | nimmt L' h' => exact absurd List.mem_cons_self (hY L' h')
      | gibt M => exact ih (List.mem_of_mem_erase (by simpa [offen] using h))

/-- A lock that leaves the open set across `X` is released in `X`. -/
theorem gibt_aus_offen (L : D.Lock) : ∀ (X s : List (Ereignis D)), L ∈ offen s →
    L ∉ offen (X ++ s) → Ereignis.gibt L ∈ X
  | [], _, h, hn => absurd h hn
  | e :: X, s, h, hn => by
      by_cases hg : Ereignis.gibt L ∈ X
      · exact List.mem_cons_of_mem _ hg
      · have hX : L ∈ offen (X ++ s) := by
          apply Classical.byContradiction
          intro hn'
          exact hg (gibt_aus_offen L X s h hn')
        cases e with
        | zugriff => exact absurd (by simpa [offen] using hX) hn
        | gzugriff => exact absurd (by simpa [offen] using hX) hn
        | nimmt M hm => exact absurd (by simp [offen, hX]) hn
        | gibt M =>
            by_cases hM : M = L
            · subst hM; exact List.mem_cons_self
            · exact absurd (by
                simp only [List.cons_append, offen]
                exact (List.mem_erase_of_ne (Ne.symm hM)).mpr hX) hn

/-- A lock that enters the open set across `X` is taken in `X`. -/
theorem nimmt_aus_offen (L : D.Lock) : ∀ (X s : List (Ereignis D)), L ∉ offen s →
    L ∈ offen (X ++ s) → ∃ h, Ereignis.nimmt L h ∈ X
  | [], _, hn, h => absurd h hn
  | e :: X, s, hn, h => by
      by_cases hX : L ∈ offen (X ++ s)
      · obtain ⟨h', hm⟩ := nimmt_aus_offen L X s hn hX
        exact ⟨h', List.mem_cons_of_mem _ hm⟩
      · cases e with
        | zugriff => exact absurd (by simpa [offen] using h) hX
        | gzugriff => exact absurd (by simpa [offen] using h) hX
        | nimmt M hm =>
            simp only [List.cons_append, offen, List.mem_cons] at h
            rcases h with rfl | h
            · exact ⟨hm, List.mem_cons_self⟩
            · exact absurd h hX
        | gibt M =>
            simp only [List.cons_append, offen] at h
            exact absurd (List.mem_of_mem_erase h) hX

/-- A recorded access event of a step of `f` on a carrier guarded by `L`:
    `f` holds `L` before the step. The event is good (its `Λ` names `L`, its
    recorded held set contains `L`) and consistent (the recorded held set is
    the open set behind it, inside the delta, which takes no lock). -/
theorem ereignis_haelt {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (hI' : SpurInv M') {c : D.Tab ⊕ D.Glob} {w : Bool} (hz : (c, w) ∈ zugriffe M M' f)
    {L : D.Lock} (hB : Bewacht c L) :
    L ∈ offen (M.faeden f).spur ∧ offen (M'.faeden f).spur = offen (M.faeden f).spur := by
  rw [zugriffe_ereignisse] at hz
  obtain ⟨e, he, hzv⟩ := List.mem_filterMap.mp hz
  have hez : e.istZugriff = true := by
    rcases zugriffVon_some hzv with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ <;> rfl
  rcases schritt_delta hO hs with ⟨X, eX, _, _, hnX, hoff⟩ | ⟨⟨X, eX, hX, _⟩, _⟩
  · refine ⟨?_, hoff⟩
    rw [ereignisse_eq eX] at he
    obtain ⟨hk, hg⟩ := hI' f
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
    have hget : (M'.faeden f).spur[n]? = some X[n] := by
      rw [eX, List.getElem?_append_left hn]
      exact List.getElem?_eq_getElem hn
    have hp := hk n _ hget
    have hgut := hg X[n] (by rw [eX]; exact List.mem_append_left _ he) hez
    have hdrop : (M'.faeden f).spur.drop (n + 1) = X.drop (n + 1) ++ (M.faeden f).spur := by
      rw [eX]
      exact List.drop_append_of_le_length hn
    have hY : ∀ (L' : D.Lock) (h : List D.Lock), Ereignis.nimmt L' h ∉ X.drop (n + 1) :=
      fun L' h hm => hnX L' h (List.mem_of_mem_drop hm)
    rw [hdrop] at hp
    rcases zugriffVon_some hzv with ⟨t, Λ, hh, e1, rfl⟩ | ⟨g, Λ, hh, e1, rfl⟩
    · rw [e1] at hp hgut
      simp only [Ereignis.passt] at hp
      simp only [Ereignis.gut] at hgut
      have hL : L ∈ hh := hgut.2 L (hgut.1 _ hB)
      rw [hp] at hL
      exact offen_ohne_nimmt L _ _ hY hL
    · rw [e1] at hp hgut
      simp only [Ereignis.passt] at hp
      simp only [Ereignis.gut] at hgut
      have hL : L ∈ hh := hgut.2 L (hgut.1 _ hB)
      rw [hp] at hL
      exact offen_ohne_nimmt L _ _ hY hL
  · rw [ereignisse_eq eX] at he
    rw [hX e he] at hez
    cases hez

/-- **Every access holds the guard, before and after.** A step of `f` on a
    reachable machine that accesses a carrier `c` guarded by `L` (a recorded
    read or write event, or a memory change) holds `L` before the step, and
    the step keeps the held locks. -/
theorem zugriff_haelt {P : Programm D} {O : Orakel D} {passes : Nat} (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O)
    (hex : StartExklusiv init) {M M' : RufMaschineG D} {f : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hs : RufSchrittG P O passes M f M') {c : D.Tab ⊕ D.Glob} {L : D.Lock} (hB : Bewacht c L)
    (hz : ZugriffG M M' f c) :
    L ∈ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur := by
  rcases hz with ⟨w, hw⟩ | hm
  · have hI' := spurInv_erreichbar hO sp init (RufErreichbarG.schritt M M' f hr hs)
    obtain ⟨h1, h2⟩ := ereignis_haelt hO hs hI' hw hB
    exact ⟨h1, by rw [h2]; exact h1⟩
  · have h1 := (rennfrei_g P O passes sp init hO hex M M' f hr hs c L hB hm).1
    rcases schritt_delta hO hs with ⟨_, _, _, _, _, hoff⟩ | ⟨_, hsp⟩
    · exact ⟨h1, by rw [hoff]; exact h1⟩
    · exact absurd (by rw [hsp]; exact traegerGleich_refl _ c) hm

/-! ## 5. Runs by index, and the ordering through a lock -/

/-- A run of `n` steps from `M0`, by index: machine `ms k`, actor `fs k`. -/
def LaufG (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat) : Prop :=
  ms 0 = M0 ∧ ∀ k, k < n → RufSchrittG P O passes (ms k) (fs k) (ms (k + 1))

theorem laufG_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) : ∀ k, k ≤ n → RufErreichbarG P O passes M0 (ms k)
  | 0, _ => by rw [hl.1]; exact .start
  | k + 1, hk => .schritt _ _ _ (laufG_erreichbar hl k (by omega)) (hl.2 k (by omega))

/-- Two runs glued at the end of the first. -/
theorem laufG_verketten {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms0 ms1 : Nat → RufMaschineG D} {fs0 fs1 : Nat → Faden} {n0 n1 : Nat}
    (h0 : LaufG P O passes M0 ms0 fs0 n0) (h1 : LaufG P O passes (ms0 n0) ms1 fs1 n1) :
    LaufG P O passes M0 (fun k => if k ≤ n0 then ms0 k else ms1 (k - n0))
      (fun k => if k < n0 then fs0 k else fs1 (k - n0)) (n0 + n1) := by
  refine ⟨by simp only [Nat.zero_le, if_true]; exact h0.1, fun k hk => ?_⟩
  dsimp only
  by_cases hk0 : k < n0
  · rw [if_pos (Nat.le_of_lt hk0), if_pos hk0, if_pos (show k + 1 ≤ n0 by omega)]
    exact h0.2 k hk0
  · have e1 : (if k ≤ n0 then ms0 k else ms1 (k - n0)) = ms1 (k - n0) := by
      split
      · have e : k = n0 := by omega
        subst e
        rw [Nat.sub_self]
        exact h1.1.symm
      · rfl
    have e2 : (if k + 1 ≤ n0 then ms0 (k + 1) else ms1 (k + 1 - n0)) = ms1 (k - n0 + 1) := by
      rw [if_neg (by omega)]
      congr 1
      omega
    rw [e1, e2, if_neg hk0]
    exact h1.2 (k - n0) (by omega)

/-- A thread that does not act in a run keeps its state. -/
theorem laufG_fremd {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) (g : Faden) (hg : ∀ k, k < n → fs k ≠ g) :
    ∀ k, k ≤ n → (ms k).faeden g = M0.faeden g
  | 0, _ => by rw [hl.1]
  | k + 1, hk => by
      rw [rufSchrittG_fremd (hl.2 k (by omega)) g (Ne.symm (hg k (by omega)))]
      exact laufG_fremd hl g hg k (by omega)

/-- The first change of a property along the indices. -/
theorem erster_wechsel (Q : Nat → Prop) : ∀ (b a : Nat), a ≤ b → Q a → ¬ Q b →
    ∃ r, a ≤ r ∧ r < b ∧ Q r ∧ ¬ Q (r + 1)
  | 0, a, hab, hq, hn => by
      have : a = 0 := by omega
      subst this
      exact absurd hq hn
  | b + 1, a, hab, hq, hn => by
      have hab' : a ≤ b := by
        rcases Nat.lt_or_ge b a with h | h
        · have : a = b + 1 := by omega
          subst this
          exact absurd hq hn
        · exact h
      by_cases hb : Q b
      · exact ⟨b, hab', by omega, hb, hn⟩
      · obtain ⟨r, h1, h2, h3, h4⟩ := erster_wechsel Q b a hab' hq hb
        exact ⟨r, h1, by omega, h3, h4⟩

/-- A release of `L` by `f` in the step `M → M'`: held before, not after,
    and the step recorded `gibt L`. -/
def GibtFrei (M M' : RufMaschineG D) (f : Faden) (L : D.Lock) : Prop :=
  L ∈ offen (M.faeden f).spur ∧ L ∉ offen (M'.faeden f).spur ∧ Ereignis.gibt L ∈ ereignisse M M' f

/-- An acquire of `L` by `f` in the step `M → M'`: not held before, held
    after, no other thread held it, and the step recorded `nimmt L`. -/
def NimmtAn (M M' : RufMaschineG D) (f : Faden) (L : D.Lock) : Prop :=
  L ∉ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur ∧ RufFreiG M f L ∧
    ∃ h : List D.Lock, Ereignis.nimmt L h ∈ ereignisse M M' f

/-- **Happens-before through the lock `L`**: between the steps `i` and `j`
    the actor of `i` releases `L` at `r` and the actor of `j` acquires it at
    `a`, with `i < r < a < j`. -/
def GeordnetG (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (L : D.Lock) (i j : Nat) : Prop :=
  ∃ r a, i < r ∧ r < a ∧ a < j ∧ fs r = fs i ∧ fs a = fs j ∧
    GibtFrei (ms r) (ms (r + 1)) (fs i) L ∧ NimmtAn (ms a) (ms (a + 1)) (fs j) L

/-- **The ordering through a lock.** On a run from an exclusive start, if
    thread `fs i` holds `L` after its step `i` and thread `fs j ≠ fs i`
    holds `L` before its step `j > i`, then `fs i` releases `L` at some step
    `r` and `fs j` acquires it at some step `a`, with `i < r < a < j`. -/
theorem sperre_ordnet {P : Programm D} {O : Orakel D} {passes : Nat} (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O) (hex : StartExklusiv init)
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : fs i ≠ fs j) (L : D.Lock)
    (hi : L ∈ offen ((ms (i + 1)).faeden (fs i)).spur)
    (hj : L ∈ offen ((ms j).faeden (fs j)).spur) : GeordnetG ms fs L i j := by
  have hx : ∀ k, k ≤ n → ∀ u v : Faden, u ≠ v → L ∈ offen ((ms k).faeden u).spur →
      L ∉ offen ((ms k).faeden v).spur :=
    fun k hk u v huv hu => exklusivG hO sp init hex (laufG_erreichbar hl k hk) u v huv L hu
  -- the release: the first index after `i` where `fs i` no longer holds `L`
  obtain ⟨r, hr1, hr2, hQr, hQr1⟩ := erster_wechsel
    (fun k => L ∈ offen ((ms k).faeden (fs i)).spur) j (i + 1) (by omega) hi
    (hx j (by omega) (fs j) (fs i) (Ne.symm hfg) hj)
  have hsr := hl.2 r (by omega)
  have hfr : fs r = fs i := by
    apply Classical.byContradiction
    intro hne
    exact hQr1 (by rw [rufSchrittG_fremd hsr (fs i) (Ne.symm hne)]; exact hQr)
  rw [hfr] at hsr
  have hgibt : Ereignis.gibt L ∈ ereignisse (ms r) (ms (r + 1)) (fs i) := by
    rcases schritt_delta hO hsr with ⟨_, _, _, _, _, hoff⟩ | ⟨⟨X, eX, _, _⟩, _⟩
    · exact absurd (by rw [hoff]; exact hQr) hQr1
    · rw [ereignisse_eq eX]
      exact gibt_aus_offen L X _ hQr (by rw [← eX]; exact hQr1)
  -- the acquire: the last index before `j` where `fs j` does not hold `L`
  have hn1 : L ∉ offen ((ms (r + 1)).faeden (fs j)).spur := by
    rw [rufSchrittG_fremd hsr (fs j) (Ne.symm hfg)]
    exact hx r (by omega) (fs i) (fs j) hfg hQr
  obtain ⟨a, ha1, ha2, hQa, hQa1⟩ := erster_wechsel
    (fun k => L ∉ offen ((ms k).faeden (fs j)).spur) j (r + 1) (by omega) hn1
    (fun h => h hj)
  have hQa1' : L ∈ offen ((ms (a + 1)).faeden (fs j)).spur :=
    Classical.byContradiction hQa1
  have hsa := hl.2 a (by omega)
  have hfa : fs a = fs j := by
    apply Classical.byContradiction
    intro hne
    exact hQa (by rw [← rufSchrittG_fremd hsa (fs j) (Ne.symm hne)]; exact hQa1')
  rw [hfa] at hsa
  have hnimmt : ∃ h, Ereignis.nimmt L h ∈ ereignisse (ms a) (ms (a + 1)) (fs j) := by
    rcases schritt_delta hO hsa with ⟨_, _, _, _, _, hoff⟩ | ⟨⟨X, eX, _, _⟩, _⟩
    · exact absurd (by rw [← hoff]; exact hQa1') hQa
    · rw [ereignisse_eq eX]
      exact nimmt_aus_offen L X _ hQa (by rw [← eX]; exact hQa1')
  have hfrei : RufFreiG (ms a) (fs j) L := by
    intro u hu
    rw [← rufSchrittG_fremd hsa u hu]
    exact hx (a + 1) (by omega) (fs j) u (Ne.symm hu) hQa1'
  exact ⟨r, a, by omega, by omega, ha2, hfr, hfa, ⟨hQr, hQr1, hgibt⟩,
    ⟨hQa, hQa1', hfrei, hnimmt⟩⟩

/-! ## 6. The theorem -/

/-- **Data-race freedom on the call machine G, full form (`rennfrei_g_voll`).**
    On every run from `RufStartG P sp init` (good oracle, exclusive start),
    any two accesses by different threads to one carrier `c` guarded by the
    lock `L` -- at steps `i < j`, each a recorded read or write event or a
    memory change -- are ordered through `L`: the first thread releases `L`
    at some step `r`, the second acquires it at some step `a`, with
    `i < r < a < j`. Reads included, any distance; it holds for read/read
    pairs too, so in particular for every pair with at least one write.
    Every premise is used: `hO`/`hex` for the invariant, exclusivity and the
    holder form; `hl` for reachability and the steps; `hij`/`hjn`/`hfg` for
    the ordering; `hB`/`hzi`/`hzj` for the held guard. -/
theorem rennfrei_g_voll (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O) (hex : StartExklusiv init)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : fs i ≠ fs j) (c : D.Tab ⊕ D.Glob) (L : D.Lock) (hB : Bewacht c L)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (fs i) c)
    (hzj : ZugriffG (ms j) (ms (j + 1)) (fs j) c) : GeordnetG ms fs L i j := by
  have hi := zugriff_haelt sp init hO hex (laufG_erreichbar hl i (by omega)) (hl.2 i (by omega))
    hB hzi
  have hj := zugriff_haelt sp init hO hex (laufG_erreichbar hl j (by omega)) (hl.2 j hjn) hB hzj
  exact sperre_ordnet sp init hO hex hl i j hij hjn hfg L hi.2 hj.1

/-- **A data race** on a run: two accesses by different threads to one
    lock-guarded carrier, at least one a write, the carrier neither an
    atomic global nor a published payload (the lock-free disciplines,
    excluded by their declared discipline as in `SchreibRasse`), and NOT
    ordered through any guard of the carrier. -/
def DatenRasse (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (i j : Nat)
    (c : D.Tab ⊕ D.Glob) : Prop :=
  i < j ∧ fs i ≠ fs j ∧ ZugriffG (ms i) (ms (i + 1)) (fs i) c ∧
    ZugriffG (ms j) (ms (j + 1)) (fs j) c ∧
    (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) ∧
    ¬ AtomarAusgenommen c ∧ ¬ PaarungAusgenommen c ∧ (∃ L : D.Lock, Bewacht c L) ∧
    ∀ L : D.Lock, Bewacht c L → ¬ GeordnetG ms fs L i j

/-- **No data race on a lock-guarded carrier** (`keine_datenrasse_g`), on
    every run from an exclusive start with a good oracle. The write and the
    lock-free exclusions of `DatenRasse` travel unused: the ordering holds
    for every pair of accesses. -/
theorem keine_datenrasse_g (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O) (hex : StartExklusiv init)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hjn : j < n)
    (c : D.Tab ⊕ D.Glob) : ¬ DatenRasse ms fs i j c := by
  rintro ⟨hij, hfg, hzi, hzj, _, _, _, ⟨L, hB⟩, hno⟩
  exact hno L hB (rennfrei_g_voll P O passes sp init hO hex ms fs n hl i j hij hjn hfg c L hB
    hzi hzj)

/-! ## CUTS:

  What is proved: the trace delta of every step rule (`schritt_delta`: an
  access step takes no lock, keeps the held set and adds only good access
  events; a lock step adds only lock events and keeps memory); the trace
  invariant on every reachable machine (`spurInv_erreichbar`); the guard
  holding of every access, read or write, before and after the step
  (`zugriff_haelt`); the ordering through a lock over run indices
  (`sperre_ordnet`, release `gibt L` by the first thread and acquire
  `nimmt L` by the second, strictly between the two accesses); the
  full-form theorem `rennfrei_g_voll` (every pair of accesses by different
  threads to a lock-guarded carrier, reads included, any distance) and
  `keine_datenrasse_g` (no pair with at least one write is unordered). The
  joint witness is `rennfrei_g_voll_zeuge` (`TravAwaitsLauf.lean`): a write
  at step 16 and a read at step 24 by different threads.

  What the access notion covers: every read the semantics performs through
  `World.lese` (expressions, arguments, conditions, loop heads, `awaits`,
  `exchange`, returns) and every write (slot/global/byte writes, publish,
  transition, exchange, the axiom's recorded `axiomSpur` writes), and every
  memory change. The accesses to a carrier are ordered for EVERY lock guard
  of it.

  What is NOT covered, precisely:
  * reads by the ORACLE: an axiom's `O.wirkt`, a register read's
    `O.regLies` and an `awaits`'s visibility answer `O.sichtbar` may depend
    on memory without recording a read event; they are hardware, not
    program accesses (`RegLokal` bounds the register and visibility answers
    to the declared carriers, it records nothing);
  * carriers without a lock guard: `atomic` globals (ordered by the machine,
    A10), published payloads (ordered by the publish/awaits pairing), and
    unshared carriers (`D.geteilt = false`, guarded by an owner mark or by
    nothing: one thread's own state, W5 of `Gesittet`, a checker duty) --
    for those the theorem has no premise `Bewacht c L` to start from, and
    the ownership ordering (single-thread marks) is not proved on G here.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.schritt_delta
#print axioms Gabbro.Grammatik.rennfrei_g_voll
#print axioms Gabbro.Grammatik.keine_datenrasse_g
