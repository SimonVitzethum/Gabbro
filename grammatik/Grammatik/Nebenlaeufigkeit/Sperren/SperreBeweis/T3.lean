/- Part 3 of 3 of `SperreBeweis` (split by instrumente/teile/lean-teilen.py; the umbrella `SperreBeweis.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritte2

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **An axiom step keeps the replay** (as `fadenR_ax`). Without an event
    the recorded answer is the machine oracle's own (`hxO`). -/
theorem fadenS_ax {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hxO : ¬ Nonempty (Ereignis D) →
      xm.2 = (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a)) (evalArgs (W.lese Λ args.orte) args
        (W.lese Λ args.orte) ρ)).2)
    (hlok : AxEnsLokal Q)
    (hxq : ∀ v : ErgVal D (D.aerg a), einpassenErg O.zeiger (D.aerg a) xm.2 = some v → Q a xm.1 v = true)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D), ZeigerGleich O O' →
      O'.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2) →
      (semH S O' U passes R r σ ρ).folgt
        (semH S O' U passes R r' (axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1) ρ')) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok0, heq⟩, hS⟩ :=
    hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by
    rw [hr] at hok0; exact hok0
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  have hlen : σ.spur.length ≤ ((σ.lese Λ args.orte).fragt (.inl a)).spur.length :=
    Nat.le_trans (lese_laenge _ _ _) (Nat.le_succ _)
  have hlen2 : σ.spur.length ≤ (axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1).spur.length :=
    Nat.le_trans hlen (axWeltF_laenge _ _ _)
  have hlt : Nonempty (Ereignis D) →
      ((σ.lese Λ args.orte).fragt (.inl a)).spur.length < (axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1).spur.length :=
    fun hN => frischSpur_laenge hN _
  have hpa : ¬ Nonempty (Ereignis D) → PasstA O (HA ++ [⟨a, (σ.lese Λ args.orte).fragt (.inl a),
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2)⟩]) := by
    intro hN a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hka.2 hN a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      rw [hxO hN, welt_eq hN (σ.lese Λ args.orte) (W.lese Λ args.orte)]
      exact Prod.ext (welt_eq hN _ _) rfl
  refine ⟨⟨H, HA ++ [⟨a, (σ.lese Λ args.orte).fragt (.inl a),
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2)⟩], HU,
    axWeltF a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, hreq, hf, hv,
    kurzVB_mono hk hlen2, ?_, ?_, ?_, ?_,
    hfu, hiu, kurzUB_mono hku hlen2, ?_, hok hok', ?_⟩, hS⟩
  · by_cases hN : Nonempty (Ereignis D)
    · exact funkA_append hfa (hka.1 hN) _ hlen
    · exact funkA_of_passtA (hpa hN)
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWeltF_rahmen a _ _
  · intro a' σk ρk x hm v hv
    rcases List.mem_append.mp hm with hm | hm
    · exact hqa a' σk ρk x hm v hv
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWeltF_vertrag hlok a _ _ v (hxq v hv)
  · refine ⟨fun hN e hm => ?_, hpa⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka.1 hN e hm) hlen2
    · rw [List.mem_singleton] at hm
      subst hm
      exact hlt hN
  · have h1 := axWeltF_gleichAuf a (hg0.lese Λ Λ args.orte args.orte) hxm
    exact gleichAuf_stabil_iff hΛ' ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' U hR hA hU hQ
    have h1 := heq R O' U hR (passtA_append hA) hU hQ
    rw [hr] at h1
    exact ZErgG.folgt_trans h1
      (hsem O' R U σ hQ.2.2 (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer. -/
theorem fadenS_blatt (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hFS : ∀ f, FussS P S lok f) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D),
      semH S O' U passes R r σ ρ = weiterH S O' U passes R K (execStmtH S O' U passes R s σ ρ))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  have hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ := s.held_iff
  cases hax : s.istAxiom with
  | false =>
      refine fadenS_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      have hs' : stmtOrteP P s ⊆ stabilS P S lok z.kopf.f Λ :=
        orte_stabil (hFS _) (s.blatt_darf P hleaf) hs
      obtain ⟨σs, hes, hgs, hls⟩ := blatt_lokalV P O passes s hleaf hax hs' hg hstep
      refine ⟨σs, hls, gleichAuf_stabil_iff hΛ' ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩,
        hK, fun R O' U => ?_⟩
      rw [hsem, execStmtH_blatt S O' U passes R s hleaf, hes]
      exact ZErgG.folgt_refl _
  | true =>
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          obtain ⟨e1, e2, u, hu⟩ := axiomCall_ok_inv O passes keinRuf a args h hw hg hd hgd W ρ σ' ρ'
            hstep
          subst e2
          have hfr := (hO a ((W.lese Λ args.orte).fragt (.inl a))
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenS_ax hF hr ρ' K σ'.spur hΛ' a args (fun h' => (hok h').2)
            (σ', (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a))
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr (fun _ => rfl)
            hlok
            (fun v hv => by
              rw [e1]
              exact hQ a _ _ v hv) ?_
          intro O' R U σ hz hw
          rw [hsem]
          apply ZErgG.folgt_of_eq
          simp only [execStmtH, axiomAntwort, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp only [Stmt.istAxiom, Bool.false_eq_true] at hax

/-- **The acquire keeps the replay.** At `locks L { body }` with `L` free in
    the machine, the invariant of `L` holds at the machine memory
    (`SperrInvG`, `SperreMaschine.lean`), so the move "protected carriers of
    `L` from the machine" is in the class; it is recorded at the sequential
    key, the new sequential world takes the protected carriers from the
    machine, and the stable set grows by them. -/
theorem fadenS_locks {z : RufFadenG D} {W : World D} (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hrL : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hrL body) rest) k⟩)
    (hinv : S.inv L W.speicher = true) (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest k))⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok, heq⟩, hS⟩ :=
    hF
  rw [hr] at hg hok
  simp only at hg hok
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  have hlen : σ.spur.length < ((mischU S L σ W.speicher).nimmt L).spur.length := by
    show σ.spur.length < (Ereignis.nimmt L _ :: σ.spur).length
    exact Nat.lt_succ_self _
  refine ⟨⟨H, HA, HU ++ [(L, σ, W.speicher)], (mischU S L σ W.speicher).nimmt L, hreq, hf, hv,
    kurzVB_mono hk (Nat.le_of_lt hlen), hfa, hra, hqa, kurzAB_mono hka (Nat.le_of_lt hlen),
    funkU_append hfu (hku ⟨.gibt L⟩) _ (Nat.le_refl _), invU_append hiu L σ W.speicher hinv, ?_, ?_,
    ⟨hks, hss, hrest⟩, ?_⟩, hS⟩
  · intro hN e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_trans (hku hN e he) hlen
    · rw [List.mem_singleton] at he
      subst he
      exact hlen
  · -- agreement on the grown stable set
    have key : ∀ c ∈ stabilS P S lok z.kopf.f (Res.held L :: Λ),
        TraegerGleich ((mischU S L σ W.speicher).nimmt L).speicher W.speicher c := by
      intro c hc
      by_cases hcL : c ∈ S.orte L
      · exact mischU_innen S L σ W.speicher c hcL
      · have hc' : c ∈ stabilS P S lok z.kopf.f Λ := by
          rcases stabilS_mem.mp hc with hc | ⟨K, hK, hcK⟩
          · exact stabilS_mem.mpr (Or.inl hc)
          · rcases List.mem_cons.mp hK with hK | hK
            · cases hK
              exact absurd hcK hcL
            · exact stabilS_mem.mpr (Or.inr ⟨K, hK, hcK⟩)
        refine traegerGleich_trans (mischU_aussen S L σ W.speicher c hcL) ?_
        cases c with
        | inl t => exact hg.1 t hc'
        | inr g => exact hg.2 g hc'
    exact ⟨fun t ht => key (.inl t) ht, fun g hg' => key (.inr g) hg'⟩
  · intro R O' U hR hA hU hQ
    have h1 := heq R O' U hR hA (passtU_append hU) hQ
    rw [hr] at h1
    simp only at h1
    refine ZErgG.folgt_trans h1 (ZErgG.folgt_of_eq ?_)
    rw [semH_locks S O' U passes R L hrL body rest k σ ρ,
      hU L σ W.speicher (List.mem_append_right _ List.mem_cons_self)]

end Schritte2
/-! ## 4. The head never predicts a `logik` outcome; the release steps -/

section Frei

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **The head's prediction is never a `logik` outcome** (as
    `kopfR_keineLogik`): against the record handler with hardware default,
    the record oracle and the record's environment move. -/
theorem kopfS_keineLogik (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
      F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ e : Logik D,
        semH S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) F.rest.2.2.2.2 σ
          F.rest.2.2.2.1 ≠ .logik e := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, hok, heq⟩ := hG
  refine ⟨H, HA, HU, σ, hg, hok, fun e he => ?_⟩
  have h1 := heq (rufAusL H) (orakelAus O HA) (umweltAus S sp HU) (rufAusL_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [he] at h1
  exact (hK F.f).2 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusL H)
    (rufAusL_rahmen hv) (rufAusL_ohneLogik hv.1) F.s0 F.rho hreq e
    (zErgG_gleich_logik (ZErgG.folgt_logik h1))

/-- The same, for a residue named by its shape. -/
theorem kopfS_keineLogik' (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
      GleichAuf (stabilS P S lok F.f Λ) σ W ∧ r.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ e : Logik D, semH S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) r σ ρ ≠
        .logik e := by
  obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik hO hRL hQ hS hsp hK hG
  rw [hr] at hok hno hg
  exact ⟨H, HA, HU, σ, hg, hok, hno⟩

/-- **At a release the invariant holds in the machine.** A head at the
    release marker `frei L` (after the body) or at a `leave`/`next` that
    leaves the body: the release check passes at the sequential world (else
    the head would predict `logik schleife`), and the protected carriers of
    `L` are stable (the frame holds `L`), so the check passes at the machine
    memory. -/
theorem kopfS_frei_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (L : D.Lock) (hL : Res.held L ∈ Λ) {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hlog : ∀ (O' : Orakel D) (U : Umwelt D) R (σ : World D), S.inv L σ.speicher = false →
      semH S O' U passes R r σ ρ = .logik .schleife) :
    S.inv L W.speicher = true := by
  obtain ⟨H, HA, HU, σ, hg, _, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hG hr
  have hi : S.inv L σ.speicher = true := by
    cases h : S.inv L σ.speicher with
    | true => rfl
    | false => exact absurd (hlog _ _ _ σ h) (hno .schleife)
  rw [← hi]
  refine hS.2 L _ _ fun c hc => ?_
  have hcs : c ∈ stabilS P S lok F.f Λ := stabilS_mem.mpr (Or.inr ⟨L, hL, hc⟩)
  cases c with
  | inl t => exact (hg.1 t hcs).symm
  | inr g => exact (hg.2 g hcs).symm

/-- The invariant of a held lock is the same at two worlds agreeing on the
    stable carriers. -/
theorem inv_gleich (hS : SperrInvOk S) {f : D.Fn} {Λ : List (Res D)} {L : D.Lock}
    (hL : Res.held L ∈ Λ) {σ W : World D} (hg : GleichAuf (stabilS P S lok f Λ) σ W) :
    S.inv L σ.speicher = S.inv L W.speicher := by
  refine hS.2 L _ _ fun c hc => ?_
  have hcs : c ∈ stabilS P S lok f Λ := stabilS_mem.mpr (Or.inr ⟨L, hL, hc⟩)
  cases c with
  | inl t => exact hg.1 t hcs
  | inr g => exact hg.2 g hcs

/-- Agreement read at a released world with the machine memory. -/
theorem gleichAuf_frei {f : D.Fn} {Λ : List (Res D)} {L : D.Lock} {σ W : World D}
    (hg : GleichAuf (stabilS P S lok f (Res.held L :: Λ)) σ W) (spur' : List (Ereignis D)) :
    GleichAuf (stabilS P S lok f Λ) (σ.gibt L) (W.speicher.welt spur') :=
  GleichAuf.mono (fun _ h => stabilS_mono (fun _ h' => List.mem_cons_of_mem _ h') h)
    ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩

/-- **The release after the body keeps the replay** (`freiGib`). -/
theorem fadenS_frei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ, k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hW := kopfS_frei_inv hO hRL hQ hS hsp hK hF.1 L List.mem_cons_self hr
    (fun O' U R σ h => semH_frei_falsch S O' U passes R L k σ ρ h)
  refine fadenS_lokal hF hr ρ k spur' (fun σ hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  exact ⟨σ.gibt L, Nat.le_succ _, gleichAuf_frei hg spur', hok,
    fun R O' U => ZErgG.folgt_of_eq (semH_frei S O' U passes R L k σ ρ hiσ)⟩

/-- **A `leave`/`next` out of a `locks` body keeps the replay**
    (`peelFreiLeave`, `peelFreiNext`). -/
theorem fadenS_peelFrei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W) {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D (vertragVon D z.kopf.f) true Γ Λ (Res.held L :: Λ1))
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (ρ : Env D Γ) (h : true = true) (x : Bool)
    (hr : z.kopf.rest =
      ⟨true, Γ, Λ, ρ, .dann (.cons (if x then .leave h else .next h) rest) (.frei L k)⟩)
    (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨true, Γ, Λ1, ρ, .dann (.cons (if x then .leave h else .next h) .nil) k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hLΛ : Res.held L ∈ Λ := (Block.held_iff rest L).mp List.mem_cons_self
  have hΛ1 : ∀ M, Res.held M ∈ Λ1 → Res.held M ∈ Λ :=
    fun M hM => (Block.held_iff rest M).mp (List.mem_cons_of_mem _ hM)
  have hW := kopfS_frei_inv hO hRL hQ hS hsp hK hF.1 L hLΛ hr
    (fun O' U R σ hi => semH_peelFrei_falsch S O' U passes R L rest k σ ρ h x hi)
  refine fadenS_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS hLΛ hg).trans hW
  obtain ⟨_, _, hk⟩ := hok
  refine ⟨σ.gibt L, Nat.le_succ _,
    GleichAuf.mono (fun _ hc => stabilS_mono hΛ1 hc) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩,
    ⟨by cases x <;> rfl, fun _ hc => by cases x <;> simp only [blockOrteP, Bool.false_eq_true, ↓reduceIte, stmtOrteP, List.append_nil, List.not_mem_nil] at hc, hk⟩,
    fun R O' U => ZErgG.folgt_of_eq (semH_peelFrei S O' U passes R L rest k σ ρ h x hiσ)⟩

end Frei

#print axioms Gabbro.Grammatik.welt_eq
#print axioms Gabbro.Grammatik.begruendet_eindeutig
#print axioms Gabbro.Grammatik.funkV_appendB
#print axioms Gabbro.Grammatik.popS_kopf
#print axioms Gabbro.Grammatik.fadenS_ax


end Gabbro.Grammatik
