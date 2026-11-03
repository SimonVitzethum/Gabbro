module
public import Grammatik.Speichermodell.Atomar.AtomarReplay.T2.Teil2Basis

public import Grammatik.Speichermodell.Atomar.AtomarReplay.T1
public import Grammatik.Speichermodell.Atomar.AtomarReplay.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}
/-- **A leaf's outcome world extends the world after its reads** (non-axiom leaves). -/
theorem blatt_lese_laenge (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) {σ : World D} {ρ : Env D Γ} {σ' : World D} {ρ' : Env D Γ}
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    (σ.lese Λ (stmtOrteP P s)).spur.length ≤ σ'.spur.length := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignThru p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignThruOwn p t ht f i e m s ho he hg hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignSlotRef r t ht ho f e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibGlob _ _ _ _)
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibBytes _ _ _ _ _ _ _)
  | assignVar x e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_refl _
  | shift t f hτ i von nach hn he hw hL =>
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
      · cases h
  | regWrite r hk e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_refl _
  | transition r hk m hm hmk maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_succ _
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibGlob _ _ _ _)
  | advances =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | retires =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | axiomCall => simp only [Stmt.istAxiom, Bool.true_eq_false] at ha
  | axiomCallElse => simp only [Stmt.istAxiom, Bool.true_eq_false] at ha
  | ret e hp => simp only [execStmt, reduceCtorEq] at h
  | retWhy r hp => simp only [execStmt, reduceCtorEq] at h
  | retScoped => simp only [execStmt, reduceCtorEq] at h
  | retWhyScoped => simp only [execStmt, reduceCtorEq] at h
  | leave hl => simp only [execStmt, reduceCtorEq] at h
  | next hl => simp only [execStmt, reduceCtorEq] at h
  | _ => simp only [Stmt.istBlatt, Bool.false_eq_true] at hb

theorem vorA_eq {A : AUmwelt D} {σ w : World D} {Λ : List (Res D)} {X : List (D.Tab ⊕ D.Glob)}
    (h : leseA A σ Λ X = w) : vorA A σ Λ X = ⟨w.slots, w.globs, σ.spur⟩ := by
  unfold vorA
  unfold leseA at h
  rw [h]

/-- **A leaf step keeps the replay** (as `fadenS_blatt`): its reads are recorded; a non-axiom
    leaf by leaf locality over the stable carriers AND the read list, an axiom call by recording
    its answer. -/
theorem fadenSA_blatt (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hFS : ∀ f, FussSX P S lok Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      semHA S O' U A passes R r σ ρ = weiterHA S O' U A passes R K (execStmtHA S O' U A passes R s σ ρ))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  have hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ := s.held_iff
  cases hax : s.istAxiom with
  | false =>
      refine fadenSA_lokalQ hF hr ρ' K σ'.spur (fun σ HX hfx hkx hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      have hXs := orte_stabilX (hFS _) (s.blatt_darf P hleaf) hs
      obtain ⟨HX', hfx', hkx', hsub, hrec⟩ :=
        lese_schritt Tg hfx hkx Λ (stmtOrteP P s) W.speicher
      have hgX := mischT_gleichAuf hg hXs Λ Λ
      have hĝ : GleichAuf (stabilS P S lok z.kopf.f Λ ++ stmtOrteP P s)
          (⟨(mischT Tg (stmtOrteP P s) (σ.lese Λ (stmtOrteP P s)) W.speicher).slots,
            (mischT Tg (stmtOrteP P s) (σ.lese Λ (stmtOrteP P s)) W.speicher).globs, σ.spur⟩ :
            World D) W := hgX
      obtain ⟨σs, hes, hgs, _⟩ := blatt_lokalV P O passes s hleaf hax
        (fun _ h => List.mem_append_right _ h) hĝ hstep
      have hl := blatt_lese_laenge P O passes keinRuf s hleaf hax (hes O keinRuf)
      refine ⟨σs, HX', hfx', kurzX_mono hkx' hl, hsub, Nat.le_trans (lese_laenge σ Λ _) hl,
        gleichAuf_stabil_iff hΛ' (GleichAuf.mono (fun _ h => List.mem_append_left _ h)
          ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩),
        hK, fun R O' U A hPX hHA _ => ?_⟩
      rw [hsem, execStmtHA_blatt P S O' U hHA passes R s hleaf, vorA_eq (hrec A hPX hHA), hes]
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
          refine fadenSA_ax hF hr ρ' K σ'.spur hΛ' a args
            (fun h' => orte_stabilX (hFS _) args.orte_darf (hok h').1) (fun h' => (hok h').2)
            (σ', (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a))
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr (fun _ => rfl)
            hlok
            (fun v hv => by
              rw [e1]
              exact hQ a _ _ v hv) ?_
          intro O' R U A σ0 κ hz hκ hw
          rw [hsem]
          apply ZErgG.folgt_of_eq
          simp only [execStmtHA, axiomAntwort, hκ, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp only [Stmt.istAxiom, Bool.false_eq_true] at hax

/-- **The acquire keeps the replay** (as `fadenS_locks`). -/
theorem fadenSA_locks {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hrL : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hrL body) rest) k⟩)
    (hinv : S.inv L W.speicher = true) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest k))⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  rw [hr] at hg hok
  simp only at hg hok
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  have hlen : σ.spur.length < ((mischU S L σ W.speicher).nimmt L).spur.length := by
    show σ.spur.length < (Ereignis.nimmt L _ :: σ.spur).length
    exact Nat.lt_succ_self _
  refine ⟨⟨H, HA, HU ++ [(L, σ, W.speicher)], HX, (mischU S L σ W.speicher).nimmt L, hreq, hf, hv, hm,
    kurzVBA_mono hk (Nat.le_of_lt hlen), hfa, hra, hqa, kurzAB_mono hka (Nat.le_of_lt hlen),
    funkU_append hfu (hku ⟨.gibt L⟩) _ (Nat.le_refl _), invU_append hiu L σ W.speicher hinv, ?_,
    ⟨hfx, kurzX_mono hkx (Nat.le_of_lt hlen)⟩, ?_, ⟨hks, hss, hrest⟩, ?_⟩, hS⟩
  · intro hN e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_trans (hku hN e he) hlen
    · rw [List.mem_singleton] at he
      subst he
      exact hlen
  · have key : ∀ c ∈ stabilS P S lok z.kopf.f (Res.held L :: Λ),
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
  · intro R O' U A hR hA hU hX hHA hQ
    have h1 := heq R O' U A hR hA (passtU_append hU) hX hHA hQ
    rw [hr] at h1
    simp only at h1
    refine ZErgG.folgt_trans h1 (ZErgG.folgt_of_eq ?_)
    rw [semHA_locks S O' U A passes R L hrL body rest k σ ρ,
      hU L σ W.speicher (List.mem_append_right _ List.mem_cons_self)]

end Schritte

end Gabbro.Grammatik
