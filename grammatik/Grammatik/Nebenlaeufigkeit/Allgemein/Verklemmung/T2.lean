/- Part 2 of 3 of `Verklemmung` (split by instrumente/teile/lean-teilen.py; the umbrella `Verklemmung.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T2Basis
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 3. At a `locks` head only another thread can stop the step -/

/-- Thread `t` stands at `locks L { … }`. -/
def AnSperre (M : RufMaschineG D) (t : Faden) (L : D.Lock) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (ρ : Env D Γ)
    (hr : ∀ K, Res.held K ∈ Λ → D.rang K < D.rang L)
    (body : Block D (vertragVon D (M.faeden t).kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩

section Folgen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **At a `locks L` head every lock the thread holds ranks below `L`**, and
    `L` is not held by the thread: `hself` and `hrang` of `dannLocks` hold
    on every reachable machine. -/
theorem sperre_rang {w : D.Fn} {M : RufMaschineG D} {t : Faden} (h : RangInvG w (M.faeden t))
    {L : D.Lock} (hA : AnSperre M t L) :
    L ∉ offen (M.faeden t).spur ∧ ∀ K ∈ offen (M.faeden t).spur, D.rang K < D.rang L := by
  obtain ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩ := hA
  have hk := rangKette_kopfK h.2.1
  have hR := (h.2.2.1 _ List.mem_cons_self).2
  rw [hhead] at hR
  simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hR
  have hU := bodenM_ueber hR.1.1.1
  have hlt : ∀ K ∈ offen (M.faeden t).spur, D.rang K < D.rang L := by
    intro K hK
    rcases hk K hK with h1 | ⟨c, hc, hlt⟩
    · rw [hhead] at h1
      exact hr K h1
    · have := hU c hc
      omega
  exact ⟨fun hL => by have := hlt L hL; omega, hlt⟩

/-- **The `locks` step fires as soon as no other thread holds the lock**:
    on every reachable machine, at a `locks L` head, `RufFreiG` is the only
    side condition that can fail. -/
theorem schritt_an_sperre {w : D.Fn} {M : RufMaschineG D} {t : Faden}
    (h : RangInvG w (M.faeden t)) {L : D.Lock} (hA : AnSperre M t L) (hfrei : RufFreiG M t L) :
    ∃ M', RufSchrittG P O passes M t M' := by
  obtain ⟨hself, hrang⟩ := sperre_rang h hA
  obtain ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩ := hA
  exact ⟨_, .dannLocks M t l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei⟩

end Folgen
/-! ## 4. No wait cycle -/

/-- A statement returns (a value or a reason). -/
def Stmt.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped _ R => R.scopes.isEmpty
  | .retWhyScoped _ R => R.scopes.isEmpty
  | _ => false

def Endblock.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped _ R => R.scopes.isEmpty
  | .retWhyScoped _ R => R.scopes.isEmpty
  | .cons s _ => s.istRueck
  | _ => false

def Block.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .cons s _ => s.istRueck
  | _ => false

/-- The residue stands at a return (the shapes a pop fires on). -/
def GRest.anRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende e => e.istRueck
  | .dann b _ => b.istRueck
  | _ => false

theorem Stmt.istRueck_perm {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : s.istRueck = true) : Λ.Perm V.ende := by
  cases s with
  | retScoped e R =>
      simp only [Stmt.istRueck, List.isEmpty_iff] at h
      have hg := R.genau
      rw [h] at hg
      simpa using hg
  | retWhyScoped r R =>
      simp only [Stmt.istRueck, List.isEmpty_iff] at h
      have hg := R.genau
      rw [h] at hg
      simpa using hg
  | _ => simp_all [Stmt.istRueck]

theorem GRest.anRueck_perm {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) (h : r.anRueck = true) : Λ.Perm V.ende := by
  cases r with
  | ende e =>
      cases e with
      | ret _ hp => exact hp
      | retWhy _ hp => exact hp
      | retScoped _ R =>
          simp only [anRueck, Endblock.istRueck, List.isEmpty_iff] at h
          have hg := R.genau
          rw [h] at hg
          simpa using hg
      | retWhyScoped _ R =>
          simp only [anRueck, Endblock.istRueck, List.isEmpty_iff] at h
          have hg := R.genau
          rw [h] at hg
          simpa using hg
      | cons s _ => exact s.istRueck_perm h
      | _ => simp only [anRueck, Endblock.istRueck, Bool.false_eq_true] at h
  | dann b _ =>
      cases b with
      | cons s _ => exact s.istRueck_perm h
      | _ => simp only [anRueck, Block.istRueck, Bool.false_eq_true] at h
  | _ => simp only [anRueck, Bool.false_eq_true] at h

/-- **Thread `t` is finished**: its stack is empty and its head stands at a
    return. -/
def FertigG (M : RufMaschineG D) (t : Faden) : Prop :=
  (M.faeden t).stapel = [] ∧ (M.faeden t).kopf.rest.2.2.2.2.anRueck = true

/-- **Thread `t` waits for a lock**: it stands at a `locks L` head, and
    every lock it stands at is held by another thread. -/
def WartetG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∃ L, AnSperre M t L) ∧ ∀ L, AnSperre M t L → ∃ u, u ≠ t ∧ L ∈ offen (M.faeden u).spur

/-- A finished thread whose start function holds no lock holds none. -/
theorem fertig_leer {M : RufMaschineG D} {t : Faden} {w : D.Fn} (h : RangInvG w (M.faeden t))
    (hw : D.haelt w = []) (hF : FertigG M t) : offen (M.faeden t).spur = [] := by
  obtain ⟨_, hk, _, hu⟩ := h
  obtain ⟨hst, hret⟩ := hF
  have hperm := GRest.anRueck_perm _ hret
  rw [hst] at hk
  have hkf : (M.faeden t).kopf.f = w := by
    rw [← hu]; unfold unten; rw [hst]; rfl
  refine List.eq_nil_iff_forall_not_mem.mpr fun K hK => ?_
  rcases hk K hK with h1 | h1
  · have := (held_ende _ K).mp (hperm.mem_iff.mp h1)
    have e : D.haelt (M.faeden t).kopf.f = [] := by rw [hkf]; exact hw
    change K ∈ D.haelt (M.faeden t).kopf.f at this
    rw [e] at this
    exact List.not_mem_nil this
  · exact h1

/-- A nonempty list of locks has one of maximal rank. -/
theorem rang_max : ∀ (ls : List D.Lock), ls ≠ [] → ∃ L ∈ ls, ∀ K ∈ ls, D.rang K ≤ D.rang L
  | [], h => absurd rfl h
  | [L], _ => ⟨L, List.mem_singleton_self L, fun K hK => by
      rw [List.mem_singleton.mp hK]; exact Int.le_refl _⟩
  | L :: L' :: rest, _ => by
      obtain ⟨M, hM, hmax⟩ := rang_max (L' :: rest) (List.cons_ne_nil _ _)
      by_cases hLM : D.rang M ≤ D.rang L
      · refine ⟨L, List.mem_cons_self, fun K hK => ?_⟩
        rcases List.mem_cons.mp hK with rfl | hK
        · exact Int.le_refl _
        · exact Int.le_trans (hmax K hK) hLM
      · refine ⟨M, List.mem_cons_of_mem _ hM, fun K hK => ?_⟩
        rcases List.mem_cons.mp hK with rfl | hK
        · omega
        · exact hmax K hK

section Verklemmung

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **NO DEADLOCK FROM LOCK RANKS.** On every reachable machine, if every
    unfinished thread waits for a lock another thread holds, then every
    thread is finished -- i.e. no reachable machine has an unfinished thread
    while all unfinished threads wait for locks. Premises: the declared
    floors hold on the bodies (`StufenM`), start functions hold no lock by
    signature (a finished thread then holds none), and the locks are
    finitely many (`ls`). The waited-for lock of a waiting thread ranks
    strictly below the lock its holder waits for (`sperre_rang`), so the
    waiting thread whose lock ranks highest waits for a lock held by a
    thread that waits for none higher -- a contradiction. -/
theorem keine_verklemmungG (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = []) (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hW : ∀ t, ¬ FertigG M t → WartetG M t) : ∀ t, FertigG M t := by
  have hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup := fun t => by
    rw [startSpur, hLeer t]; exact List.nodup_nil
  have hI := rangInvG_erreichbar hO hSt sp init hND hr
  intro t0
  refine Classical.byContradiction fun h0 => ?_
  let W := ls.filter fun L => @decide (∃ t, ¬ FertigG M t ∧ AnSperre M t L)
    (Classical.propDecidable _)
  have hWmem : ∀ L, L ∈ W ↔ ∃ t, ¬ FertigG M t ∧ AnSperre M t L := by
    intro L
    simp only [W, List.mem_filter, hls L, true_and]
    exact ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
      fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩
  obtain ⟨L0, hL0⟩ := (hW t0 h0).1
  have hne : W ≠ [] := fun he => by
    have := (hWmem L0).mpr ⟨t0, h0, hL0⟩
    rw [he] at this
    exact List.not_mem_nil this
  obtain ⟨Lm, hLm, hmax⟩ := rang_max W hne
  obtain ⟨tm, htm, hAm⟩ := (hWmem Lm).mp hLm
  obtain ⟨u, hu, hLu⟩ := (hW tm htm).2 Lm hAm
  by_cases hFu : FertigG M u
  · rw [fertig_leer (hI u) (hLeer u) hFu] at hLu
    exact List.not_mem_nil hLu
  · obtain ⟨Lu, hAu⟩ := (hW u hFu).1
    have hlt := (sperre_rang (hI u) hAu).2 Lm hLu
    have hle := hmax Lu ((hWmem Lu).mpr ⟨u, hFu, hAu⟩)
    omega

/-- The same, as "no reachable machine has all its unfinished threads
    waiting while one is unfinished". -/
theorem keine_verklemmungG' (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = []) (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ¬ ((∃ t, ¬ FertigG M t) ∧ ∀ t, ¬ FertigG M t → WartetG M t) :=
  fun ⟨⟨t, ht⟩, hW⟩ => ht (keine_verklemmungG hO hSt sp init hLeer ls hls hr hW t)

end Verklemmung
/-! ## 5. `StufenOk` gives the floors on the residues -/


end Gabbro.Grammatik
