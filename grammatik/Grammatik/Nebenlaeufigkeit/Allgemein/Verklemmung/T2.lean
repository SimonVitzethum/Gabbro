/- Part 2 of 3 of `Verklemmung` (split by instrumente/teile/lean-teilen.py; the umbrella `Verklemmung.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **A push**: the callee's typing at the call site (`RufPasst`: its
    signature locks are named by the caller, every extra lock ranks below
    its floor, floors rise) gives the chain one frame higher. -/
theorem rangKette_push {o : List D.Lock} {F C G : RufRahmenG D} {S : List (RufRahmenG D)}
    {g : D.Fn} (h : RangKette o (fun _ => False) F S) (hCf : C.f = F.f) (hGf : G.f = g)
    (hGΛ : G.rest.2.2.1 = Signatur.anfang D (D.signatur g))
    (hCΛ : ∀ K, Res.held K ∈ F.rest.2.2.1 → Res.held K ∈ C.rest.2.2.1)
    (hp : RufPasst D (vertragVon D F.f) (D.signatur g) F.rest.2.2.1) :
    RangKette o (fun _ => False) G (C :: S) := by
  have hk0 := rangKette_kopfK h
  have ebG : bodenF G.f = (D.signatur g).boden := by rw [hGf]; rfl
  have ehG : D.haelt G.f = (D.signatur g).haelt := by rw [hGf]; rfl
  have ebC : bodenF C.f = bodenF F.f := congrArg bodenF hCf
  have ehC : D.haelt C.f = D.haelt F.f := congrArg D.haelt hCf
  have hb : BodenLe (bodenF F.f) (bodenF G.f) := by
    rw [ebG]; exact fun c hc => hp.hb c hc
  refine ⟨fun K hK => ?_, ?_, by rw [ebC]; exact hb, ?_⟩
  · rcases hk0 K hK with h1 | h1
    · by_cases hKg : K ∈ (D.signatur g).haelt
      · exact Or.inl (by rw [hGΛ]; exact (held_anfang _ K).mpr hKg)
      · obtain ⟨c, hc, hlt⟩ := hp.hx K h1 hKg
        exact Or.inr (Or.inl ⟨c, by rw [ebG]; exact hc, hlt⟩)
    · obtain ⟨c, hc, hlt⟩ := h1
      obtain ⟨c', hc', hle⟩ := hb c hc
      exact Or.inr (Or.inl ⟨c', hc', by omega⟩)
  · rw [ehG]
    exact fun L hL => hCΛ L (hp.hh L hL)
  · cases S with
    | nil =>
        intro K hK
        rcases h K hK with h1 | h1
        · exact Or.inl (hCΛ K h1)
        · exact h1.elim
    | cons c rest =>
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨fun K hK => ?_, by rw [ehC]; exact h2, by rw [ebC]; exact h3, by rw [ebC]; exact h4⟩
        rcases h1 K hK with h5 | h5 | h5
        · exact Or.inl (hCΛ K h5)
        · exact Or.inr (Or.inl (by rw [ebC]; exact h5))
        · exact h5.elim

/-- **A pop**: a frame at its end holdings names only its signature locks,
    which its caller names; a lock below its floor was held before the call
    (it is not at least the floor), so the caller names it or it is below
    the caller's floor. -/
theorem rangKette_pop {o : List D.Lock} {H caller N : RufRahmenG D} {rst : List (RufRahmenG D)}
    (h : RangKette o (fun _ => False) H (caller :: rst))
    (hperm : H.rest.2.2.1.Perm (vertragVon D H.f).ende)
    (hNf : N.f = caller.f) (hNΛ : N.rest.2.2.1 = caller.rest.2.2.1) :
    RangKette o (fun _ => False) N rst := by
  obtain ⟨h1, h2, _, h4⟩ := h
  have ebN : bodenF N.f = bodenF caller.f := congrArg bodenF hNf
  have ehN : D.haelt N.f = D.haelt caller.f := congrArg D.haelt hNf
  have hnamed : ∀ K, Res.held K ∈ H.rest.2.2.1 → Res.held K ∈ caller.rest.2.2.1 := fun K hK =>
    h2 K ((held_ende _ K).mp (hperm.mem_iff.mp hK))
  cases rst with
  | nil =>
      intro K hK
      rw [hNΛ]
      rcases h1 K hK with h5 | h5 | h5
      · exact Or.inl (hnamed K h5)
      · rcases h4 K hK with h6 | h6
        · exact Or.inl h6
        · exact (unter_ueber h5 h6).elim
      · exact h5.elim
  | cons c rest =>
      obtain ⟨g1, g2, g3, g4⟩ := h4
      refine ⟨fun K hK => ?_, by rw [ehN]; exact g2, by rw [ebN]; exact g3, by rw [ebN]; exact g4⟩
      rw [hNΛ, ebN]
      rcases h1 K hK with h5 | h5 | h5
      · exact Or.inl (hnamed K h5)
      · rcases g1 K hK with h6 | h6 | h6
        · exact Or.inl h6
        · exact Or.inr (Or.inl h6)
        · exact (unter_ueber h5 h6).elim
      · exact h5.elim

/-- The feature set of the floors: every `locks L` still ahead of a frame of
    `f` ranks at least `f`'s floor. -/
def bodenM (f : D.Fn) : Merkmal D :=
  ⟨fun _ => true, fun _ => true, fun L => match bodenF f with
    | none => true
    | some c => decide (c ≤ D.rang L)⟩

theorem bodenM_ueber {f : D.Fn} {L : D.Lock} (h : (bodenM f).sperre L = true) :
    UeberB (bodenF f) L := by
  intro c hc
  simp only [bodenM, hc, decide_eq_true_eq] at h
  exact h

/-- The floors of a program, read on its bodies (the residue form of
    `StufenOk`), decided per function. -/
def StufenM (P : Programm D) : Prop := ∀ f, mE (bodenM f) (P.rumpf f) = true

/-- The bottom frame's function. -/
def unten (z : RufFadenG D) : D.Fn := (z.stapel.getLast?.getD z.kopf).f

/-- **The rank invariant of a thread** whose start function is `w`. -/
def RangInvG (w : D.Fn) (z : RufFadenG D) : Prop :=
  (offen z.spur).Nodup ∧ RangKette (offen z.spur) (fun _ => False) z.kopf z.stapel ∧
  MerkInvG (fun _ => True) bodenM z ∧ unten z = w

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem rangInvG_schritt (hO : GutO O) (hSt : StufenM P) {w : D.Fn} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O passes M u M') (h : RangInvG w (M.faeden u)) :
    RangInvG w (M'.faeden u) := by
  obtain ⟨hnd, hk, hm, hu⟩ := h
  have hm' := merkInvG_schritt (fun f _ => ⟨hSt f, fun _ _ => trivial⟩) hs hm
  have hR := (hm _ List.mem_cons_self).2
  rcases schrittRang hO hs _ hR with
    ⟨hst, hf, ⟨ho, hΛ⟩ | ⟨L, hL, _, hsp, ho, hΛ⟩ | ⟨L, ho, hΛ⟩⟩ |
    ⟨g, c', hst, hcf, hgf, hgΛ, hcΛ, ho, hp⟩ | ⟨caller, rst, hpop, hst, hf, hΛ, ho, hperm⟩
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      exact rangKette_kopf hf hk (fun K hK => Or.inr ⟨hK, hΛ K⟩) (fun K hK => Or.inl hK)
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact List.nodup_cons.mpr ⟨hL, hnd⟩, ?_, hm', ?_⟩
    · rw [hst, ho]
      refine rangKette_kopf hf hk (fun K hK => ?_) (fun K hK => ?_)
      · rcases List.mem_cons.mp hK with rfl | hK
        · exact Or.inl (by rw [hΛ]; exact List.mem_cons_self)
        · exact Or.inr ⟨hK, fun h => by rw [hΛ]; exact List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp hK with rfl | hK
        · refine Or.inr fun G hG => ?_
          rcases List.mem_cons.mp hG with rfl | hG
          · exact bodenM_ueber hsp
          · exact ueberB_of_le (bodenM_ueber hsp) (rangKette_boden hk G hG)
        · exact Or.inl hK
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd.erase L, ?_, hm', ?_⟩
    · rw [hst, ho]
      refine rangKette_kopf hf hk (fun K hK => ?_) (fun K hK => Or.inl (List.mem_of_mem_erase hK))
      obtain ⟨hne, hK'⟩ := (List.Nodup.mem_erase_iff hnd).mp hK
      exact Or.inr ⟨hK', hΛ K hne⟩
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      exact rangKette_push hk hcf hgf hgΛ hcΛ hp
    · rw [← hu]; unfold unten; rw [hst, List.getLast?_cons]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hcf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      rw [hpop] at hk
      exact rangKette_pop hk hperm hf hΛ
    · rw [← hu]; unfold unten; rw [hst, hpop, List.getLast?_cons]
      cases rst.getLast? with
      | none => exact hf
      | some F => rfl

/-- **The rank invariant on every reachable machine**, given the floors on
    the bodies and duplicate-free start locks. -/
theorem rangInvG_erreichbar (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ t, RangInvG (init t).1 (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      refine ⟨hND t, fun K hK => Or.inl ((held_anfang _ K).mpr ((offen_startSpur _ K).mp hK)), ?_, rfl⟩
      intro F hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact ⟨trivial, hSt _⟩
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact rangInvG_schritt hO hSt hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv
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
  | _ => false

def Endblock.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
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
  cases s <;> simp_all [Stmt.istRueck]

theorem GRest.anRueck_perm {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) (h : r.anRueck = true) : Λ.Perm V.ende := by
  cases r with
  | ende e =>
      cases e with
      | ret _ hp => exact hp
      | retWhy _ hp => exact hp
      | cons s _ => exact s.istRueck_perm h
      | _ => simp [GRest.anRueck, Endblock.istRueck] at h
  | dann b _ =>
      cases b with
      | cons s _ => exact s.istRueck_perm h
      | _ => simp [GRest.anRueck, Block.istRueck] at h
  | _ => simp [GRest.anRueck] at h

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
