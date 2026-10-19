/- Part 2 of 5 of `KostenG` (split by instrumente/teile/lean-teilen.py; the umbrella `KostenG.lean` imports all parts). -/
import Grammatik.Logik.Fortschritt.KostenG.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **One own step of the head: the potential argument, per rule of G.** -/
theorem schrittArt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O pa M f M') (c : D.Fn → Nat) (Z : D.Fn → Bool) :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (rufeR Z (M.faeden f).kopf.rest.2.2.2.2 = true →
        rufeR Z (M'.faeden f).kopf.rest.2.2.2.2 = true ∧
        potRest c pa (M'.faeden f).kopf.rest.2.2.2.2 + 1 ≤
          potRest c pa (M.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      (rufeR Z (M.faeden f).kopf.rest.2.2.2.2 = true →
        Z g = true ∧ rufeR Z caller'.rest.2.2.2.2 = true ∧
        potRest c pa caller'.rest.2.2.2.2 + 1 + c g ≤
          potRest c pa (M.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      ∀ (c' : D.Fn → Nat) (Z' : D.Fn → Bool),
        (rufeR Z' caller.rest.2.2.2.2 = true →
          rufeR Z' (M'.faeden f).kopf.rest.2.2.2.2 = true) ∧
        potRest c' pa (M'.faeden f).kopf.rest.2.2.2.2 ≤ potRest c' pa caller.rest.2.2.2.2) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead =>
    kopfA
    · simp_all
    · have := kostenStmt_pos c pa s; omega
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead =>
    kopfA
    · simp_all
    · have := kostenStmt_pos c pa s; omega
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    kopfA
    · simp_all
    · rw [entfZ_wahr hent]; omega
  | endeForm l Γ Λ e ρ hl hent hhead =>
    kopfA
    · cases e <;> try (simp [EndEntfaltbar] at hent; done)
      all_goals simp_all [rufeB_alsBlock, rufeR]
    · cases e <;> try (simp [EndEntfaltbar] at hent; done)
      all_goals (simp only [potRest, kostenBlock_alsBlock, kostenEnd, kostenSonst]; omega)
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw =>
    kopfA
    · have h := rufeB_armWahlG Z arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : rufeB Z b = true := h
      simp_all
    · have h := kostenBlock_armWahlG c pa arms (eval σ₁ v σ₁ ρ)
      rw [hw] at h
      have h2 : kostenBlock c pa b ≤ kostenArms c pa arms := h
      omega
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
    kopfA
    · have h := rufeB_armWahlG Z arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : rufeB Z b = true := h
      simp_all
    · have h := kostenBlock_armWahlG c pa arms (eval σ₁ v σ₁ ρ)
      rw [hw] at h
      have h2 : kostenBlock c pa b ≤ kostenArms c pa arms := h
      omega
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
    kopfA
    · have h := rufeB_grundWahlG Z arms (eval σ₁ r σ₁ ρ) hok.1.1
      rw [hw] at h
      simp_all
    · have h := kostenBlock_grundWahlG c pa arms (eval σ₁ r σ₁ ρ)
      rw [hw] at h
      omega
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    kopfA
    · simp_all
    · have h : @List.length (Wert D (.index (D.count t))) (alleIndizes (D.count t)) *
          (kostenBlock c pa body + kostenExpr inv + 2) ≤
          (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2) :=
        Nat.mul_le_mul_right _ (alleIndizes_length (D.count t))
      omega
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenEnd, kostenStmt, rufeR, rufeE, rufeS, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1, hok.2, by omega⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenBlock, kostenStmt, rufeR, rufeB, rufeS,
        Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1, ⟨hok.1.2, hok.2⟩, by omega⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1, ⟨hok.1.2, hok.2⟩, by omega⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1.1, ⟨⟨hok.1.1.2, hok.1.2⟩, hok.2⟩, by omega⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok
      dsimp only at hok
      simp only [rufeR, rufeB, rufeS, Bool.false_and, Bool.false_eq_true] at hok
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok
      dsimp only at hok
      simp only [rufeR, rufeE, rufeS, Bool.false_and, Bool.false_eq_true] at hok
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok
      dsimp only at hok
      simp only [rufeR, rufeB, Bool.false_and, Bool.false_eq_true] at hok
  | rueck caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | rueckCons caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potRest, rufeR, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potRest, rufeR, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potRest, rufeR, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; have := kostenBlock_pos c pa b; omega
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; have := kostenBlock_pos c pa b; omega
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa ueber
      have hm : max 1 (kostenBlock c pa ueber) = kostenBlock c pa ueber := Nat.max_eq_right this
      omega
  | _ =>
    kopfA
    · simp_all
    · omega
/-! ## 6. Counting one thread's steps -/

/- `RufErreichbarG` lives in `Prop`, so no function can count the steps of
    its derivations. `SegLauf` is the `Type`-valued twin: the same steps,
    made explicit, so `segZaehle` can count one thread's firings.
    `segLauf_erreichbar` forgets back, and `erreichbar_segLauf` is the
    converse (as a `Nonempty`): "any reachable run" and "any `SegLauf`"
    are the same runs. -/
inductive SegLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) : RufMaschineG D → Type where
  | start : SegLauf P O passes M0 M0
  | schritt (M M' : RufMaschineG D) (f : Faden)
      (h : SegLauf P O passes M0 M) (hs : RufSchrittG P O passes M f M') :
      SegLauf P O passes M0 M'

/-- Number of steps of thread `f` in an explicit run. Steps of other
    threads interleave freely and contribute nothing -- this is where
    scheduling delay drops out of the bound. -/
def segZaehle {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} : SegLauf P O passes M0 M → Faden → Nat
  | .start, _ => 0
  | .schritt _ _ g h' _, f => segZaehle h' f + (if g = f then 1 else 0)

/-- Every counted run is reachable. -/
theorem segLauf_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} (h : SegLauf P O passes M0 M) :
    RufErreichbarG P O passes M0 M := by
  induction h with
  | start => exact .start
  | schritt M M' f _ hs ih => exact .schritt M M' f ih hs

/-- Every reachable machine is the end of a counted run. -/
theorem erreichbar_segLauf {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} (h : RufErreichbarG P O passes M0 M) :
    Nonempty (SegLauf P O passes M0 M) := by
  induction h with
  | start => exact ⟨.start⟩
  | schritt M M' f _ hs ih => exact ⟨.schritt M M' f (Classical.choice ih) hs⟩

/-- The frame has not returned before the last step: before every step of
    the run, thread `f` still has at least `k` frames below its head. A
    frame entered with `k` frames below it returns exactly when that number
    drops under `k`, so the return, if the run contains it, is the LAST
    step. -/
def aktivVor {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 : RufMaschineG D} (f : Faden) (k : Nat) : {M : RufMaschineG D} →
    SegLauf P O passes M0 M → Prop
  | _, .start => True
  | _, .schritt (M := M) _ _ h' _ => aktivVor f k h' ∧ k ≤ (M.faeden f).stapel.length

/-! ## 7. Where frames begin -/

/-- The entry of a frame: thread `f`'s head is a fresh frame of `g`
    (parameters `rho`, entry world `s0`, residue the whole body), with `k`
    frames below it. Every frame of G begins so: the start frames
    (`eintritt_start`) and every pushed callee (`eintritt_push`). -/
def Eintritt (P : Programm D) (f : Faden) (g : D.Fn) (rho : Env D (D.params g))
    (s0 : World D) (k : Nat) (M : RufMaschineG D) : Prop :=
  (M.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
    rho, .ende (P.rumpf g)⟩⟩ ∧ (M.faeden f).stapel.length = k

/-- The start frames are entries (no frame below). -/
theorem eintritt_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (f : Faden) :
    Eintritt P f (init f).1 (init f).2 (sp.welt []) 0 (RufStartG P sp init) :=
  ⟨rfl, rfl⟩

/-- Every push enters a frame: after a step of `f` that grows `f`'s stack,
    `f`'s head is an entry with one more frame below it. -/
theorem eintritt_push {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M')
    (hl : (M.faeden f).stapel.length < (M'.faeden f).stapel.length) :
    ∃ (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D),
      Eintritt P f g rho s0 ((M.faeden f).stapel.length + 1) M' := by
  rcases schrittArt hs (fun _ => 0) (fun _ => true) with
    ⟨hst, _⟩ | ⟨g, caller', rho, s0, hst, hk, _⟩ | ⟨caller, rst, hpop, hst, _⟩
  · rw [hst] at hl; exact absurd hl (Nat.lt_irrefl _)
  · exact ⟨g, rho, s0, hk, by rw [hst]; rfl⟩
  · rw [hst, hpop] at hl; simp only [List.length_cons] at hl; omega

/-! ## 8. The invariant and the engine -/

/-- The frames at and above the entry frame, each with an index `i` of the
    cost table `T i` it is costed at and of the admission `S i` its callees
    satisfy, and their total potential. -/
inductive Seg {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa : Nat) :
    List (RufRahmenG D) → Nat → Prop where
  | nil : Seg T S pa [] 0
  | cons (r : RufRahmenG D) (i : ι) (rs : List (RufRahmenG D)) (p : Nat)
      (hok : rufeR (S i) r.rest.2.2.2.2 = true) (h : Seg T S pa rs p) :
      Seg T S pa (r :: rs) (potRest (T i) pa r.rest.2.2.2.2 + p)

/-- **The invariant**: thread `f` runs the segment `kopf :: oben` above the
    `k` frames below the entry frame, `n` own steps are counted, and counted
    plus remaining potential fit under the budget `B`. Frames below the
    entry frame belong to callers outside the segment and carry nothing. -/
def KInv {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa B : Nat) (f : Faden)
    (k : Nat) (M : RufMaschineG D) (n : Nat) : Prop :=
  ∃ (oben unten : List (RufRahmenG D)) (Φ : Nat),
    (M.faeden f).stapel = oben ++ unten ∧ unten.length = k ∧
    Seg T S pa ((M.faeden f).kopf :: oben) Φ ∧ n + Φ ≤ B

section Motor

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  (P : Programm D) (O : Orakel D) (pa : Nat)

/-- Entry establishes the invariant with nothing counted, at the budget of
    the body costed at the entry frame's table. -/
theorem kinv_eintritt {f : Faden} {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D}
    {k : Nat} {M : RufMaschineG D} (hE : Eintritt P f g rho s0 k M) (i0 : ι)
    (hok : rufeE (S i0) (P.rumpf g) = true) :
    KInv T S pa (kostenEnd (T i0) pa (P.rumpf g)) f k M 0 := by
  obtain ⟨hk, hl⟩ := hE
  refine ⟨[], (M.faeden f).stapel, kostenEnd (T i0) pa (P.rumpf g) + 0, rfl, hl, ?_,
    by omega⟩
  rw [hk]
  exact Seg.cons _ i0 [] 0 hok Seg.nil

/-- **The engine step.** A step of any thread keeps the invariant as long
    as the frame is active: a foreign step changes nothing, an own step
    counts one and lowers the potential by at least one (`schrittArt`); the
    return of the entry frame itself still fits the budget. The two
    admission facts say that a callee admitted at index `i` has a body that
    fits the cost `T i g` counted for it, at the index `nx i g`, whose own
    callees are admitted there. -/
theorem kinv_schritt
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {B : Nat} {f : Faden} {k : Nat} {M M' : RufMaschineG D} {n : Nat} {g : Faden}
    (hI : KInv T S pa B f k M n) (hs : RufSchrittG P O pa M g M') :
    n + (if g = f then 1 else 0) ≤ B ∧
    (k ≤ (M'.faeden f).stapel.length →
      KInv T S pa B f k M' (n + (if g = f then 1 else 0))) := by
  by_cases hgf : g = f
  · subst hgf
    simp only [if_true]
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    cases hseg with
    | cons _ i _ p hok hrest =>
      rcases schrittArt hs (T i) (S i) with
        ⟨hst', hA⟩ | ⟨g', caller', rho, s0, hst', hk', hB'⟩ | ⟨caller, rst, hpop, hst', hC⟩
      · obtain ⟨hok', hpot⟩ := hA hok
        refine ⟨by omega, fun _ => ⟨oben, unten, _, by rw [hst', hst], hul,
          Seg.cons _ i oben p hok' hrest, by omega⟩⟩
      · obtain ⟨hZ, hokc, hpot⟩ := hB' hok
        have h1 := hS1 i g' hZ
        have h2 := hS2 i g' hZ
        refine ⟨by omega, fun _ => ⟨caller' :: oben, unten,
          kostenEnd (T (nx i g')) pa (P.rumpf g') + (potRest (T i) pa caller'.rest.2.2.2.2 + p),
          by rw [hst', hst]; rfl, hul, ?_, by omega⟩⟩
        rw [hk']
        exact Seg.cons _ (nx i g') _ _ h2 (Seg.cons _ i oben p hokc hrest)
      · have hpos := potRest_pos (T i) pa (M.faeden g).kopf.rest.2.2.2.2
        refine ⟨by omega, fun hk => ?_⟩
        cases oben with
        | nil =>
          rw [hst', ← List.nil_append rst] at hk
          rw [hst, List.nil_append] at hpop
          rw [hpop] at hul
          simp only [List.length_cons] at hul
          simp only [List.nil_append] at hk
          omega
        | cons o oben' =>
          rw [hst] at hpop
          simp only [List.cons_append, List.cons.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          cases hrest with
          | cons _ j _ p' hokj hrest' =>
            obtain ⟨hokc, hpotc⟩ := hC (T j) (S j)
            refine ⟨oben', unten, _, hst', hul, Seg.cons _ j oben' p' (hokc hokj) hrest', ?_⟩
            omega
  · simp only [hgf, if_false, Nat.add_zero]
    have hEq : M'.faeden f = M.faeden f := rufSchrittG_fremd hs f (Ne.symm hgf)
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    refine ⟨by omega, fun _ => ⟨oben, unten, Φ, ?_, hul, ?_, hB⟩⟩
    · rw [hEq]; exact hst
    · rw [hEq]; exact hseg

/-- **The engine over a run.** From the entry invariant, along any run on
    which the frame stays active, the own steps never exceed the budget. -/
theorem kinv_lauf
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {B : Nat} {f : Faden} {k : Nat} {M1 : RufMaschineG D}
    (h0 : KInv T S pa B f k M1 0) :
    ∀ {M2 : RufMaschineG D} (run : SegLauf P O pa M1 M2), aktivVor f k run →
      segZaehle run f ≤ B ∧
      (k ≤ (M2.faeden f).stapel.length → KInv T S pa B f k M2 (segZaehle run f)) := by
  intro M2 run
  induction run with
  | start =>
    intro _
    refine ⟨?_, fun _ => h0⟩
    obtain ⟨_, _, _, _, _, _, hB⟩ := h0
    simp only [segZaehle]
    omega
  | schritt M M' g run' hs ih =>
    intro hA
    obtain ⟨hA', hk⟩ := hA
    have hI := (ih hA').2 hk
    exact kinv_schritt T S nx P O pa hS1 hS2 hI hs

/-- **The engine theorem**: a frame entered at index `i0` whose body names
    only callees admitted at `i0` takes at most `kostenEnd (T i0)` of its
    body own steps until (and including) its return. -/
theorem rahmen_schritte
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {f : Faden} {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D} {k : Nat}
    {M1 M2 : RufMaschineG D} (hE : Eintritt P f g rho s0 k M1) (i0 : ι)
    (hok : rufeE (S i0) (P.rumpf g) = true)
    (run : SegLauf P O pa M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenEnd (T i0) pa (P.rumpf g) :=
  (kinv_lauf T S nx P O pa hS1 hS2 (kinv_eintritt T S P pa hE i0 hok) run hA).1

end Motor
/-! ## 9. TARGET 1: the bound by call depth -/

/-- The cost of `g` with calls nested at most `n` deep: at depth `0` no
    callee is admitted (cost `0`, never used); at depth `n + 1` the body,
    each call counting its callee at depth `n`. -/
def kostenTief (P : Programm D) (pa : Nat) : Nat → D.Fn → Nat
  | 0, _ => 0
  | n + 1, g => kostenEnd (kostenTief P pa n) pa (P.rumpf g)

/-- The call-depth admission, as a Bool: at depth `n + 1` a function is
    admitted if every direct callee of its body is admitted at depth `n`
    and the body has no indirect call; at depth `0` none is. The same depth
    discipline as `TiefK`/`Tief` (RufUmkehrRufG.lean, RufAdaequatRufG.lean),
    over the WHOLE syntax instead of a fragment, and decidable. -/
def rufTief (P : Programm D) : Nat → D.Fn → Bool
  | 0, _ => false
  | n + 1, g => rufeE (rufTief P n) (P.rumpf g)

/-- **TARGET 1 -- `frame_schritte_beschraenkt`.** Let thread `f` enter a
    frame of `g` with `k` frames below it (`Eintritt`, as every start frame
    and every pushed callee does), and let `g` be admitted at call depth
    `n + 1` (`rufTief`: callees nested at most `n` deep, no indirect call).
    On ANY run from there on which the frame has not returned before the
    last step (`aktivVor`), thread `f` takes at most
    `kostenTief P passes (n + 1) g` steps -- the body's cost with each call
    counting its callee's cost one depth down, each `traverse` its body
    times `count`, each `retry n` its body `n` times, each `forever` its
    body `passes` times.

    Counted: firings of `RufSchrittG` by `f`, including the frame's return
    if the run ends with it. Not counted: other threads' steps, and time
    during which a step of `f` cannot fire (a `locks` whose lock another
    thread holds, an `awaits` whose payload is not visible) -- the
    SCHEDULER ASSUMPTION of the file header. -/
theorem frame_schritte_beschraenkt (P : Programm D) (O : Orakel D) (passes : Nat)
    (f : Faden) (g : D.Fn) (n : Nat) (hadm : rufTief P (n + 1) g = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenTief P passes (n + 1) g :=
  rahmen_schritte (kostenTief P passes) (rufTief P) (fun i _ => i - 1) P O passes
    (fun i h hS => by
      cases i with
      | zero => simp [rufTief] at hS
      | succ m => exact Nat.le_refl _)
    (fun i h hS => by
      cases i with
      | zero => simp [rufTief] at hS
      | succ m => exact hS)
    hE n hadm run hA

/-! ## 10. TARGET 2: the declared costs -/


