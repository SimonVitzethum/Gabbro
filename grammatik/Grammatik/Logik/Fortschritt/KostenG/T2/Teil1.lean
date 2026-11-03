module

public import Grammatik.Logik.Fortschritt.KostenG.T2.Teil1a

public import Grammatik.Logik.Fortschritt.KostenG.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
  cases hs with
  | g7 hs =>
      cases hs with
      | rueckFreigabeLetzte _ _ _ _ z ha
      | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z ha
      | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z ha =>
          have he := rufAntwortG_stapel ha
          simp only [rufUpdateG_self] at hl
          rw [he] at hl
          rw [List.length_tail] at hl
          omega
      | _ => simp_all [rufUpdateG_self]
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;> simp_all [Eintritt, rufUpdateG_self]
      all_goals exact ⟨_, _, _, rfl, rfl⟩


/-! ## 8. The invariant and the engine -/

/-- The frames at and above the entry frame, each with an index `i` of the
    cost table `T i` it is costed at and of the admission `S i` its callees
    satisfy, and their total potential. -/
inductive Seg {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa : Nat) :
    List (RufRahmenG D) → Nat → Prop where
  | nil : Seg T S pa [] 0
  | cons (r : RufRahmenG D) (i : ι) (rs : List (RufRahmenG D)) (p : Nat)
      (hok : rufeR (S i) (fun _ => false) true r.rest.2.2.2.2 = true)
      (hb : RestScopeBalance r.rest) (h : Seg T S pa rs p) :
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
    (hok : rufeE (S i0) (fun _ => false) true (P.rumpf g) = true) :
    KInv T S pa (kostenEnd (T i0) pa (P.rumpf g)) f k M 0 := by
  obtain ⟨hk, hl⟩ := hE
  refine ⟨[], (M.faeden f).stapel, kostenEnd (T i0) pa (P.rumpf g) + 0, rfl, hl, ?_,
    by omega⟩
  rw [hk]
  exact Seg.cons _ i0 [] 0 hok (GRest.scopeChain_eintritt (P := P) _) Seg.nil

/-- **The engine step.** A step of any thread keeps the invariant as long
    as the frame is active: a foreign step changes nothing, an own step
    counts one and lowers the potential by at least one (`schrittArt`); the
    return of the entry frame itself still fits the budget. The two
    admission facts say that a callee admitted at index `i` has a body that
    fits the cost `T i g` counted for it, at the index `nx i g`, whose own
    callees are admitted there. -/
theorem kinv_schritt
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
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
    | cons _ i _ p hok hb hrest =>
      rcases schrittArt hs hb (T i) (S i) (fun _ => false) true with
        ⟨hst', hA⟩ | ⟨g', caller', rho, s0, hst', hk', hB'⟩ | ⟨caller, rst, hpop, hst', hC⟩
      · obtain ⟨hok', hpot⟩ := hA hok
        refine ⟨by omega, fun _ => ⟨oben, unten, _, by rw [hst', hst], hul,
          Seg.cons _ i oben p hok' ((rufSchrittG_scopeMove hs).same hst' hb) hrest, by omega⟩⟩
      · obtain ⟨hokc, hdir⟩ := hB' hok
        obtain ⟨hZ, hpot⟩ := hdir.resolve_right (fun ⟨_, hn, _⟩ => Bool.false_ne_true hn)
        have h1 := hS1 i g' hZ
        have h2 := hS2 i g' hZ
        refine ⟨by omega, fun _ => ⟨caller' :: oben, unten,
          kostenEnd (T (nx i g')) pa (P.rumpf g') + (potRest (T i) pa caller'.rest.2.2.2.2 + p),
          by rw [hst', hst]; rfl, hul, ?_, by omega⟩⟩
        rw [hk']
        exact Seg.cons _ (nx i g') _ _ h2 (GRest.scopeChain_eintritt (P := P) _)
          (Seg.cons _ i oben p hokc ((rufSchrittG_scopeMove hs).push caller' hst' hb) hrest)
      · have hpos := potRest_pos (T i) pa (M.faeden g).kopf.rest.2.2.2.2 (rufSchrittG_arbeitsfaehig hs)
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
          | cons _ j _ p' hokj hbj hrest' =>
            obtain ⟨hokc, hpotc⟩ := hC (T j) (S j) (fun _ => false) true
            refine ⟨oben', unten, _, hst', hul, Seg.cons _ j oben' p' (hokc hokj)
              ((rufSchrittG_scopeMove hs).pop caller rst (by rw [hst]; rfl) hst' hbj) hrest', ?_⟩
            omega
  · simp only [hgf, if_false, Nat.add_zero]
    have hEq : M'.faeden f = M.faeden f := rufSchrittG_fremd hs f (Ne.symm hgf)
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    refine ⟨by omega, fun _ => ⟨oben, unten, Φ, ?_, hul, ?_, hB⟩⟩
    · rw [hEq]; exact hst
    · rw [hEq]; exact hseg

end Motor
end Gabbro.Grammatik
