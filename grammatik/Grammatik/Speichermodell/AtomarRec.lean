/-
  File:      Grammatik/Speichermodell/AtomarRec.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 1: the record of atomic reads, the obligation
             over `execStmtHA`, the footprint property with shared atomics, and the replay
             invariant (`KopfSA` ... `ZielInvSA`) with its generic steps. Opus lane O25b,
             2026-09-26, OFFEN O25. Standalone: `Zielsatz/Spec.lean` does not import this file.

  THE IDEA. The replay of `ziel_ort_sperre` (SperreBeweis.lean) keeps, per frame, a SEQUENTIAL
  world `σ` that agrees with the machine on the frame's STABLE carriers, and records every answer
  the frame received from outside -- callee answers (`H`), axiom answers (`HA`), lock moves at an
  acquire (`HU`) -- keyed at a trace position no earlier record has, so that ONE handler, oracle
  and move repeat all of them. Here one record more: `HX`, the ATOMIC READS. At a read of a list
  `X` that contains shared atomics (the set `Tg`: atomic, unguarded, not local to the thread, and
  in no contract), the machine presented some values -- W's choice, any message the weak memory
  permits. The replay records (key = the sequential world after the read events, value = the
  presented memory); the atomic environment of the record (`umweltAusA`) answers the read with
  exactly those values at `X ∩ Tg` and changes nothing else, so it is in the class `HavocA Tg`
  the user's obligation `KoerperGutSA` covers. The key is fresh because the read events make the
  trace longer (a read of `[]` needs no record: the class forces the identity there).

  After the read the sequential world agrees with the machine's on the stable carriers AND on
  the whole read list (`mischT_gleichAuf`): what the step computes from the read is what the
  machine computes. Shared atomics are never stable (`Tg` is disjoint from `stabilS`), so the
  agreement the invariant keeps is unchanged: the sequential world may hold a stale value at a
  shared atomic between two reads, and no computation ever uses it.
-/
import Grammatik.Speichermodell.SperreSemA
import Grammatik.ZielOrtInv
import Grammatik.Speichermodell.MaschineW

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The obligation over `execStmtHA` (the part of `LogikPflichtA` below the goal file) -/

/-- **The body triple, caller duty and no `logik` outcome, against every atomic environment**
    over `T` (`KoerperGutS` with `execEndHA`). -/
def KoerperGutSA (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn) : Prop :=
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        (∀ (σ' : World D) (v : ErgVal D (D.erg f)),
          execEndHA (V := vertragVon D f) S O' U A passes R (P.rumpf f) σ ρ =
            EndAusgang.zurueck σ' v → EnsAmRueck P f σ σ' ρ v) ∧
        (∀ g : D.Fn,
          execEndHA (V := vertragVon D f) S O' U A passes (torRuf P R) (P.rumpf f) σ ρ ≠
            EndAusgang.logik (Logik.vorbedingung g))) ∧
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneLogik R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ e : Logik D, execEndHA (V := vertragVon D f) S O' U A passes R (P.rumpf f) σ ρ ≠
          EndAusgang.logik e)

/-- Owed invariants at a value return, against every atomic environment. -/
def InvGutSA (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ (σ' : World D) (v : ErgVal D (D.erg f)),
          execEndHA (V := vertragVon D f) S O' U A passes R (P.rumpf f) σ ρ =
            EndAusgang.zurueck σ' v → InvAmRueck P f σ'

/-- Owed invariants at a REASON return, against every atomic environment (the twin of
    `InvGutGrund`, Spec.lean). -/
def InvGutGrundA (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ (σ' : World D) (r : Fin (D.gruende f)),
          execEndHA (V := vertragVon D f) S O' U A passes R (P.rumpf f) σ ρ =
            EndAusgang.grund σ' r → InvAmRueck P f σ'

theorem invGutGrundA_mono {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {T T' : D.Tab ⊕ D.Glob → Prop} (hT : ∀ c, T c → T' c) {f : D.Fn}
    (h : InvGutGrundA P passes Q S T' f) : InvGutGrundA P passes Q S T f :=
  fun O' a b c U hU A hA => h O' a b c U hU A (havocA_mono hT hA)

/-- A bigger set of shared atomics is a stronger obligation. -/
theorem koerperGutSA_mono {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {T T' : D.Tab ⊕ D.Glob → Prop} (hT : ∀ c, T c → T' c) {f : D.Fn}
    (h : KoerperGutSA P passes Q S T' f) : KoerperGutSA P passes Q S T f :=
  ⟨fun O' a b c U hU A hA => h.1 O' a b c U hU A (havocA_mono hT hA),
    fun O' a b c U hU A hA => h.2 O' a b c U hU A (havocA_mono hT hA)⟩

theorem invGutSA_mono {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {T T' : D.Tab ⊕ D.Glob → Prop} (hT : ∀ c, T c → T' c) {f : D.Fn}
    (h : InvGutSA P passes Q S T' f) : InvGutSA P passes Q S T f :=
  fun O' a b c U hU A hA => h O' a b c U hU A (havocA_mono hT hA)

/-! ## 2. The record of atomic reads -/

/-- `σ` with the carriers of `X` that are in `T` taken from `s`. -/
noncomputable def mischT (T : D.Tab ⊕ D.Glob → Prop) (X : List (D.Tab ⊕ D.Glob)) (σ : World D)
    (s : Speicher D) : World D :=
  haveI := Classical.propDecidable
  ⟨fun t => if Sum.inl t ∈ X ∧ T (.inl t) then s.slots t else σ.slots t,
   fun g => if Sum.inr g ∈ X ∧ T (.inr g) then s.globs g else σ.globs g, σ.spur⟩

theorem mischT_spur (T : D.Tab ⊕ D.Glob → Prop) (X : List (D.Tab ⊕ D.Glob)) (σ : World D)
    (s : Speicher D) : (mischT T X σ s).spur = σ.spur := rfl

theorem mischT_innen {T : D.Tab ⊕ D.Glob → Prop} {X : List (D.Tab ⊕ D.Glob)} (σ : World D)
    (s : Speicher D) {c : D.Tab ⊕ D.Glob} (h : c ∈ X ∧ T c) :
    TraegerGleich (mischT T X σ s).speicher s c := by
  classical
  cases c with
  | inl t => exact if_pos h
  | inr g => exact if_pos h

theorem mischT_aussen {T : D.Tab ⊕ D.Glob → Prop} {X : List (D.Tab ⊕ D.Glob)} (σ : World D)
    (s : Speicher D) {c : D.Tab ⊕ D.Glob} (h : ¬ (c ∈ X ∧ T c)) :
    TraegerGleich (mischT T X σ s).speicher σ.speicher c := by
  classical
  cases c with
  | inl t => exact if_neg h
  | inr g => exact if_neg h

/-- A recorded atomic read: the key world (after the read events), the presented memory. -/
abbrev XEintrag (D : Deklaration) := World D × Speicher D

def FunkX (HX : List (XEintrag D)) : Prop :=
  ∀ (σ : World D) (s s' : Speicher D), (σ, s) ∈ HX → (σ, s') ∈ HX → s = s'

/-- Every key is at most `N` long (the NEXT key, after a non-empty read, is longer). -/
def KurzX (N : Nat) (HX : List (XEintrag D)) : Prop :=
  ∀ e ∈ HX, e.1.spur.length ≤ N

/-- The environment repeats the records. -/
def PasstX (T : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) (HX : List (XEintrag D)) : Prop :=
  ∀ (σ : World D) (s : Speicher D), (σ, s) ∈ HX → ∀ X, A X σ = mischT T X σ s

/-- The environment of a record: the recorded memory at a recorded key, nothing elsewhere. -/
noncomputable def umweltAusA (T : D.Tab ⊕ D.Glob → Prop) (HX : List (XEintrag D)) : AUmwelt D :=
  fun X σ =>
    haveI := Classical.propDecidable (∃ s : Speicher D, (σ, s) ∈ HX)
    if h : ∃ s : Speicher D, (σ, s) ∈ HX then mischT T X σ (Classical.choose h) else σ

theorem umweltAusA_passt (T : D.Tab ⊕ D.Glob → Prop) {HX : List (XEintrag D)} (hf : FunkX HX) :
    PasstX T (umweltAusA T HX) HX := by
  intro σ s hm X
  have hex : ∃ s : Speicher D, (σ, s) ∈ HX := ⟨s, hm⟩
  simp only [umweltAusA, dif_pos hex]
  rw [hf σ _ s (Classical.choose_spec hex) hm]

/-- **The environment of a record is in the class.** -/
theorem umweltAusA_ok (T : D.Tab ⊕ D.Glob → Prop) (HX : List (XEintrag D)) :
    HavocA T (umweltAusA T HX) := by
  intro X σ
  unfold umweltAusA
  split
  · exact ⟨rfl, fun c hc => mischT_aussen σ _ hc⟩
  · exact ⟨rfl, fun c _ => traegerGleich_refl _ c⟩

theorem funkX_nil : FunkX ([] : List (XEintrag D)) := fun _ _ _ h => absurd h List.not_mem_nil

theorem kurzX_nil (N : Nat) : KurzX N ([] : List (XEintrag D)) := fun _ h => absurd h List.not_mem_nil

theorem kurzX_mono {N N' : Nat} {HX : List (XEintrag D)} (h : KurzX N HX) (hN : N ≤ N') :
    KurzX N' HX := fun e he => Nat.le_trans (h e he) hN

theorem passtX_teil {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} {HX HX' : List (XEintrag D)}
    (hsub : ∀ e ∈ HX, e ∈ HX') (h : PasstX T A HX') : PasstX T A HX :=
  fun σ s hm => h σ s (hsub _ hm)

/-- A read of `[]` records no event. -/
theorem lese_nil (σ : World D) (Λ : List (Res D)) : σ.lese Λ [] = σ := by
  cases σ; rfl

/-- **ONE READ OF THE REPLAY.** At a read of `X` from the sequential world `σ` (records `HX`, all
    keys at most `σ`'s trace long), with the machine presenting the memory `s`: there are records
    `HX' ⊇ HX`, still functional and short for the world after the read, such that every
    environment in the class repeating them answers the read with `s` at `X ∩ T` and with `σ`'s
    own values everywhere else. -/
theorem lese_schritt (T : D.Tab ⊕ D.Glob → Prop) {HX : List (XEintrag D)} (hf : FunkX HX)
    {σ : World D} (hk : KurzX σ.spur.length HX) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob))
    (s : Speicher D) :
    ∃ HX' : List (XEintrag D), FunkX HX' ∧ KurzX (σ.lese Λ X).spur.length HX' ∧
      (∀ e ∈ HX, e ∈ HX') ∧
      ∀ A : AUmwelt D, PasstX T A HX' → HavocA T A → leseA A σ Λ X = mischT T X (σ.lese Λ X) s := by
  cases X with
  | nil =>
      refine ⟨HX, hf, ?_, fun _ h => h, fun A _ hA => ?_⟩
      · rw [lese_nil]; exact hk
      · unfold leseA
        rw [lese_nil]
        apply world_ext
        · intro c
          exact traegerGleich_trans ((hA [] σ).2 c fun ⟨h, _⟩ => absurd h List.not_mem_nil)
            (traegerGleich_symm (mischT_aussen σ s fun ⟨h, _⟩ => absurd h List.not_mem_nil))
        · exact (hA [] σ).1
  | cons x xs =>
      have hlt : σ.spur.length < (σ.lese Λ (x :: xs)).spur.length := by
        show σ.spur.length < (leseEv σ Λ (x :: xs) ++ σ.spur).length
        simp [leseEv]
        omega
      refine ⟨HX ++ [(σ.lese Λ (x :: xs), s)], ?_, ?_, fun e h => List.mem_append_left _ h,
        fun A hP _ => hP _ _ (List.mem_append_right _ List.mem_cons_self) _⟩
      · intro k s1 s2 h1 h2
        rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
        · exact hf k s1 s2 h1 h2
        · rw [List.mem_singleton] at h2
          cases h2
          have := hk _ h1
          simp only at this
          omega
        · rw [List.mem_singleton] at h1
          cases h1
          have := hk _ h2
          simp only at this
          omega
        · rw [List.mem_singleton] at h1 h2
          cases h1; cases h2; rfl
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact Nat.le_trans (hk e he) (Nat.le_of_lt hlt)
        · rw [List.mem_singleton] at he
          subst he
          exact Nat.le_refl _

/-- **After the read the sequential world agrees with the machine's on the read list** (and on
    whatever it agreed before): at `X ∩ T` it holds the presented values, elsewhere its own. -/
theorem mischT_gleichAuf {T : D.Tab ⊕ D.Glob → Prop} {L X : List (D.Tab ⊕ D.Glob)}
    {σ W : World D} (hg : GleichAuf L σ W) (hX : ∀ c ∈ X, c ∈ L ∨ T c) (Λ Λ' : List (Res D)) :
    GleichAuf (L ++ X) (mischT T X (σ.lese Λ X) W.speicher) (W.lese Λ' X) := by
  have key : ∀ c, c ∈ L ++ X → TraegerGleich (mischT T X (σ.lese Λ X) W.speicher).speicher
      (W.lese Λ' X).speicher c := by
    intro c hc
    by_cases h : c ∈ X ∧ T c
    · exact mischT_innen _ _ h
    · refine traegerGleich_trans (mischT_aussen _ _ h) ?_
      have hcL : c ∈ L := by
        rcases List.mem_append.mp hc with hc | hc
        · exact hc
        · rcases hX c hc with h' | h'
          · exact h'
          · exact absurd ⟨hc, h'⟩ h
      cases c with
      | inl t => exact hg.1 t hcL
      | inr g => exact hg.2 g hcL
  exact ⟨fun t ht => key (.inl t) ht, fun g hg' => key (.inr g) hg'⟩

/-- The old agreement survives the read (restriction of `mischT_gleichAuf`). -/
theorem mischT_gleichAuf_alt {T : D.Tab ⊕ D.Glob → Prop} {L X : List (D.Tab ⊕ D.Glob)}
    {σ W : World D} (hg : GleichAuf L σ W) (hX : ∀ c ∈ X, c ∈ L ∨ T c) (Λ Λ' : List (Res D)) :
    GleichAuf L (mischT T X (σ.lese Λ X) W.speicher) (W.lese Λ' X) :=
  GleichAuf.mono (fun _ h => List.mem_append_left _ h) (mischT_gleichAuf hg hX Λ Λ')

theorem mischT_laenge (T : D.Tab ⊕ D.Glob → Prop) (X : List (D.Tab ⊕ D.Glob)) (σ : World D)
    (Λ : List (Res D)) (s : Speicher D) :
    σ.spur.length ≤ (mischT T X (σ.lese Λ X) s).spur.length := lese_laenge σ Λ X

/-! ## 3. A leaf through the atomic environment -/

/-- The world a leaf starts from once its reads are answered: `A`'s memory, `σ`'s trace. -/
def vorA (A : AUmwelt D) (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) : World D :=
  ⟨(A X (σ.lese Λ X)).slots, (A X (σ.lese Λ X)).globs, σ.spur⟩

theorem vorA_lese {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A) (σ : World D)
    (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) : (vorA A σ Λ X).lese Λ X = leseA A σ Λ X := by
  unfold leseA
  apply world_ext (fun c => by cases c <;> rfl)
  rw [(hA X _).1]
  rfl

theorem vorA_nil {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A) (σ : World D)
    (Λ : List (Res D)) : vorA A σ Λ [] = σ := by
  have e : σ.lese Λ [] = σ := lese_nil σ Λ
  unfold vorA
  rw [e]
  exact world_ext (fun c => (hA [] σ).2 c fun ⟨h, _⟩ => absurd h List.not_mem_nil) rfl

/-- **A leaf of `execStmtHA` is a leaf of `execStmt` from the answered world.** -/
theorem execStmtHA_blatt (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (σ : World D) (ρ : Env D Γ) :
    execStmtHA S O U A passes R s σ ρ = execStmt O passes R s (vorA A σ Λ (stmtOrteP P s)) ρ := by
  cases s <;> first
    | (simp [Stmt.istBlatt] at hb; done)
    | (simp only [execStmtHA, execStmt, stmtOrteP, ← vorA_lese hA]; done)
    | (simp only [execStmtHA, execStmt, stmtOrteP, vorA_nil hA]; done)
    | (simp only [execStmtHA, execStmt, stmtOrteP, vorA_lese hA]; done)
    | (simp only [stmtOrteP]; unfold execStmtHA execStmt; rw [vorA_lese hA]; done)
    | (simp only [stmtOrteP]; unfold execStmtHA execStmt; rw [vorA_lese hA]; simp only [];
        generalize axiomAntwort _ _ _ _ = z; rcases z with ⟨_, _ | _⟩ <;> rfl)

end Gabbro.Grammatik
