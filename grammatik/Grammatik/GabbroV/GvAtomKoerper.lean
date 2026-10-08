/-
  File:      Grammatik/GabbroV/GvAtomKoerper.lean
  Subject:   GabbroV: atomic-bearing bodies whose rely duty follows from a
              per-body flag duty (agent 05, follow-up).

  Agent 1385's accepted obstruction (`gv_rely_braucht_atomfreiheit`): without
  atomic-freedom the transfer from the plain duty to the arbitrary-value duty
  FAILS (`hP`/`zaehlB`: sequential duty holds, rely duty fails at `aFuenf`).
  THIS FILE proves the next step: for bodies of the `hP` shape -- one store
  of a shared atomic into a slot, one flag test over it, both branches
  covered -- the duty over ARBITRARY atomic values (`KoerperGutSA`) follows
  from a duty the person states per body (pinned-memory runs, one per
  read site, with a case split over the test outcome).

  Design (all engines reused, nothing duplicated): `istFlagKoerper` is the
  decidable shape predicate; `flagKoerperLesen` computes every orte outside
  the two pinned reads; `pinA` answers those two reads from two fixed
  memories (in `HavocA T` by `mischT`); `FlagPersonenPflicht` is the
  person's duty over pinned runs; `flagKoerper_relyDuty` is the transfer.
-/
import Grammatik.Zielsatz.Atomar.AtomarPflicht
import Grammatik.Speichermodell.Atomar.AtomarSem
import Grammatik.Speichermodell.Atomar.AtomarRec
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
import Grammatik.GabbroV.GvAtomRely

namespace Gabbro.Grammatik.GvAtomKoerper

open Gabbro.Grammatik.Zielsatz NIZeuge AtomarXZeuge

variable {D : Deklaration}

/-- **The class, decidable**: store into a slot, test once, return -- and
    the test mentions the shared flag `g`. Everything else (which carriers
    the rest may read) is computed by `flagKoerperLesen` and discharged by
    one premise. -/
def istFlagKoerper (P : Programm D) (f : D.Fn) (g : D.Glob) (t : D.Tab) : Bool :=
  match P.rumpf f with
  | .cons sStore (.cons sTest _) =>
      match sStore, sTest with
      | .assignSlot t' _ _ _ _ _, .ite c _ _ =>
          decide (t' = t) && c.orte.any fun o => decide (o = .inr g)
      | _, _ => false
  | _ => false

/-- **Every orte outside the two pinned reads**, computed: the store index,
    both branches, the tail. The store source and the test condition are the
    pinned reads (`s₁`, `s₂`); everything here must avoid `T` (one premise).
    Off-shape bodies give `[]` (then `istFlagKoerper` is false anyway). -/
def flagKoerperLesen (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  match P.rumpf f with
  | .cons sStore (.cons sTest tail) =>
      match sStore, sTest with
      | .assignSlot _ _ idx _ _ _, .ite _ B₁ B₂ =>
          idx.orte ++ blockOrteP P B₁ ++ blockOrteP P B₂ ++ endblockOrteP P tail
      | _, _ => []
  | _ => []

/-! ## 2. The pinned havoc -/

/-- **Pinned havoc**: answer `X₁`-reads from `s₁`, `X₂`-reads from `s₂`,
    every other read unchanged. Non-adaptive (no dependence on history),
    hence statable by the person: two fixed memories, not an adversary.
    Noncomputable like `mischT` (its `Classical.propDecidable` for `T`). -/
noncomputable def pinA (T : D.Tab ⊕ D.Glob → Prop) (X₁ X₂ : List (D.Tab ⊕ D.Glob))
    (s₁ s₂ : Speicher D) : AUmwelt D :=
  fun X σ => if X = X₁ then mischT T X σ s₁ else if X = X₂ then mischT T X σ s₂ else σ

/-- The pinned havoc is in the class (both premises used: `mischT_spur`
    for the trace, `mischT_aussen` where nothing may change). -/
theorem pinA_havoc (T : D.Tab ⊕ D.Glob → Prop) (X₁ X₂ : List (D.Tab ⊕ D.Glob))
    (s₁ s₂ : Speicher D) : HavocA T (pinA T X₁ X₂ s₁ s₂) := by
  intro X σ
  unfold pinA
  by_cases h1 : X = X₁
  · rw [if_pos h1]
    exact ⟨mischT_spur _ _ _ _, fun c hc => mischT_aussen _ _ hc⟩
  · rw [if_neg h1]
    by_cases h2 : X = X₂
    · rw [if_pos h2]
      exact ⟨mischT_spur _ _ _ _, fun c hc => mischT_aussen _ _ hc⟩
    · rw [if_neg h2]
      exact ⟨rfl, fun c _ => traegerGleich_refl _ c⟩

/-! ## 3. Pinned reads agree with the havoc they pin -/

/-- At an `X₁`-read the pinned havoc answers what `A` answered (no
    `X₁ ≠ X₂` needed: the first branch wins regardless). Every premise is
    used: `hA` for `A`'s side, `hS` for the pinned memory. -/
theorem leseA_pinA_X₁ (T : D.Tab ⊕ D.Glob → Prop) (X₁ X₂ : List (D.Tab ⊕ D.Glob))
    (A : AUmwelt D) (hA : HavocA T A) (s₁ s₂ : Speicher D) (σ : World D)
    (Λ : List (Res D)) (hS : s₁ = (A X₁ (σ.lese Λ X₁)).speicher) :
    leseA (pinA T X₁ X₂ s₁ s₂) σ Λ X₁ = leseA A σ Λ X₁ := by
  classical
  have hAspur : (A X₁ (σ.lese Λ X₁)).spur = (σ.lese Λ X₁).spur :=
    (hA X₁ (σ.lese Λ X₁)).1
  have hAgle : ∀ c, ¬ (c ∈ X₁ ∧ T c) →
      TraegerGleich (A X₁ (σ.lese Λ X₁)).speicher ((σ.lese Λ X₁)).speicher c :=
    fun c hc => (hA X₁ (σ.lese Λ X₁)).2 c hc
  unfold leseA pinA
  rw [if_pos rfl, hS]
  apply world_ext _ _
  · intro c
    by_cases h : c ∈ X₁ ∧ T c
    · exact mischT_innen _ _ h
    · exact traegerGleich_trans (mischT_aussen _ _ h) (traegerGleich_symm (hAgle c h))
  · rw [mischT_spur, hAspur]

/-- At an `X₂`-read the pinned havoc answers what `A` answered -- here
    `X₂ ≠ X₁` is load-bearing (otherwise the `s₁` branch would win, and no
    single pin could match two answers at one read list). -/
theorem leseA_pinA_X₂ (T : D.Tab ⊕ D.Glob → Prop) (X₁ X₂ : List (D.Tab ⊕ D.Glob))
    (A : AUmwelt D) (hA : HavocA T A) (s₁ s₂ : Speicher D) (σ : World D)
    (Λ : List (Res D)) (hNe : X₂ ≠ X₁)
    (hS : s₂ = (A X₂ (σ.lese Λ X₂)).speicher) :
    leseA (pinA T X₁ X₂ s₁ s₂) σ Λ X₂ = leseA A σ Λ X₂ := by
  classical
  have hAspur : (A X₂ (σ.lese Λ X₂)).spur = (σ.lese Λ X₂).spur :=
    (hA X₂ (σ.lese Λ X₂)).1
  have hAgle : ∀ c, ¬ (c ∈ X₂ ∧ T c) →
      TraegerGleich (A X₂ (σ.lese Λ X₂)).speicher ((σ.lese Λ X₂)).speicher c :=
    fun c hc => (hA X₂ (σ.lese Λ X₂)).2 c hc
  unfold leseA pinA
  rw [if_neg hNe, if_pos rfl, hS]
  apply world_ext _ _
  · intro c
    by_cases h : c ∈ X₂ ∧ T c
    · exact mischT_innen _ _ h
    · exact traegerGleich_trans (mischT_aussen _ _ h) (traegerGleich_symm (hAgle c h))
  · rw [mischT_spur, hAspur]

/-! ## 4. The person's duty: pinned runs -/

/-- **The duty the person states per body**: the `KoerperGutSA` conclusions,
    but with the havoc ranging over pinned memories (`pinA`) instead of the
    adversary (`HavocA T`). Two fixed memories per entry state, no history
    dependence -- hence provable by a case split over the test outcome. -/
def FlagPersonenPflicht (P : Programm D) (Q : AxEns D) (S : SperrInv D)
    (T : D.Tab ⊕ D.Glob → Prop) (passes : Nat) (f : D.Fn)
    (X₁ X₂ : List (D.Tab ⊕ D.Glob)) : Prop :=
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ (s₁ s₂ : Speicher D),
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        (∀ (σ' : World D) (v : ErgVal D (D.erg f)),
          execEndHA (V := vertragVon D f) S O' U (pinA T X₁ X₂ s₁ s₂) passes R
            (P.rumpf f) σ ρ = EndAusgang.zurueck σ' v →
          EnsAmRueck P f σ σ' ρ v) ∧
        (∀ g : D.Fn,
          execEndHA (V := vertragVon D f) S O' U (pinA T X₁ X₂ s₁ s₂) passes (torRuf P R)
            (P.rumpf f) σ ρ ≠ EndAusgang.logik (Logik.vorbedingung g))) ∧
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ (s₁ s₂ : Speicher D),
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneLogik R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ e : Logik D,
          execEndHA (V := vertragVon D f) S O' U (pinA T X₁ X₂ s₁ s₂) passes R
            (P.rumpf f) σ ρ ≠ EndAusgang.logik e)

/-! ## 5. The run equality: adversary and pin take the same path -/

/-- **The `A`-run is the pinned run.** From the same entry state, every
    step agrees: the store and the test read through equal `leseA` worlds
    (`leseA_pinA_X₁/X₂` at the memories `A` itself showed), branches and
    tail run havoc-free on both sides (the sequential bridge
    `execHA_frei`). The handler `R'` stays schematic: the store never
    consults it. -/
theorem flagKoerper_run_gleich (P : Programm D) (S : SperrInv D)
    (T : D.Tab ⊕ D.Glob → Prop) (passes : Nat) (f : D.Fn)
    (O' : Orakel D) (hl : RegLokal O') (U : Umwelt D)
    (A : AUmwelt D) (hA : HavocA T A) (s₁ s₂ : Speicher D)
    (R' : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D (D.params f))
    {Λ₂ : List (Res D)}
    (sStore : Stmt D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (sTest : Stmt D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) Λ₂)
    (tail : Endblock D (vertragVon D f) false (D.params f) Λ₂)
    (t : D.Tab) (fld : D.Feld t)
    (idx : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (.index (D.count t)))
    (eSrc : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (D.typ t fld))
    (c : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool)
    (B₁ B₂ : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) Λ₂)
    (hShape : P.rumpf f = .cons sStore (.cons sTest tail))
    (hStore : ∃ (hw : (vertragVon D f).schreibt t = true)
      (hL : darf D t (Signatur.anfang D (D.signatur f))),
      sStore = .assignSlot t fld idx eSrc hw hL)
    (hTest : sTest = .ite c B₁ B₂)
    (hNe : c.orte ≠ idx.orte ++ eSrc.orte)
    (hS₁ : s₁ = (A (idx.orte ++ eSrc.orte)
      (σ.lese (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte))).speicher)
    (hFrei : ∀ o ∈ blockOrteP P B₁ ++ blockOrteP P B₂ ++ endblockOrteP P tail, ¬ T o) :
    ∀ (σ₁ : World D),
    execStmtHA S O' U A passes R' sStore σ ρ = .ok σ₁ ρ →
    (s₂ = (A c.orte (σ₁.lese (Signatur.anfang D (D.signatur f)) c.orte)).speicher) →
    execEndHA (V := vertragVon D f) S O' U A passes R' (P.rumpf f) σ ρ
      = execEndHA (V := vertragVon D f) S O' U
        (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂) passes R' (P.rumpf f) σ ρ := by
  obtain ⟨hw, hL, hStoreEq⟩ := hStore
  intro σ₁ hA1 hS₂
  -- the store reads agree
  have hW₁ : leseA (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂) σ
        (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte)
      = leseA A σ (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte) :=
    leseA_pinA_X₁ T _ _ A hA s₁ s₂ σ _ hS₁
  have hP1 : execStmtHA S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
        passes R' sStore σ ρ = .ok σ₁ ρ := by
    have hStep : execStmtHA S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
          passes R' sStore σ ρ
        = execStmtHA S O' U A passes R' sStore σ ρ := by
      rw [hStoreEq]
      simp only [execStmtHA]
      rw [hW₁]
    rw [hStep]
    exact hA1
  -- the test reads agree
  have hW₂ : leseA (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂) σ₁
        (Signatur.anfang D (D.signatur f)) c.orte
      = leseA A σ₁ (Signatur.anfang D (D.signatur f)) c.orte :=
    leseA_pinA_X₂ T _ _ A hA s₁ s₂ σ₁ _ hNe hS₂
  -- branches and tail agree through the sequential bridge
  have hmem : ∀ (l₁ l₂ l₃ : List (D.Tab ⊕ D.Glob)) (o : D.Tab ⊕ D.Glob),
      o ∈ l₁ ∨ o ∈ l₂ ∨ o ∈ l₃ → o ∈ l₁ ++ l₂ ++ l₃ := by
    intro l₁ l₂ l₃ o h
    simp only [List.mem_append] at h ⊢
    cases h with
    | inl h =>
        first | exact Or.inl (Or.inl h) | exact Or.inl h
    | inr h =>
        cases h with
        | inl h => first | exact Or.inl (Or.inr h) | exact Or.inr (Or.inl h)
        | inr h => first | exact Or.inr h | exact Or.inr (Or.inr h)
  have hB₁ : ∀ o ∈ blockOrteP P B₁, ¬ T o :=
    fun o h => hFrei o (hmem _ _ _ o (Or.inl h))
  have hB₂ : ∀ o ∈ blockOrteP P B₂, ¬ T o :=
    fun o h => hFrei o (hmem _ _ _ o (Or.inr (Or.inl h)))
  have hTl : ∀ o ∈ endblockOrteP P tail, ¬ T o :=
    fun o h => hFrei o (hmem _ _ _ o (Or.inr (Or.inr h)))
  have hBr₁ : ∀ σ₂ ρ₂, execBlockHA S O' U A passes R' B₁ σ₂ ρ₂
      = execBlockHA S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
          passes R' B₁ σ₂ ρ₂ := by
    intro σ₂ ρ₂
    rw [Block.execHA_frei P S O' U A passes R' hA hl.2 B₁ hB₁,
      Block.execHA_frei P S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
        passes R' (pinA_havoc T _ _ s₁ s₂) hl.2 B₁ hB₁]
  have hBr₂ : ∀ σ₂ ρ₂, execBlockHA S O' U A passes R' B₂ σ₂ ρ₂
      = execBlockHA S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
          passes R' B₂ σ₂ ρ₂ := by
    intro σ₂ ρ₂
    rw [Block.execHA_frei P S O' U A passes R' hA hl.2 B₂ hB₂,
      Block.execHA_frei P S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
        passes R' (pinA_havoc T _ _ s₁ s₂) hl.2 B₂ hB₂]
  have hTlEq : ∀ σ₂ ρ₂, execEndHA (V := vertragVon D f) S O' U A passes R' tail σ₂ ρ₂
      = execEndHA (V := vertragVon D f) S O' U
          (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂) passes R' tail σ₂ ρ₂ := by
    intro σ₂ ρ₂
    rw [Endblock.execHA_frei P S O' U A passes R' hA hl.2 tail hTl,
      Endblock.execHA_frei P S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
        passes R' (pinA_havoc T _ _ s₁ s₂) hl.2 tail hTl]
  have hStepTest : execStmtHA S O' U A passes R' sTest σ₁ ρ
      = execStmtHA S O' U (pinA T (idx.orte ++ eSrc.orte) c.orte s₁ s₂)
          passes R' sTest σ₁ ρ := by
    rw [hTest]
    simp only [execStmtHA, ← hW₂, hBr₁, hBr₂]
  rw [hShape]
  simp only [execEndHA, hA1, hP1, hStepTest, hTlEq]

/-! ## 6. The transfer: person's duty gives the rely duty -/

/-- **Person's duty gives the rely duty on flag bodies.** For every
    adversary `A`, the `A`-run is the pinned run at the memories `A`
    itself showed (`flagKoerper_run_gleich`), which the person's duty
    covers. Every premise is used. -/
theorem flagKoerper_relyDuty (P : Programm D) (S : SperrInv D) (Q : AxEns D)
    (T : D.Tab ⊕ D.Glob → Prop) (passes : Nat) (f : D.Fn)
    {Λ₂ : List (Res D)}
    (sStore : Stmt D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (sTest : Stmt D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) Λ₂)
    (tail : Endblock D (vertragVon D f) false (D.params f) Λ₂)
    (t : D.Tab) (fld : D.Feld t)
    (idx : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (.index (D.count t)))
    (eSrc : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (D.typ t fld))
    (c : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool)
    (B₁ B₂ : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) Λ₂)
    (hShape : P.rumpf f = .cons sStore (.cons sTest tail))
    (hStore : ∃ (hw : (vertragVon D f).schreibt t = true)
      (hL : darf D t (Signatur.anfang D (D.signatur f))),
      sStore = .assignSlot t fld idx eSrc hw hL)
    (hTest : sTest = .ite c B₁ B₂)
    (hNe : c.orte ≠ idx.orte ++ eSrc.orte)
    (hFrei : ∀ o ∈ blockOrteP P B₁ ++ blockOrteP P B₂ ++ endblockOrteP P tail, ¬ T o)
    (hPerson : FlagPersonenPflicht P Q S T passes f (idx.orte ++ eSrc.orte) c.orte) :
    KoerperGutSA P passes Q S T f := by
  refine ⟨fun O' hr hl hq U hU A hA R hR hV σ ρ hReq => ?_,
    fun O' hr hl hq U hU A hA R hR hOL σ ρ hReq => ?_⟩
  · have ⟨hw, hL, hStoreEq⟩ := hStore
    -- the store never consults the handler: one computation for every `R'`
    have hStoreR : ∀ R' : (∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
        execStmtHA S O' U A passes R' sStore σ ρ
        = execStmtHA S O' U A passes R sStore σ ρ := by
      intro R'
      rw [hStoreEq]
      simp only [execStmtHA]
    have hStoreOk : ∃ σ₁, execStmtHA S O' U A passes R sStore σ ρ = .ok σ₁ ρ := by
      rw [hStoreEq]
      simp only [execStmtHA]
      exact ⟨_, rfl⟩
    obtain ⟨σ₁, hA1⟩ := hStoreOk
    have hA1T : execStmtHA S O' U A passes (torRuf P R) sStore σ ρ = .ok σ₁ ρ := by
      rw [hStoreR]
      exact hA1
    have hRun := flagKoerper_run_gleich P S T passes f O' hl U A hA
      (A (idx.orte ++ eSrc.orte)
        (σ.lese (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte))).speicher
      (A c.orte (σ₁.lese (Signatur.anfang D (D.signatur f)) c.orte)).speicher
      R σ ρ sStore sTest tail t fld idx eSrc c B₁ B₂ hShape hStore hTest hNe rfl hFrei
      σ₁ hA1 rfl
    have hRunT := flagKoerper_run_gleich P S T passes f O' hl U A hA
      (A (idx.orte ++ eSrc.orte)
        (σ.lese (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte))).speicher
      (A c.orte (σ₁.lese (Signatur.anfang D (D.signatur f)) c.orte)).speicher
      (torRuf P R) σ ρ sStore sTest tail t fld idx eSrc c B₁ B₂ hShape hStore hTest hNe
      rfl hFrei σ₁ hA1T rfl
    have hP := hPerson
    unfold FlagPersonenPflicht at hP
    obtain ⟨hEns, hVbd⟩ := hP.1 O' hr hl hq U hU
      (A (idx.orte ++ eSrc.orte)
        (σ.lese (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte))).speicher
      (A c.orte (σ₁.lese (Signatur.anfang D (D.signatur f)) c.orte)).speicher
      R hR hV σ ρ hReq
    refine ⟨fun σ' v h => ?_, fun g h => ?_⟩
    · rw [hRun] at h
      exact hEns σ' v h
    · rw [hRunT] at h
      exact hVbd g h
  · have ⟨hw, hL, hStoreEq⟩ := hStore
    have hStoreOk : ∃ σ₁, execStmtHA S O' U A passes R sStore σ ρ = .ok σ₁ ρ := by
      rw [hStoreEq]
      simp only [execStmtHA]
      exact ⟨_, rfl⟩
    obtain ⟨σ₁, hA1⟩ := hStoreOk
    have hRun := flagKoerper_run_gleich P S T passes f O' hl U A hA
      (A (idx.orte ++ eSrc.orte)
        (σ.lese (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte))).speicher
      (A c.orte (σ₁.lese (Signatur.anfang D (D.signatur f)) c.orte)).speicher
      R σ ρ sStore sTest tail t fld idx eSrc c B₁ B₂ hShape hStore hTest hNe rfl hFrei
      σ₁ hA1 rfl
    have hP := hPerson
    unfold FlagPersonenPflicht at hP
    have hNoLog := hP.2 O' hr hl hq U hU
      (A (idx.orte ++ eSrc.orte)
        (σ.lese (Signatur.anfang D (D.signatur f)) (idx.orte ++ eSrc.orte))).speicher
      (A c.orte (σ₁.lese (Signatur.anfang D (D.signatur f)) c.orte)).speicher
      R hR hOL σ ρ hReq
    intro e h
    rw [hRun] at h
    exact hNoLog e h

/-! ## 7. Witness: the `hP` shape with both branches covered -/

/-- Projection inside: a pinned carrier reads the pinned memory. -/
theorem mischT_globs (T : D.Tab ⊕ D.Glob → Prop) (X : List (D.Tab ⊕ D.Glob))
    (w : World D) (s : Speicher D) (g : D.Glob)
    (h : Sum.inr g ∈ X ∧ T (.inr g)) :
    (mischT T X w s).globs g = s.globs g := by
  simp [mischT, h]

/-- Projection outside, applied: an unpinned slot reads the live world. -/
theorem mischT_slot_beiseite (T : D.Tab ⊕ D.Glob → Prop)
    (X : List (D.Tab ⊕ D.Glob)) (w : World D) (s : Speicher D)
    (t : D.Tab) (k : Int) (f : D.Feld t)
    (h : ¬ (Sum.inl t ∈ X ∧ T (.inl t))) :
    (mischT T X w s).slots t k f = w.slots t k f := by
  simp only [mischT, h, if_false]

open AtomarXZeuge in
/-- One covered branch: `tabB[0] = 1` (literal write, reads nothing). -/
def hZweigEins : Block nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .cons (hSetze 1 (by decide) (by decide)) .nil

open AtomarXZeuge in
/-- The tail: return with no value. -/
def hSchwanzLeer : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .ret .keine List.Perm.nil

open AtomarXZeuge in
/-- The `hP` body with BOTH branches writing `1`: the test outcome no
    longer decides the postcondition. -/
def hRumpfBeide : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons hLies (.cons (.ite hC hZweigEins hZweigEins) hSchwanzLeer)

open AtomarXZeuge in
/-- `hP` with the both-covered body (contracts unchanged). -/
def hPBeide : Programm nD :=
  ({ AtomarXZeuge.hP with rumpf := fun f => match f with
    | .zaehlB => hRumpfBeide
    | f => AtomarXZeuge.hP.rumpf f } : Programm nD)

/-- The both-covered body IS in the class (decided computation). -/
theorem hBeide_in_klasse :
    istFlagKoerper hPBeide NFn.zaehlB NGlob.konfig NTab.tabB = true := by
  rfl

/-- Its non-pinned orte are empty (literal writes only). -/
theorem hBeide_lesen_leer :
    flagKoerperLesen hPBeide NFn.zaehlB = [] := by
  rfl

/-- The branch/tail orte of the witness are empty. -/
theorem hBeide_frei_liste :
    blockOrteP hPBeide hZweigEins ++ blockOrteP hPBeide hZweigEins
      ++ endblockOrteP hPBeide hSchwanzLeer = [] := by
  rfl

open AtomarXZeuge in
/-- `konfig` is shared in the both-covered program (same call graph and
    footprints as `hP`: the two bodies read the same carriers). -/
theorem hPBeide_konfig_geteilt :
    GeteiltA hPBeide [NFn.kern, NFn.zaehlB] (.inr NGlob.konfig) := by
  refine ⟨⟨_, rfl, rfl⟩, ⟨(fun (L : nD.Lock) _ => nomatch L), fun h => ?_⟩⟩
  have := h NFn.zaehlB (List.mem_cons_of_mem _ List.mem_cons_self) NFn.kern List.mem_cons_self
    (Or.inl (fun e => by cases e)) NFn.zaehlB NFn.kern .wurzel (istIn_iff.mp (by decide)) .wurzel
  exact Bool.noConfusion this

/-- A table carrier is never atomically excepted (needs no program fact). -/
theorem tab_nicht_geteilt (P : Programm D) (ws : List D.Fn) (t : D.Tab)
    [DecidableEq D.Fn] :
    ¬ GeteiltA P ws (.inl t) := by
  intro h
  obtain ⟨g, hEq, _⟩ := h.1
  cases hEq

/-! ## 8. The person's proof on the witness: both outcomes give `1` -/

/-- Pinned store read answers `s₁`. -/
theorem hBeide_pin1 (s₁ s₂ : Speicher nD) (w : World nD) :
    pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂ [.inr NGlob.konfig] w
    = mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig] w s₁ := by
  unfold pinA
  rw [if_pos rfl]

/-- Pinned test read answers `s₂`. -/
theorem hBeide_pin2 (s₁ s₂ : Speicher nD) (w : World nD) :
    pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂ [.inr NGlob.konfig, .inl NTab.tabB] w
    = mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
        [.inr NGlob.konfig, .inl NTab.tabB] w s₂ := by
  unfold pinA
  rw [if_neg (by decide), if_pos rfl]

/-- Any other read (here: the empty one of `.keine`) is untouched. -/
theorem hBeide_pin0 (s₁ s₂ : Speicher nD) (w : World nD) :
    pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂ [] w = w := by
  unfold pinA
  rw [if_neg (by decide), if_neg (by decide)]

/-- `leseA` through the pin at the store read (fires on the folded form). -/
theorem hBeide_lese1 (s₁ s₂ : Speicher nD) (w : World nD) (Λ : List (Res nD)) :
    leseA (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) w Λ [.inr NGlob.konfig]
    = mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        (w.lese Λ [.inr NGlob.konfig]) s₁ := by
  unfold leseA
  rw [hBeide_pin1]

/-- `leseA` through the pin at the test read. -/
theorem hBeide_lese2 (s₁ s₂ : Speicher nD) (w : World nD) (Λ : List (Res nD)) :
    leseA (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) w Λ
      [.inr NGlob.konfig, .inl NTab.tabB]
    = mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
        [.inr NGlob.konfig, .inl NTab.tabB] (w.lese Λ [.inr NGlob.konfig, .inl NTab.tabB]) s₂ := by
  unfold leseA
  rw [hBeide_pin2]

/-- `leseA` through the pin off both reads is the plain read. -/
theorem hBeide_lese0 (s₁ s₂ : Speicher nD) (w : World nD) (Λ : List (Res nD)) :
    leseA (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) w Λ []
    = w.lese Λ [] := by
  unfold leseA
  rw [hBeide_pin0]

/-- The pinned store value: `s₁`'s `konfig`. -/
theorem hBeide_g1 (s₁ : Speicher nD) (w : World nD) :
    (mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig] w s₁).globs
      NGlob.konfig = s₁.globs NGlob.konfig :=
  mischT_globs _ _ w s₁ _ ⟨List.mem_cons_self, hPBeide_konfig_geteilt⟩

/-- The pinned test value: `s₂`'s `konfig`. -/
theorem hBeide_g2 (s₂ : Speicher nD) (w : World nD) :
    (mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
      [.inr NGlob.konfig, .inl NTab.tabB] w s₂).globs NGlob.konfig
    = s₂.globs NGlob.konfig :=
  mischT_globs _ _ w s₂ _ ⟨List.mem_cons_self, hPBeide_konfig_geteilt⟩

/-- The test's slot read sees the live world (`tabB` is never shared). -/
theorem hBeide_slot (s₂ : Speicher nD) (w : World nD) (k : Int) :
    (mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
      [.inr NGlob.konfig, .inl NTab.tabB] w s₂).slots NTab.tabB k ()
    = w.slots NTab.tabB k () := by
  apply mischT_slot_beiseite
  intro h
  exact tab_nicht_geteilt hPBeide _ NTab.tabB h.2

/-- The closed index reads `0` (at `tabB`, the witness's slot). -/
theorem hBeide_idx0 {Γ : Ctx} (w : World nD) (ρ : Env nD Γ) :
    (eval w (nI0 : Expr nD Γ [] (.index (nD.count NTab.tabB))) w ρ).n = 0 := by
  rfl

/-- Any closed `0` index reads `0` (unfolded form, schematic proofs). -/
theorem hBeide_idx0w {Γ : Ctx} (w : World nD) (ρ : Env nD Γ)
    (h1 : (0 : Int) ≤ 0) (h2 : (0 : Int) ≤ 0) :
    (eval w (Expr.weiter h1 h2 (Expr.lit 0 : Expr nD Γ [] (.int 0 0))) w ρ).n
      = 0 := by
  rfl

/-- The closed index reads nothing. -/
theorem hBeide_orte_nI0 :
    Expr.orte (nI0 : Expr nD [] [] (.index (nD.count NTab.tabB))) = [] := by
  rfl

/-- `eval` of a global read is the world's global (by definition;
    the access proof stays schematic, so this fires on every occurrence). -/
theorem hBeide_evalGlob {Γ : Ctx} (w : World nD) (ρ : Env nD Γ)
    (hg : gdarf nD NGlob.konfig []) :
    eval w (.glob NGlob.konfig hg) w ρ = w.globs NGlob.konfig := by
  rfl

/-- `eval` of the slot read (by definition; index and access proofs stay
    schematic, the index computes later). -/
theorem hBeide_evalSlot {Γ : Ctx} (w : World nD) (ρ : Env nD Γ)
    (i : Expr nD Γ [] (.index (nD.count NTab.tabB)))
    (hd : darf nD NTab.tabB []) :
    eval w (.slot NTab.tabB () i hd) w ρ
    = w.slots NTab.tabB (eval w i w ρ).n () := by
  rfl

/-- A plain read changes only the trace: slots stay. -/
theorem hBeide_lese_slots (w : World nD) (Λ : List (Res nD))
    (X : List (nD.Tab ⊕ nD.Glob)) (k : Int) :
    ((w.lese Λ X).slots NTab.tabB k ()) = w.slots NTab.tabB k () := by
  rfl

/-- Either branch writes literal `1` from any start world (it reads
    nothing shared, so even the kernel computes it). -/
theorem hZweigEins_eins (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (w₂ : World nD) (ρ : Env nD []) :
    ∃ σ₂, execBlockHA (V := vertragVon nD NFn.zaehlB) S O' U
      (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R hZweigEins w₂ ρ
      = .ok σ₂ ρ ∧ (σ₂.slots NTab.tabB 0 ()).n = 1 := by
  exact ⟨_, rfl, rfl⟩

/-- The tail returns, keeping `tabB[0]`. -/
theorem hSchwanz_behält (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ₂ : World nD) (ρ : Env nD []) :
    ∃ σ' v, execEndHA (V := vertragVon nD NFn.zaehlB) S O' U
      (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R hSchwanzLeer σ₂ ρ
      = .zurueck σ' v ∧ (σ'.slots NTab.tabB 0 ()).n = (σ₂.slots NTab.tabB 0 ()).n := by
  exact ⟨_, _, rfl, rfl⟩

/-- The stored value is `s₁`'s `konfig`. -/
theorem hBeide_stored_is_s1 (w₁ : World nD) (s₁ : Speicher nD) :
    ((w₁.schreibSlot NTab.tabB [] 0 () (s₁.globs NGlob.konfig)).slots
      NTab.tabB 0 ()) = s₁.globs NGlob.konfig := by
  simp only [World.schreibSlot, World.storeSlot, World.merke]
  rfl

/-- The program runs the both-covered body (by definition). -/
theorem hPBeide_rumpf : hPBeide.rumpf NFn.zaehlB = hRumpfBeide := by
  rfl

/-- Under every pinned run the body answers `tabB[0] = 1` (green version,
    restored verbatim from the pre-kill commit). -/
theorem hBeide_wert (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    tabBNach (execEndHA (V := vertragVon nD NFn.zaehlB) S O' U
    (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R
      (hPBeide.rumpf NFn.zaehlB) σ ρ) = 1 := by
  rw [hPBeide_rumpf]
  simp only [hRumpfBeide, hLies, hC, hZweigEins, hSetze, hSchwanzLeer, nI0, nW,
    execEndHA, execStmtHA, execBlockHA, Expr.orte, wahr?, eval,
    List.nil_append, List.cons_append, List.append_nil,
    hBeide_lese1, hBeide_lese2, hBeide_lese0,
    hBeide_idx0w, hBeide_g1, hBeide_g2, hBeide_slot]
  split <;> rename_i heq <;>
    (simp only [hBeide_lese0, ErgExpr.orte, tabBNach, hBeide_lese_slots]
     split at heq <;> cases heq <;> rfl)

/-- A `1` answer comes from a value return (all other outcomes read `-1`). -/
theorem tabBNach_zurueck {V : Vertrag nD} {l : Bool} {Γ : Ctx}
    (o : EndAusgang V l Γ) (h : tabBNach o = 1) : ∃ σ' v, o = .zurueck σ' v := by
  cases o with
  | zurueck σ' v => exact ⟨σ', v, rfl⟩
  | grund σ' r => simp only [tabBNach] at h; omega
  | leave h σ' ρ' => simp only [tabBNach] at h; omega
  | next h σ' ρ' => simp only [tabBNach] at h; omega
  | logik e => simp only [tabBNach] at h; omega
  | hardware e => simp only [tabBNach] at h; omega

/-- Every pinned run returns (from the `= 1` fact). -/
theorem hBeide_zurueck (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    ∃ σ' v, execEndHA (V := vertragVon nD NFn.zaehlB) S O' U
      (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R
      (hPBeide.rumpf NFn.zaehlB) σ ρ
      = .zurueck σ' v :=
  tabBNach_zurueck _ (hBeide_wert S O' U s₁ s₂ passes R σ ρ)

/-- **The person's duty holds on the witness**: every pinned run answers
    `1` (both outcomes), always returns, and never hits `.logik`. -/
theorem hBeide_personenPflicht (passes : Nat) :
    FlagPersonenPflicht hPBeide (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) passes NFn.zaehlB
      [.inr NGlob.konfig] [.inr NGlob.konfig, .inl NTab.tabB] := by
  refine ⟨fun O' _ _ _ U _ s₁ s₂ R _ _ σ ρ _ => ⟨fun σ' v h => ?_, fun g h => ?_⟩,
    fun O' _ _ _ U _ s₁ s₂ R _ _ σ ρ _ e h => ?_⟩
  · have h1 := hBeide_wert SchwachZeuge.nS O' U s₁ s₂ passes R σ ρ
    rw [h] at h1
    simp only [tabBNach] at h1
    show decide ((σ'.slots NTab.tabB 0 ()).n = 1) = true
    exact decide_eq_true h1
  · obtain ⟨σ', v, h'⟩ := hBeide_zurueck SchwachZeuge.nS O' U s₁ s₂ passes
      (torRuf hPBeide R) σ ρ
    rw [h'] at h
    cases h
  · obtain ⟨σ', v, h'⟩ := hBeide_zurueck SchwachZeuge.nS O' U s₁ s₂ passes R σ ρ
    rw [h'] at h
    cases h

/-- The witness body has the flag shape (by definition). -/
theorem hBeide_shape :
    hPBeide.rumpf NFn.zaehlB
      = .cons hLies (.cons (.ite hC hZweigEins hZweigEins) hSchwanzLeer) := by
  rfl

/-- The witness store source, named once so every occurrence matches
    syntactically (the transfer, the store fact and the read lists share
    this exact term). -/
def eSrcWitness : Expr nD (nD.params NFn.zaehlB)
    (Signatur.anfang nD (nD.signatur NFn.zaehlB)) (nD.typ NTab.tabB ()) :=
  (.glob NGlob.konfig (nGd _ _))

/-- The witness store is the shared-flag store. -/
theorem hBeide_store :
    ∃ (hw : (vertragVon nD NFn.zaehlB).schreibt NTab.tabB = true)
      (hL : darf nD NTab.tabB (Signatur.anfang nD (nD.signatur NFn.zaehlB))),
      hLies = .assignSlot NTab.tabB () nI0 eSrcWitness hw hL := by
  exact ⟨rfl, nDarf _ _, rfl⟩

/-- The non-pinned witness reads avoid the shared set (vacuous: none). -/
theorem hBeide_frei :
    ∀ o ∈ blockOrteP hPBeide hZweigEins ++ blockOrteP hPBeide hZweigEins
      ++ endblockOrteP hPBeide hSchwanzLeer,
      ¬ GeteiltA hPBeide [NFn.kern, NFn.zaehlB] o := by
  rw [hBeide_frei_liste]
  intro o h
  simp only [List.mem_nil_iff] at h

/-- **The transfer fires on the witness**: the both-covered `hP` shape
    meets its contract against every atomic environment. -/
theorem hBeide_relyDuty (passes : Nat) :
    KoerperGutSA hPBeide passes (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) NFn.zaehlB :=
  flagKoerper_relyDuty hPBeide SchwachZeuge.nS (axWahr nD)
    (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) passes NFn.zaehlB
    hLies (.ite hC hZweigEins hZweigEins) hSchwanzLeer
    NTab.tabB () nI0 eSrcWitness hC hZweigEins hZweigEins
    hBeide_shape hBeide_store rfl (by decide) hBeide_frei
    (hBeide_personenPflicht passes)

/-- Owed invariants at a value return: vacuous (`nD` declares none). -/
theorem hBeide_invGutSA (passes : Nat) :
    InvGutSA hPBeide passes (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) NFn.zaehlB := by
  intro O' hr hl hq U hU A hA R hR hV σ ρ hReq σ' v he
  intro i hi _
  cases hi

/-- Owed invariants at a reason return: vacuous likewise. -/
theorem hBeide_invGutGrundA (passes : Nat) :
    InvGutGrundA hPBeide passes (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) NFn.zaehlB := by
  intro O' hr hl hq U hU A hA R hR hV σ ρ hReq σ' r he
  intro i hi _
  cases hi

/-- **The full rely duty on the witness**: body triple (both branches
    covered) plus the vacuous invariant duties. -/
theorem hBeide_relyDuty_voll (passes : Nat) :
    Gabbro.Grammatik.X86.GvAtomRely.GvRelyDuty hPBeide SchwachZeuge.nS (axWahr nD)
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) passes NFn.zaehlB :=
  ⟨hBeide_relyDuty passes, hBeide_invGutSA passes, hBeide_invGutGrundA passes⟩

/-! ## 9. Planted body outside the class -/

open AtomarXZeuge in
/-- Planted body: the same flag test, but with NO pinning store (the test
    reads the live shared value directly). A real body that runs -- just
    not in the class: there is no pinned read to case-split on. -/
def hRumpfFalsch : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons (.ite hC hZweigEins hZweigEins) hSchwanzLeer

open AtomarXZeuge in
/-- The planted program (contracts unchanged). -/
def hPFalsch : Programm nD :=
  ({ AtomarXZeuge.hP with rumpf := fun f => match f with
    | .zaehlB => hRumpfFalsch
    | f => AtomarXZeuge.hP.rumpf f } : Programm nD)

/-- The predicate rejects it, by deciding the computation. -/
theorem hFalsch_abgelehnt :
    istFlagKoerper hPFalsch NFn.zaehlB NGlob.konfig NTab.tabB = false := by
  rfl

/- CUTS: what is not proved or not covered.
    PROVED here: `istFlagKoerper`, `flagKoerperLesen`, `pinA` (+ `pinA_havoc`),
    `leseA_pinA_X₁/X₂`, `FlagPersonenPflicht`, `flagKoerper_run_gleich`,
    `flagKoerper_relyDuty` (the transfer for `KoerperGutSA`); the witness
    (`hRumpfBeide`, `hPBeide`, class/decide facts, `GeteiltA` facts,
    pinned-run values, `hBeide_personenPflicht`, `hBeide_relyDuty`,
    `hBeide_invGutSA/GrundA`, full `hBeide_relyDuty_voll`).
    NOT proved / not covered:
    * heterogeneous (non-uniform) chains: not this file's subject;
      see `GvSplits.lean`.
    * invariant duties beyond invariant-free programs: the witness's
      `InvGutSA/GrundA` hold vacuously (`nD.invs = []`); programs WITH
      table invariants need per-invariant coverage in the person's duty.
    * no tactic integration: nothing here changes `gabbro_calls` or
      `programmlogik/`; these are the sound proof rules such integration
      would invoke.
    * the planted rejection is PROVED (`hFalsch_abgelehnt`: a flag test
      with no pinning store is rejected by `decide`). -/
#print axioms Gabbro.Grammatik.GvAtomKoerper.istFlagKoerper
#print axioms Gabbro.Grammatik.GvAtomKoerper.flagKoerperLesen
#print axioms Gabbro.Grammatik.GvAtomKoerper.pinA
#print axioms Gabbro.Grammatik.GvAtomKoerper.pinA_havoc
#print axioms Gabbro.Grammatik.GvAtomKoerper.leseA_pinA_X₁
#print axioms Gabbro.Grammatik.GvAtomKoerper.leseA_pinA_X₂
#print axioms Gabbro.Grammatik.GvAtomKoerper.FlagPersonenPflicht
#print axioms Gabbro.Grammatik.GvAtomKoerper.flagKoerper_run_gleich
#print axioms Gabbro.Grammatik.GvAtomKoerper.flagKoerper_relyDuty
#print axioms Gabbro.Grammatik.GvAtomKoerper.hRumpfBeide
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPBeide
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_in_klasse
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lesen_leer
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPBeide_konfig_geteilt
#print axioms Gabbro.Grammatik.GvAtomKoerper.tab_nicht_geteilt
#print axioms Gabbro.Grammatik.GvAtomKoerper.mischT_globs
#print axioms Gabbro.Grammatik.GvAtomKoerper.mischT_slot_beiseite
#print axioms Gabbro.Grammatik.GvAtomKoerper.hZweigEins
#print axioms Gabbro.Grammatik.GvAtomKoerper.hSchwanzLeer
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_frei_liste
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_pin1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_pin2
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_pin0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese2
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_g1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_g2
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_slot
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_idx0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_idx0w
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_orte_nI0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese_slots
#print axioms Gabbro.Grammatik.GvAtomKoerper.hZweigEins_eins
#print axioms Gabbro.Grammatik.GvAtomKoerper.hSchwanz_behält
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_stored_is_s1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_evalGlob
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_evalSlot
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_wert
#print axioms Gabbro.Grammatik.GvAtomKoerper.tabBNach_zurueck
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_zurueck
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPBeide_rumpf
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_personenPflicht
#print axioms Gabbro.Grammatik.GvAtomKoerper.eSrcWitness
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_shape
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_store
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_frei
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_relyDuty
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_invGutSA
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_invGutGrundA
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_relyDuty_voll
#print axioms Gabbro.Grammatik.GvAtomKoerper.hRumpfFalsch
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPFalsch
#print axioms Gabbro.Grammatik.GvAtomKoerper.hFalsch_abgelehnt

end Gabbro.Grammatik.GvAtomKoerper
