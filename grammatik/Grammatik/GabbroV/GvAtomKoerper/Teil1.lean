module
public import Grammatik.GabbroV.GvAtomKoerper.Teil1a

public import Grammatik.Zielsatz.Atomar.AtomarPflicht
public import Grammatik.Speichermodell.Atomar.AtomarSem
public import Grammatik.Speichermodell.Atomar.Invariants.AtomarRec
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
public import Grammatik.GabbroV.GvAtomRely
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik.GvAtomKoerper

open Gabbro.Grammatik.Zielsatz NIZeuge AtomarXZeuge

variable {D : Deklaration}

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
  simp only [mischT, h, and_self, ↓reduceIte]

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
  .ret .empty List.Perm.nil

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

end Gabbro.Grammatik.GvAtomKoerper
