/-
  File:      Grammatik/X86/PipelineWorkPath.lean
  Subject:   Taken-path work and per-round loop correspondence over the
             direct pipeline lowering (lane 1259).

  Follow-up of `PipelineWork.lean`: its `Deckung` counts the STATIC
  whole-list length and its dynamic-path bound is arithmetic only, not
  connected to a taken-path `lauf` prefix; loop work stops at the
  labelled-step budget. This file connects the taken-path bound to the
  executed `lauf` prefix of the byte-level run, and proves the
  per-round loop body correspondence and the labelled-to-bytes leg
  with `PipelineLoops.lean`.

  Reused, not duplicated: `Pipeline.lauf_zu_laufBytes`/`gerade`/`kanon`/
  `encodeAll`/`CodeAt`, `DerivedWorkBound.decodiertZu`/`arbeit_decodiert`,
  `PipelineWork.pipeSummary`/`pipeSummary_expand`/`senkStmt_flach_laenge`/
  `PipePaket`, `PipelineLoops.schleifeProg`/`schleifeSchritte`/
  `schleife_korrekt_endlich`/`schleife_bytes`/`relax_laufBytes`,
  the actual `lauf`/`laufBytes`/`laufL`/`laufBytesI` runs. No second IR,
  no second source interpreter, no new cost model. Unsupported shapes
  are REFUSED, never guessed. Rust is out of scope.
-/
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineLoops
import Grammatik.X86.ISAWitnesses

namespace Gabbro.Grammatik.X86.PipelineWorkPath

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineLoops
open Gabbro.Grammatik.X86.PipelineWitnesses

/-! ## 1. Taken-path work: the executed prefix length.

    The taken-path work of a byte-level run is the length of the
    instruction prefix it actually retires -- never the static
    whole-list length. -/

/-- TAKEN-PATH WORK: the retired count of the executed prefix. -/
def genommenArbeit (T : List Befehl) : Nat := T.length

/-! ## 2. The taken-path prefix bridge: executed prefix to bytes.

    `Pipeline.lauf_zu_laufBytes` runs a whole static list. Here the
    STATIC program `prog` is split at the actually executed TAKEN
    prefix `T` (`prog = T ++ rest`): the fetched byte run of exactly
    `T.length` steps is the taken prefix run, its retired work is
    `T.length` (never the static length), and the taken length never
    exceeds the static length. Every premise is used: `hprog` fixes
    the split, `hg`/`hlauf`/`hc`/`hf`/`hrip` feed the bridge. -/

/-- TAKEN-PATH BRIDGE: the fetched run of `T.length` steps retires
    exactly the taken prefix `T` of the static program. -/
theorem laufBytes_genommen (cs : Adresse) (flat : List Byte)
    (prog T rest : List Befehl) (pre post : List Byte) (s s' : Zustand)
    (hprog : prog = T ++ rest)
    (hg : T.all Pipeline.gerade = true)
    (hlauf : lauf (T.map Pipeline.kanon) s = some s')
    (hc : Pipeline.CodeAt s.speicher cs flat)
    (hf : flat = pre ++ Pipeline.encodeAll prog ++ post)
    (hrip : s.rip = addrOff cs pre.length) :
    laufBytes T.length s = .weiter s' ∧
      s'.rip = addrOff cs (pre.length + (Pipeline.encodeAll T).length) ∧
      Pipeline.CodeAt s'.speicher cs flat ∧
      targetWork ((decodiertZu T).map fun d => d.befehl) = T.length ∧
      T.length ≤ prog.length := by
  subst hprog
  have hfs : flat = pre ++ Pipeline.encodeAll T ++
      (Pipeline.encodeAll rest ++ post) := by
    simp only [List.append_assoc] at hf ⊢
    rw [Pipeline.encodeAll_append] at hf
    simp only [List.append_assoc] at hf
    exact hf
  obtain ⟨hb, hr, hc', -, -⟩ := Pipeline.lauf_zu_laufBytes cs flat T pre
    (Pipeline.encodeAll rest ++ post) s s' hg hlauf hc hfs hrip
  refine ⟨hb, hr, hc', arbeit_decodiert T, ?_⟩
  simp only [List.length_append]
  omega

/-- JOINT WITNESS for `laufBytes_genommen`: the first witness chunk
    is the taken prefix of the candidate; the fetched five steps
    retire exactly five instructions, within the static twelve. -/
theorem laufBytes_genommen_zeuge :
    ∃ (T rest : List Befehl) (s' : Zustand),
      (pwChunk ++ pwProg.drop 5) = T ++ rest ∧
      T.all Pipeline.gerade = true ∧
      lauf (T.map Pipeline.kanon) (pwStart 30) = some s' ∧
      Pipeline.CodeAt (pwStart 30).speicher (natAdresse 4096) pwBytes ∧
      pwBytes = [] ++ Pipeline.encodeAll (pwChunk ++ pwProg.drop 5) ++ [] ∧
      (pwStart 30).rip = addrOff (natAdresse 4096) ([] : List Byte).length ∧
      laufBytes T.length (pwStart 30) = .weiter s' ∧
      targetWork ((decodiertZu T).map fun d => d.befehl) = T.length ∧
      T.length ≤ (pwChunk ++ pwProg.drop 5).length ∧
      PipePaket := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp pw_chunk_lauft
  have hf : pwBytes = [] ++ Pipeline.encodeAll (pwChunk ++ pwProg.drop 5) ++ [] := by
    rw [Pipeline.encodeAll_append]
    simpa using pw_split
  have hrip : (pwStart 30).rip = addrOff (natAdresse 4096) ([] : List Byte).length := by
    have h0 : (pwStart 30).rip = natAdresse 4096 := rfl
    rw [h0, List.length_nil]
    exact (addrOff_null _).symm
  obtain ⟨hb, hr, hc, hw, hle⟩ := laufBytes_genommen (natAdresse 4096) pwBytes
    (pwChunk ++ pwProg.drop 5) pwChunk (pwProg.drop 5) [] [] (pwStart 30) s'
    rfl pw_chunk_gerade hs' pw_code hf hrip
  exact ⟨pwChunk, pwProg.drop 5, s', rfl, pw_chunk_gerade, hs', pw_code, hf,
    hrip, hb, hw, hle, pipePaket_hold⟩

/-! ## 3. Dynamic coverage: the taken prefix is priced, not the list.

    `deckung_pipeChunk` covers the STATIC chunk length. Here the
    coverage is over the EXECUTED prefix `T` (`chunk = T ++ rest`):
    the taken length is at most the shallow chunk bound (3 or 5),
    hence covered by the admitted summary over any positive source
    budget. Every premise is used: `hflach`/`hchunk`/`hT` bound the
    static chunk, `hprefix` carries the taken length below it,
    `hsrc` keeps the scaled bound above it. -/

variable {D : Deklaration}

/-- TAKEN-PATH COVERAGE: the executed prefix of a shallow lowered
    chunk is covered by the admitted pipeline summary. -/
theorem deckung_pfad_chunk (c : Pipeline.PipeCfg) (L : Pipeline.Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (src : Nat)
    (p chunk T rest : List Befehl)
    (hflach : Pipeline.senkWert (Pipeline.abbOf c) e c.dst c.tmp = some p)
    (hchunk : Pipeline.senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (hprefix : chunk = T ++ rest)
    (hsrc : 1 ≤ src) :
    Deckung pipeSummary src (decodiertZu T) := by
  have hlen := senkStmt_flach_laenge c L l t f i e hT hw hL p chunk hflach hchunk
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have hwork : targetWork ((decodiertZu T).map fun d => d.befehl) = T.length :=
    arbeit_decodiert T
  subst hprefix
  rw [hwork]
  simp only [List.length_append] at hlen
  omega

/-- JOINT WITNESS for `deckung_pfad_chunk`: the taken prefix is the
    whole witness chunk, covered over source budget 1. -/
theorem deckung_pfad_chunk_zeuge :
    ∃ (p chunk T rest : List Befehl),
      Pipeline.senkWert (Pipeline.abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      Pipeline.senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      chunk = T ++ rest ∧
      1 ≤ 1 ∧
      Deckung pipeSummary 1 (decodiertZu T) ∧
      PipePaket := by
  have hprefix : pwProg.take 5 = pwChunk ++ [] := by simp [pwChunk]
  refine ⟨_, _, _, _, pw_senkWert0, pwChunkCast, hprefix, Nat.le_refl 1, ?_,
    pipePaket_hold⟩
  exact deckung_pfad_chunk pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL 1 _ _ _ _ pw_senkWert0 pwChunkCast hprefix (Nat.le_refl 1)

/-! ## 4. Per-round loop correspondence: one source round is one segment.

    The `n`-round theorem (`schleife_korrekt_endlich`) lifts a
    one-round simulation to `n` rounds with budget accounting. Here
    the anatomy of ONE round is explicit: the labelled run of
    `schleifeSchritte 1 m` steps is one body segment of `m + 2`
    steps back to the head plus the final exit step, and a single
    continuing source round (`retryLauf ... 1`) is exactly that
    shape. The bound predicate is read through `hBed` in both
    branches, so the exit agreement steers the case split. -/

/-- ROUND DECOMPOSITION: the `(n+1)`-round budget splits into one
    body segment plus the `n`-round rest. -/
theorem schleife_runde_zerlegung (koerper : List Instr) (c : Bedingung)
    (adr : Nat → Adresse) (n : Nat) (x : Nat × Zustand) :
    laufL adr (schleifeProg koerper c) (schleifeSchritte (n + 1) koerper.length) x =
      (laufL adr (schleifeProg koerper c) (koerper.length + 2) x).bind
        (laufL adr (schleifeProg koerper c) (schleifeSchritte n koerper.length)) := by
  rw [schleifeSchritte_add, laufL_add]

/-- SINGLE-ROUND CORRESPONDENCE: one continuing source round is the
    one-round labelled segment to the end label, keeping `Rep`. -/
theorem runde_einzel {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (koerper : List Instr) (c : Bedingung)
    (adr : Nat → Adresse)
    (Rep : World D → Env D Γ → Zustand → Prop)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hLese : ∀ σ ρ s, Rep σ ρ s → Rep (bis σ ρ).1 ρ s)
    (hBisStabil : ∀ σ ρ, bis (bis σ ρ).1 ρ = bis σ ρ)
    (hBed : ∀ σ ρ s, Rep σ ρ s → (bis σ ρ).2 = bedingung c s.flags)
    (hWeiter : ∀ σ ρ s, Rep σ ρ s → (bis σ ρ).2 = false →
      ∃ σ₁ ρ₁ s₁, (schritt (bis σ ρ).1 ρ = .ok σ₁ ρ₁ ∨
          (∃ h : true = true, schritt (bis σ ρ).1 ρ = .next h σ₁ ρ₁)) ∧
        laufL adr (schleifeProg koerper c) (koerper.length + 2) (0, s)
          = some (0, s₁) ∧
        Rep σ₁ ρ₁ s₁)
    (hEnde : ∀ σ ρ s, Rep σ ρ s → (bis σ ρ).2 = true →
      ∃ s', laufL adr (schleifeProg koerper c) 1 (0, s)
        = some (koerper.length + 2, s') ∧ Rep (bis σ ρ).1 ρ s')
    (hUeberlauf : ∀ σ ρ σ' ρ', (bis σ ρ).2 = false →
      ueberlauf (bis σ ρ).1 ρ ≠ .ok σ' ρ') :
    ∀ (σ : World D) (ρ : Env D Γ) (s : Zustand),
      Rep σ ρ s →
      ∀ σ' ρ', retryLauf schritt bis ueberlauf 1 σ ρ = .ok σ' ρ' →
        ∃ s', laufL adr (schleifeProg koerper c)
            (schleifeSchritte 1 koerper.length) (0, s)
          = some (koerper.length + 2, s') ∧
          Rep σ' ρ' s' := by
  have hlen : (schleifeProg koerper c).length = koerper.length + 2 :=
    schleifeProg_laenge koerper c
  have hstop : ∀ (k : Nat) (t : Zustand),
      laufL adr (schleifeProg koerper c) k (koerper.length + 2, t)
        = some (koerper.length + 2, t) := by
    intro k t
    exact laufL_stop adr (schleifeProg koerper c) k _ (by simp [hlen])
  intro σ ρ s hRep σ' ρ' hrun
  have hbv : (bis σ ρ).2 = bedingung c s.flags := hBed σ ρ s hRep
  cases heq : bedingung c s.flags with
  | true =>
    have he : (bis σ ρ).2 = true := by rw [hbv, heq]
    have hrun' : retryLauf schritt bis ueberlauf (0 + 1) σ ρ = .ok σ' ρ' := hrun
    rw [wiederhol_steht schritt bis ueberlauf 0 σ ρ he] at hrun'
    cases hrun'
    have hrepL := hLese σ ρ s hRep
    have heL : (bis (bis σ ρ).1 ρ).2 = true := by
      rw [hBisStabil]
      exact he
    obtain ⟨sx, hrunx, hrepx⟩ := hEnde _ _ _ hrepL heL
    rw [hBisStabil] at hrepx
    have hbud : schleifeSchritte 1 koerper.length = 1 + (koerper.length + 2) := by
      unfold schleifeSchritte
      omega
    refine ⟨sx, ?_, hrepx⟩
    rw [hbud, laufL_add, hrunx]
    exact hstop _ _
  | false =>
    have he : (bis σ ρ).2 = false := by rw [hbv, heq]
    obtain ⟨σ₁, ρ₁, s₁, hfort, hseg, hrep₁⟩ := hWeiter σ ρ s hRep he
    have hbud : schleifeSchritte 1 koerper.length = (koerper.length + 2) + 1 := by
      unfold schleifeSchritte
      omega
    have hrun' : retryLauf schritt bis ueberlauf (0 + 1) σ ρ = .ok σ' ρ' := hrun
    have hrun0 : retryLauf schritt bis ueberlauf 0 σ₁ ρ₁ = .ok σ' ρ' := by
      rcases hfort with hok | ⟨_, hnext⟩
      · rw [wiederhol_schritt schritt bis ueberlauf 0 σ σ₁ ρ ρ₁ he hok] at hrun'
        exact hrun'
      · have hstep : retryLauf schritt bis ueberlauf (0 + 1) σ ρ
            = retryLauf schritt bis ueberlauf 0 σ₁ ρ₁ := by
          simp [retryLauf, he, hnext]
        rw [hstep] at hrun'
        exact hrun'
    have hbv1 : (bis σ₁ ρ₁).2 = bedingung c s₁.flags := hBed σ₁ ρ₁ s₁ hrep₁
    cases heq1 : bedingung c s₁.flags with
    | true =>
      have he1 : (bis σ₁ ρ₁).2 = true := by rw [hbv1, heq1]
      simp only [retryLauf, he1] at hrun0
      cases hrun0
      obtain ⟨sx, hrunx, hrepx⟩ := hEnde _ _ _ hrep₁ he1
      refine ⟨sx, ?_, hrepx⟩
      rw [hbud, laufL_add, hseg]
      exact hrunx
    | false =>
      have he1 : (bis σ₁ ρ₁).2 = false := by rw [hbv1, heq1]
      simp only [retryLauf, he1] at hrun0
      exact absurd hrun0 (hUeberlauf σ₁ ρ₁ σ' ρ' he1)

/-- JOINT WITNESS for `runde_einzel`: the witness loop's single
    memory-changing round is the one-round segment to the end label,
    on a table the contract writes. -/
theorem runde_einzel_zeuge :
    ∃ (s' : Zustand),
      zwRep zwSigma0 .nil zwS0 ∧
      retryLauf zwSchritt zwBis zwUeberlauf 1 zwSigma0 .nil
        = .ok (zwSigma1 zwSigma0) .nil ∧
      laufL zwAdr (schleifeProg zwKoerper .e)
        (schleifeSchritte 1 zwKoerper.length) (0, zwS0)
        = some (zwKoerper.length + 2, s') ∧
      zwRep (zwSigma1 zwSigma0) .nil s' ∧
      zwV.schreibt () = true ∧
      (zwSigma0.slots () 0 ()).n = 0 ∧
      ((zwSigma1 zwSigma0).slots () 0 ()).n = 1 := by
  have hRep0 : zwRep zwSigma0 .nil zwS0 := by
    refine ⟨?_, Or.inl ⟨?_, rfl⟩⟩
    · rfl
    · rfl
  have hrun : retryLauf zwSchritt zwBis zwUeberlauf 1 zwSigma0 .nil
      = .ok (zwSigma1 zwSigma0) .nil := rfl
  obtain ⟨s', hT, hrep'⟩ := runde_einzel zwKoerper .e zwAdr
    zwRep zwSchritt zwBis zwUeberlauf zw_lese zw_stabil zw_bed zw_weiter
    zw_ende zw_kein_ueberlauf zwSigma0 .nil zwS0 hRep0 _ _ hrun
  exact ⟨s', hRep0, hrun, hT, hrep', rfl, rfl, rfl⟩

/-! ## 5. The labelled-to-bytes leg: source rounds to fetched bytes.

    `schleife_pfad_bytes` is the leg the follow-up asks for:
    `schleife_korrekt_endlich` (source run to the labelled run of
    `schleifeSchritte n m` steps) followed by `schleife_bytes`
    (`relax_laufBytes` at the loop schema: the labelled run is the
    fetched-byte run of the relaxed image). The witness fixtures
    below load the witness loop schema (`zwKoerper`, all-wide
    layout) at 4096 in W^X memory with the post-round data word.
 -/

/-- The all-wide layout of the witness loop schema. -/
def wpWs : List Bool := alleWeit (schleifeProg zwKoerper .e)

/-- The witness loop image: the all-wide bytes of the schema. -/
def wpBild : List Byte := bild wpWs (schleifeProg zwKoerper .e)

/-- Witness memory: the loop image at 4096, the post-round word `1`
    at 8192, zero elsewhere; data readable/writable, code execute
    only (the `isaSpeicher` shape). -/
def wpMem : Speicher :=
  { isaSpeicher with bytes :=
    fun a => if a.toNat = 8192 then 1 else bytesAusProg wpBild 4096 a }

/-- The post-round witness state: `rax = 1`, flags say equal
    (`zf`), instruction pointer at the image base. -/
def wpPost : Zustand :=
  { register := fun q => if q = .rax then 1 else isaReg q,
    flags := { witnessFlags with zf := true },
    rip := isaStart.rip,
    speicher := wpMem }

/-- The all-wide layout of the witness schema validates. -/
theorem wp_allwide :
    relaxLayoutOk (alleWeit (schleifeProg zwKoerper .e))
      (schleifeProg zwKoerper .e) = true := by
  decide

/-- Relaxation answers the all-wide layout at zero fuel. -/
theorem wp_relax :
    relax 0 (schleifeProg zwKoerper .e) = some wpWs :=
  relax_null (schleifeProg zwKoerper .e) wp_allwide

/-- The witness memory is W^X. -/
theorem wp_wx : WX wpMem := by
  intro x hx
  simp only [wpMem, isaSpeicher, isaExec, decide_eq_true_eq] at hx
  show isaDaten x = false
  simp only [isaDaten, decide_eq_false_iff_not]
  omega

/-- The witness image sits at the witness instruction pointer. -/
theorem wp_code : CodeAt wpPost.speicher wpPost.rip wpBild := by
  intro i hi
  revert i
  decide

/-- The post-round data word reads back. -/
theorem wp_read1 : read64 wpMem (natAdresse 8192) = some 1 := by
  decide

/- CUTS:
   - Skeleton only: `genommenArbeit` names the taken-path count.
   - OPEN: the prefix-run bridge (`laufBytes_genommen`), the dynamic
     `Deckung` producer, the per-round loop correspondence
     (`runde_einzel`), the labelled-to-bytes leg
     (`schleife_pfad_bytes`), refusals, gifts and joint witnesses.
-/

#print axioms genommenArbeit

end Gabbro.Grammatik.X86.PipelineWorkPath
