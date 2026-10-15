/-
  File:      Grammatik/X86/OptLeaSel.lean
  Subject:   LEA selection rule lemma (lane 886).

  DESIGN section 7 row "Flags-aware peepholes": local premise "rule in
  register, flag-liveness, disp-fits-i32, no token op in pure window",
  certificate "A", phase L, cost O(window). DESIGN section 3A tile:
  `LEA` for `a + b*k + c` with `k` in {1,2,4,8} -- pure, no flags, no
  memory event -- preferred over ADD/SHL sequences wherever the address
  form already computes the value.

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.AddressEncoding`, `X86.LeaPureForm`): the validator-decided side
  conditions with their refusals, the value-identity lemma (a scaled
  address form computes base + index*scale + displacement as words, so
  non-address values may use LEA), and the connection rule lemma. No
  `ensures` is derived, no refusal becomes a warning, no faulting form
  is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.AddressEncoding
import Grammatik.X86.LeaPureForm

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one LEA-selection site
    (DESIGN section 7 row): admitted scale, admitted displacement,
    flag-liveness checked, no token op in the pure window. A refused
    OPTIONAL optimisation falls back to another certified translation,
    never to a warning. -/
structure LeaCert where
  skala : Bool
  disp : Bool
  lebendigOk : Bool
  keinToken : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. -/
def leaZulassen (c : LeaCert) : Bool :=
  c.skala && c.disp && c.lebendigOk && c.keinToken

/-- A non-admitted scale refuses the selection. -/
theorem leaVerweigert_skala (c : LeaCert)
    (h : c.skala = false) :
    leaZulassen c = false := by
  simp [leaZulassen, h]

/-- A non-admitted displacement refuses the selection: a constant
    outside the signed 32-bit range has no displacement encoding, and
    wrapping it would change the value. -/
theorem leaVerweigert_disp (c : LeaCert)
    (h : c.disp = false) :
    leaZulassen c = false := by
  simp [leaZulassen, h]

/-- An unchecked flag-liveness refuses: the validator recomputes
    liveness at the site (LEA itself clobbers no flags, proved at the
    step in section 4, but the record is only complete with the
    recomputed citation). -/
theorem leaVerweigert_lebendig (c : LeaCert)
    (h : c.lebendigOk = false) :
    leaZulassen c = false := by
  simp [leaZulassen, h]

/-- A token op in the pure window refuses: LEA emits no memory event,
    so a window that reads or writes shared state is not the pure
    shape this rule selects. -/
theorem leaVerweigert_token (c : LeaCert)
    (h : c.keinToken = false) :
    leaZulassen c = false := by
  simp [leaZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_leaZulassen_ok :
    leaZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-! ## 2. Scale admission: exactly 1, 2, 4 and 8.

    The validator recomputes the accepted `skalaOk` at the site; only
    an admitted scale reaches a SIB encoding (`codeSkala_skalaCode`).
    A scale of 3 (or 5, or 0) has no SIB form: selecting LEA there
    would invent semantics, so the rule must NOT fire. -/

/-- Probe: every admitted scale passes the recomputed check. -/
theorem probe_skala_admitted :
    skalaOk 1 = true ∧ skalaOk 2 = true ∧
      skalaOk 4 = true ∧ skalaOk 8 = true := by
  decide

/-- REFUSAL: scale 3 has no SIB encoding. -/
theorem probe_skala_drei :
    skalaOk 3 = false := by
  decide

/-- REFUSAL: scale 5 has no SIB encoding. -/
theorem probe_skala_fuenf :
    skalaOk 5 = false := by
  decide

/-- The admitted scale survives the SIB bits: what the validator
    admits is what the encoder writes (accepted round trip). -/
theorem leaSkala_kodiert (k : Nat)
    (hk : skalaOk k = true) :
    codeSkala (skalaCode k) = k :=
  codeSkala_skalaCode k hk

/-! ## 3. Certificate construction: recomputed analyses cited.

    The validator fills each field by RECOMPUTING the accepted checks
    (`skalaOk` for the scale, `leaDispOk` for a source-level constant
    displacement) and its own liveness/token analyses. The constructor
    below is that citation shape: no field is trusted input. -/

/-- Certificate constructor from recomputed checks: the scale field
    IS the accepted `skalaOk` decision, the displacement field IS the
    accepted `leaDispOk` decision. -/
def leaCertFuer (k : Nat) (neg : Bool) (m : Nat) (lebendigOk keinToken : Bool) :
    LeaCert :=
  ⟨skalaOk k, leaDispOk neg m, lebendigOk, keinToken⟩

/-- A refused scale refuses the constructed certificate. -/
theorem leaCertFuer_verweigert_skala (k : Nat) (neg : Bool) (m : Nat)
    (lebendigOk keinToken : Bool)
    (h : skalaOk k = false) :
    leaZulassen (leaCertFuer k neg m lebendigOk keinToken) = false := by
  simp [leaZulassen, leaCertFuer, h]

/-- A refused displacement refuses the constructed certificate. -/
theorem leaCertFuer_verweigert_disp (k : Nat) (neg : Bool) (m : Nat)
    (lebendigOk keinToken : Bool)
    (h : leaDispOk neg m = false) :
    leaZulassen (leaCertFuer k neg m lebendigOk keinToken) = false := by
  simp [leaZulassen, leaCertFuer, h]

/-- Probe: scale 8 with a small displacement is admitted. -/
theorem probe_leaCertFuer_ok :
    leaZulassen (leaCertFuer 8 false 5 true true) = true := by
  decide

/-! ## 4. Local rewrite record and the precise refusal case.

    The exact certificate shape is the local rewrite record below plus
    the cited `LeaCert`: which destination, base and index registers,
    which scale, which displacement bytes of which kind. The refusal
    case where the rule must NOT fire: a scale outside {1,2,4,8}
    admits NO address form (`adrOk` is false, so `encodeAdr` is none)
    -- selecting LEA there would invent an encoding. -/

/-- The LOCAL REWRITE RECORD for one LEA-selection site: destination,
    base and index registers, scale, displacement bytes of one kind,
    and the cited validator certificate. -/
structure LeaRewrite where
  dst : Register
  basis : Register
  index : Register
  skala : Nat
  disp : BitVec 32
  art : DispArt
  cert : LeaCert
  deriving DecidableEq, Repr

/-- The selected address form of one rewrite record. -/
def leaRewriteForm (r : LeaRewrite) : AdrForm :=
  skaliertForm r.basis r.index r.skala r.disp r.art

/-- REFUSAL: a scale-3 record admits no address form -- the rule must
    NOT fire, since no SIB byte could encode it. -/
theorem leaRewriteForm_drei_verweigert (r : LeaRewrite)
    (h : r.skala = 3) :
    adrOk (leaRewriteForm r) = false := by
  simp [leaRewriteForm, skaliertForm, adrOk, h, skalaOk_drei]

/-! ## 5. Value identity: what the selected LEA computes.

    A scaled address form computes base + index*scale + displacement
    as words. Non-address values may use LEA for exactly this reason:
    the arithmetic coincides with the integer sum, read through the
    canonical word under width-exactness (section 6). The four-corner
    product of two singletons IS the product, so the source `mul` of
    two literals normalises to its value. -/

/-- `imin x x` is `x`. -/
theorem imin_selbst (x : Int) : imin x x = x := by
  unfold imin
  exact if_pos (Int.le_refl x)

/-- `imax x x` is `x`. -/
theorem imax_selbst (x : Int) : imax x x = x := by
  unfold imax
  exact if_pos (Int.le_refl x)

/-- The lower four-corner product of the scale: the `mul` bound. -/
def leaMulLo (b k : Int) : Int :=
  imin (imin (b * k) (b * k)) (imin (b * k) (b * k))

/-- The upper four-corner product of the scale: the `mul` bound. -/
def leaMulHi (b k : Int) : Int :=
  imax (imax (b * k) (b * k)) (imax (b * k) (b * k))

/-- The lower corner normalises to the product. -/
theorem leaMulLo_selbst (b k : Int) : leaMulLo b k = b * k := by
  simp [leaMulLo, imin_selbst]

/-- The upper corner normalises to the product. -/
theorem leaMulHi_selbst (b k : Int) : leaMulHi b k = b * k := by
  simp [leaMulHi, imax_selbst]

/-- VALUE IDENTITY: a scaled address form computes base +
    index*scale + displacement as words, for ARBITRARY values. This is
    why non-address values may use LEA: the arithmetic coincides with
    the integer sum `a + b*k + c` read through the canonical word. -/
theorem leaWert_identitaet (s : Zustand) (n : Adresse) (bb bi : Register)
    (a b : Wort) (k : Nat) (d : BitVec 32) (art : DispArt)
    (hb : s.register bb = a) (hi : s.register bi = b) :
    adrEff s n (skaliertForm bb bi k d art) =
      a + b * BitVec.ofNat 64 k +
        dispWortArt ⟨some bb, some bi, k, d, art, false⟩ := by
  simp [adrEff, skaliertForm, hb, hi]

/-! ## 6. Word bridge: the source sum reads through the word.

    The source computes `a + b*k + c` over `Int`; LEA computes over
    words. Under validator-decided width-exactness (nonnegative parts,
    total fit: no truncation, no wrap) the word image of the sum IS
    the LEA arithmetic. -/

/-- `ofNat` distributes over addition. -/
theorem wortOfNat_add (n x y : Nat) :
    (BitVec.ofNat n (x + y) : BitVec n) =
      BitVec.ofNat n x + BitVec.ofNat n y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- `ofNat` distributes over multiplication. -/
theorem wortOfNat_mul (n x y : Nat) :
    (BitVec.ofNat n (x * y) : BitVec n) =
      BitVec.ofNat n x * BitVec.ofNat n y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]

/-- The source sum reads whole through the canonical word: under
    width-exactness (nonnegative parts, total fit: no truncation, no
    wrap) the word image of `a + b*k + c` IS the LEA arithmetic on the
    word images. The equation is exact from part-nonnegativity alone;
    total fit is the separate read-back conjunct of the rule lemma. -/
theorem leaWort_bruecke (a b : Int) (k : Nat) (c : Int)
    (ha : 0 ≤ a) (hbn : 0 ≤ b) (hc : 0 ≤ c) :
    BitVec.ofNat 64 ((a + b * ↑k + c).toNat) =
      (BitVec.ofNat 64 a.toNat + BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 k) +
        BitVec.ofNat 64 c.toNat := by
  have hbk : 0 ≤ b * (↑k : Int) := Int.mul_nonneg hbn (by omega)
  have e1 : (b * (↑k : Int)).toNat = b.toNat * k := by
    rw [Int.toNat_mul hbn (by omega)]
    simp
  have e2 : (a + b * (↑k : Int)).toNat = a.toNat + b.toNat * k := by
    rw [Int.toNat_add ha hbk, e1]
  have e3 : ((a + b * (↑k : Int)) + c).toNat =
      a.toNat + b.toNat * k + c.toNat := by
    rw [Int.toNat_add (by omega) hc, e2]
  rw [e3, wortOfNat_add, wortOfNat_add, wortOfNat_mul]

/-! ## 7. Executed step: the selection is pure.

    An executed LEA step writes the selected address into the
    destination, keeps every flag and every memory byte, and advances
    RIP past its length. No memory event, no flag clobber: the
    no-flags purity the DESIGN row selects LEA for. -/

/-- An executed LEA step writes the selected address into `dst`. -/
theorem leaSchritt_wert (dst : Register) (f : AdrForm) (l : Nat) (s : Zustand)
    (ripNext : Adresse)
    (hok : laengeOk l = true) :
    (leaFormSchritt dst f l s ripNext).map (fun t => t.register dst) =
      some (adrEff s ripNext f) := by
  unfold leaFormSchritt
  rw [hok]
  simp [regSet]

/-- An executed LEA step keeps every flag. -/
theorem leaSchritt_flags (dst : Register) (f : AdrForm) (l : Nat) (s : Zustand)
    (ripNext : Adresse)
    (hok : laengeOk l = true) :
    (leaFormSchritt dst f l s ripNext).map (fun t => t.flags) =
      some s.flags := by
  unfold leaFormSchritt
  rw [hok]
  simp

/-- An executed LEA step is no memory event: every byte is kept. -/
theorem leaSchritt_speicher (dst : Register) (f : AdrForm) (l : Nat) (s : Zustand)
    (ripNext : Adresse)
    (hok : laengeOk l = true) :
    (leaFormSchritt dst f l s ripNext).map (fun t => t.speicher) =
      some s.speicher := by
  unfold leaFormSchritt
  rw [hok]
  simp

/-! ## 8. Window heads: selected literal versus computed sum.

    The two ends of the selection at source level: the folded literal
    (what the LEA materialises) and the computed `a + b*k + c` over
    literals (what the ADD sequence would compute). The `mul` of two
    literals carries the four-corner bound; `weiter` normalises it to
    the exact product by section 5, so both heads share one type. -/

/-- Selected window head: the folded literal. -/
def leaFensterLit {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (a b : Int) (k : Nat) (c : Int) :
    Expr D Γ Λ (.int ((a + b * (k : Int)) + c) ((a + b * (k : Int)) + c)) :=
  .lit ((a + b * (k : Int)) + c)

/-- Unselected window head: `a + (b*k) + c` over literals. -/
def leaFensterAdd {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (a b : Int) (k : Nat) (c : Int)
    (hw1 : b * (k : Int) ≤ leaMulLo b (k : Int))
    (hw2 : leaMulHi b (k : Int) ≤ b * (k : Int)) :
    Expr D Γ Λ (.int ((a + b * (k : Int)) + c) ((a + b * (k : Int)) + c)) :=
  .add (.add (.lit a)
    (.weiter hw1 hw2 (.mul (.lit b) (.lit (k : Int))))) (.lit c)

/-! ## 9. Connection: selecting LEA preserves everything observed.

    The rule lemma over ARBITRARY values with validator-decided side
    conditions (DESIGN section 7 row): admitted certificate (all four
    fields decided true), admitted scale (`skalaOk`, so the SIB bits
    carry it), width-exactness (nonnegative parts plus total fit, so
    the word reads back whole), registers holding the word images,
    the cited displacement equation (the validator's recomputed
    disp bytes name the source addend), and a checked step length.
    Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved (selected literal and
    computed sum agree);
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree on every path), every downstream
    observation agrees: contracts at their place read the same values
    from the same environments, call logs gain no event (no call on
    either side), no shared access is added or removed for
    concurrency (both windows read `orte = []`, proved as its own
    conjunct), the step-budget accounting is unchanged (same block
    shape, the replaced computation is pure and unbudgeted), and float
    checks elsewhere see identical environments (both sides are
    integer-only: no rounding scope is entered, no `bruch` is folded);
    (3) the certificate is admitted and the scale survives the SIB
    bits;
    (4) the source sum reads whole through the canonical word as the
    LEA arithmetic;
    (5) the selected address form computes exactly that arithmetic;
    (6) the LEA step computes the source value with no flag clobber
    and no memory event;
    (7) the folded value reads back whole through the word.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (there is no
    divisor, no load, no float op in either window). The checker's
    range at the site (`weiter`/`narrow`) is untouched by the
    selection and still enforced there. -/

/-- CONNECTION: selecting LEA for `a + b*k + c` preserves value,
    outcome, certificate, word image, target value, purity and the
    width-exact read-back. -/
theorem OptLeaSel_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (a b : Int) (c : Int)
    (sel : LeaRewrite)
    (hsk : sel.cert.skala = true) (hdp : sel.cert.disp = true)
    (hfl : sel.cert.lebendigOk = true) (htk : sel.cert.keinToken = true)
    (hk : skalaOk sel.skala = true)
    (ha : 0 ≤ a) (hbn : 0 ≤ b) (hc : 0 ≤ c)
    (hW : 0 ≤ (a + b * ((sel.skala : Int))) + c ∧
      (a + b * ((sel.skala : Int))) + c < 2 ^ 64)
    (hw1 : b * ((sel.skala : Int)) ≤ leaMulLo b ((sel.skala : Int)))
    (hw2 : leaMulHi b ((sel.skala : Int)) ≤ b * ((sel.skala : Int)))
    (rest : Endblock D V l
      ((.int ((a + b * ((sel.skala : Int))) + c)
        ((a + b * ((sel.skala : Int))) + c)) :: Γ) Λ)
    (s : Zustand) (n : Adresse) (len : Nat)
    (hrb : s.register sel.basis = BitVec.ofNat 64 a.toNat)
    (hri : s.register sel.index = BitVec.ofNat 64 b.toNat)
    (hdisp : dispWortArt (leaRewriteForm sel) = BitVec.ofNat 64 c.toNat)
    (hok : laengeOk len = true)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (leaFensterLit (D := D) (Γ := Γ) (Λ := Λ) a b sel.skala c) σ ρ).n
      = (eval σ₀ (leaFensterAdd (D := D) (Γ := Γ) (Λ := Λ) a b sel.skala c hw1 hw2) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (leaFensterLit (D := D) (Γ := Γ) (Λ := Λ) a b sel.skala c) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (leaFensterAdd (D := D) (Γ := Γ) (Λ := Λ) a b sel.skala c hw1 hw2) rest) σ ρ
    ∧ (leaFensterLit (D := D) (Γ := Γ) (Λ := Λ) a b sel.skala c).orte
        = ([] : List (D.Tab ⊕ D.Glob))
      ∧ (leaFensterAdd (D := D) (Γ := Γ) (Λ := Λ) a b sel.skala c hw1 hw2).orte
        = ([] : List (D.Tab ⊕ D.Glob))
    ∧ leaZulassen sel.cert = true
    ∧ codeSkala (skalaCode sel.skala) = sel.skala
    ∧ BitVec.ofNat 64 ((a + b * ((sel.skala : Int)) + c).toNat) =
        (BitVec.ofNat 64 a.toNat +
          BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 sel.skala) +
        BitVec.ofNat 64 c.toNat
    ∧ adrEff s n (leaRewriteForm sel) =
        BitVec.ofNat 64 a.toNat +
          BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 sel.skala +
        dispWortArt (leaRewriteForm sel)
    ∧ adrEff s n (leaRewriteForm sel) =
        BitVec.ofNat 64 ((a + b * ((sel.skala : Int)) + c).toNat)
    ∧ (leaFormSchritt sel.dst (leaRewriteForm sel) len s n).map
        (fun t => t.register sel.dst)
        = some (adrEff s n (leaRewriteForm sel))
    ∧ (leaFormSchritt sel.dst (leaRewriteForm sel) len s n).map
        (fun t => t.flags) = some s.flags
    ∧ (leaFormSchritt sel.dst (leaRewriteForm sel) len s n).map
        (fun t => t.speicher) = some s.speicher
    ∧ (BitVec.ofNat 64 ((a + b * ((sel.skala : Int)) + c).toNat)).toNat =
        ((a + b * ((sel.skala : Int)) + c).toNat) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [leaZulassen, hsk, hdp, hfl, htk]
  · exact leaSkala_kodiert _ hk
  · exact leaWort_bruecke a b sel.skala c ha hbn hc
  · exact leaWert_identitaet s n sel.basis sel.index
      (BitVec.ofNat 64 a.toNat) (BitVec.ofNat 64 b.toNat)
      sel.skala sel.disp sel.art hrb hri
  · calc adrEff s n (leaRewriteForm sel)
        = BitVec.ofNat 64 a.toNat +
            BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 sel.skala +
          dispWortArt (leaRewriteForm sel) :=
          leaWert_identitaet s n sel.basis sel.index
            (BitVec.ofNat 64 a.toNat) (BitVec.ofNat 64 b.toNat)
            sel.skala sel.disp sel.art hrb hri
      _ = BitVec.ofNat 64 a.toNat +
            BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 sel.skala +
          BitVec.ofNat 64 c.toNat := by rw [hdisp]
      _ = BitVec.ofNat 64 ((a + b * ((sel.skala : Int)) + c).toNat) :=
          (leaWort_bruecke a b sel.skala c ha hbn hc).symm
  · exact leaSchritt_wert sel.dst (leaRewriteForm sel) len s n hok
  · exact leaSchritt_flags sel.dst (leaRewriteForm sel) len s n hok
  · exact leaSchritt_speicher sel.dst (leaRewriteForm sel) len s n hok
  · have hlt : ((a + b * ((sel.skala : Int)) + c).toNat) < 2 ^ 64 := by
      omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-! ## 10. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptLeaSel_verbindung` instantiated JOINTLY:
    `8192 + 1*8 + 5` folds to `8205` under a `bind` with a `leave`
    continuation, in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside
    the reached F-machine run `MB` that changes memory
    (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`); the LEA
    witness state beside it holds `rbx = 8192`, `rcx = 1`, and the
    selected scaled form with displacement byte `5` computes `8205`
    with no flag clobber and no memory event. -/

/-- JOINT WITNESS for `OptLeaSel_verbindung`: `8192 + 1*8 + 5`
    selects LEA on `refD`, beside the memory-changing reached run. -/
theorem OptLeaSel_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (a b : Int) (c : Int)
      (sel : LeaRewrite)
      (_hsk : sel.cert.skala = true) (_hdp : sel.cert.disp = true)
      (_hfl : sel.cert.lebendigOk = true) (_htk : sel.cert.keinToken = true)
      (_hk : skalaOk sel.skala = true)
      (_ha : 0 ≤ a) (_hbn : 0 ≤ b) (_hc : 0 ≤ c)
      (_hW : 0 ≤ (a + b * ((sel.skala : Int))) + c ∧
        (a + b * ((sel.skala : Int))) + c < 2 ^ 64)
      (_hw1 : b * ((sel.skala : Int)) ≤ leaMulLo b ((sel.skala : Int)))
      (_hw2 : leaMulHi b ((sel.skala : Int)) ≤ b * ((sel.skala : Int)))
      (rest : Endblock refD V l
        ((.int ((a + b * ((sel.skala : Int))) + c)
          ((a + b * ((sel.skala : Int))) + c)) :: Γ) Λ)
      (s : Zustand) (n : Adresse) (len : Nat)
      (_hrb : s.register sel.basis = BitVec.ofNat 64 a.toNat)
      (_hri : s.register sel.index = BitVec.ofNat 64 b.toNat)
      (_hdisp : dispWortArt (leaRewriteForm sel) = BitVec.ofNat 64 c.toNat)
      (_hok : laengeOk len = true)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (leaFensterLit (D := refD) (Γ := Γ) (Λ := Λ) a b sel.skala c) σ ρ).n
        = (eval σ₀ (leaFensterAdd (D := refD) (Γ := Γ) (Λ := Λ) a b sel.skala c
            _hw1 _hw2) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind
            (leaFensterLit (D := refD) (Γ := Γ) (Λ := Λ) a b sel.skala c) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind
            (leaFensterAdd (D := refD) (Γ := Γ) (Λ := Λ) a b sel.skala c
              _hw1 _hw2) rest) σ ρ
      ∧ adrEff s n (leaRewriteForm sel) =
          BitVec.ofNat 64 ((a + b * ((sel.skala : Int)) + c).toNat)
      ∧ (leaFormSchritt sel.dst (leaRewriteForm sel) len s n).map
          (fun t => t.register sel.dst) =
          some (BitVec.ofNat 64 ((a + b * ((sel.skala : Int)) + c).toNat))
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true,
    8192, 1, 5,
    ⟨.rax, .rbx, .rcx, 8, BitVec.ofNat 32 5, .d8, ⟨true, true, true, true⟩⟩,
    rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    Endblock.leave rfl,
    leaWitZustand, BitVec.ofNat 64 4101, 5,
    by decide, by decide, by decide, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    Proved here: the validator-decided side conditions (`LeaCert`,
    `leaZulassen`) with all four refusals (scale, displacement,
    flag-liveness, token op) and the admitted probe; scale admission
    pins (1/2/4/8 admitted, 3/5 refused) with the SIB round trip
    (`leaSkala_kodiert`, accepted `codeSkala_skalaCode`); the
    certificate constructor from recomputed checks (`leaCertFuer`
    over accepted `skalaOk`/`leaDispOk`) with its two refusal
    bridges and admission probe; the local rewrite record
    (`LeaRewrite`, `leaRewriteForm`) with the precise target-level
    refusal where the rule must NOT fire (scale 3 admits no
    `adrOk` form, so no SIB byte could encode it); the
    value-identity lemma (`leaWert_identitaet`: a scaled address
    form computes base + index*scale + displacement as words, for
    arbitrary values -- why non-address values may use LEA); the
    four-corner normalisation (`imin_selbst`, `imax_selbst`,
    `leaMulLo_selbst`, `leaMulHi_selbst`); the word bridge
    (`wortOfNat_add`, `wortOfNat_mul`, `leaWort_bruecke`: the source
    sum reads whole through the canonical word as the LEA
    arithmetic); the executed-step purity (`leaSchritt_wert`,
    `leaSchritt_flags`, `leaSchritt_speicher`); the window heads
    (`leaFensterLit`, `leaFensterAdd`); the connection rule lemma
    (`OptLeaSel_verbindung`: value, outcome, empty footprints,
    admission, SIB round trip, word image, target identity, LEA
    computes the source value, step value/flags/memory, width-exact
    read-back) with its joint witness
    (`OptLeaSel_verbindung_zeuge`: `8192 + 1*8 + 5` selects LEA on
    the table-writing `refD` beside the memory-changing reached run
    `MB`, with the fetched LEA computing `8205`).
    NOT proved here, and not claimed:
    - No silicon correspondence: LEA purity (no memory read, no flag
      change) is the named Intel SDM entry reused through the
      accepted `leaFormSchritt` lemmas; correspondence of byte rows
      to hardware truth is open.
    - No new codec rows: every form, byte and step is the accepted
      `AddressEncoding`/`ExtendedExecution` one; disp8/disp32
      selection stays with the accepted encoder.
    - No TSO/GX bridge: LEA emits no memory event, so there is no
      footprint, no visibility and no grouping to transfer.
    - No lowering-pass certificate: which backend pass picks the
      scaled form for a source window (layer-B/C availability and
      dominance, recomputed liveness) stays with the lowering lane
      per IR-VALIDIERUNG; this file proves what the selected form
      computes, not when a pass may pick it.
    - No ADD/SHL-sequence comparison at instruction level: the pilot
      `Befehl` has no `shl`/`imul`/`lea` forms, so the unselected
      side is the word arithmetic those instructions would compute;
      per-form byte comparison waits for the extended vocabulary.
    - No totalCost/work-bound inequality: the replaced computation
      is pure and unbudgeted, so step-budget accounting is
      unchanged; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG (lane 278).
    - No source correspondence beyond the window, no ABI/loader/
      entry/budget claim; floats are untouched (both windows are
      integer-only: no rounding scope is entered, no `bruch` folded).
-/

#print axioms leaVerweigert_skala
#print axioms leaVerweigert_disp
#print axioms leaVerweigert_lebendig
#print axioms leaVerweigert_token
#print axioms probe_leaZulassen_ok
#print axioms probe_skala_admitted
#print axioms probe_skala_drei
#print axioms probe_skala_fuenf
#print axioms leaSkala_kodiert
#print axioms leaCertFuer_verweigert_skala
#print axioms leaCertFuer_verweigert_disp
#print axioms probe_leaCertFuer_ok
#print axioms leaRewriteForm_drei_verweigert
#print axioms imin_selbst
#print axioms imax_selbst
#print axioms leaMulLo_selbst
#print axioms leaMulHi_selbst
#print axioms leaWert_identitaet
#print axioms wortOfNat_add
#print axioms wortOfNat_mul
#print axioms leaWort_bruecke
#print axioms leaSchritt_wert
#print axioms leaSchritt_flags
#print axioms leaSchritt_speicher
#print axioms OptLeaSel_verbindung
#print axioms OptLeaSel_verbindung_zeuge

end Gabbro.Grammatik.X86
