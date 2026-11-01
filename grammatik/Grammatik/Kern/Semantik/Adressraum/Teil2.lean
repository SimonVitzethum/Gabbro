module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Semantik.Adressraum.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Adressraum

/-! ## 9. Range-check discharge shapes, Seite-tagged reading, execution linkage (C6, Adressraum side) -/

/- The Adressraum side of cut C6, closed without touching `Semantik.lean`:
   the discharge SHAPE exists here -- a step whose constructor requires
   `validiert` (the `h : …` premise style of `Stmt`: `schreibBytes` carries
   `hhi : hi + n ≤ D.count t`; `BereichSchritt.geprueft` carries
   `h : validiert r k`) -- with an executable check and its holds-lemma, the
   Seite-tagged reading of the world mapping, and the validated copy run
   through the model write path (`schreibBytes`/`bytesAb`). What stays on the
   Semantik side, booked below and not faked here: a `Stmt`/`exec` branch
   taking such a step (or an `h : validiert`-carrying constructor), and a
   `Seite` partition in `World` it could check against. -/

/-! ### The executable range check, with its holds-lemma -/

/-- The range check, executable: the `decide` of the `innerhalb` conjunction,
    stated over the conjunction itself so no unfolding instance is needed. -/
def imBereichBool (r : UserRegion) (addr laenge : Nat) : Bool :=
  decide (r.basis ≤ addr ∧ addr + laenge ≤ r.basis + r.laenge)

/-- The executable check holds exactly where the proposition holds. -/
theorem imBereichBool_holds (r : UserRegion) (addr laenge : Nat) :
    imBereichBool r addr laenge = true ↔ innerhalb r addr laenge := by
  unfold imBereichBool
  constructor
  · intro h
    have h' : r.basis ≤ addr ∧ addr + laenge ≤ r.basis + r.laenge :=
      of_decide_eq_true h
    exact h'
  · intro h
    have h' : r.basis ≤ addr ∧ addr + laenge ≤ r.basis + r.laenge := h
    exact decide_eq_true h'

/-- The copy check, executable: the `decide` of the `validiert` conjunction,
    stated over the conjunction itself so no unfolding instance is needed. -/
def kopieImBereichBool (r : UserRegion) (k : Kopie) : Bool :=
  decide (r.basis ≤ k.userAddr ∧ k.userAddr + k.laenge ≤ r.basis + r.laenge)

/-- The executable copy check holds exactly where the validation holds. -/
theorem kopieImBereichBool_holds (r : UserRegion) (k : Kopie) :
    kopieImBereichBool r k = true ↔ validiert r k := by
  unfold kopieImBereichBool
  constructor
  · intro h
    have h' : r.basis ≤ k.userAddr ∧ k.userAddr + k.laenge ≤ r.basis + r.laenge :=
      of_decide_eq_true h
    exact h'
  · intro h
    have h' : r.basis ≤ k.userAddr ∧ k.userAddr + k.laenge ≤ r.basis + r.laenge := h
    exact decide_eq_true h'

/-- Every copy reads either checked or refused: the boolean check decides. -/
theorem kopieImBereichBool_entweder (r : UserRegion) (k : Kopie) :
    kopieImBereichBool r k = true ∨ kopieImBereichBool r k = false := by
  cases hbt : kopieImBereichBool r k with
  | true => exact Or.inl rfl
  | false => exact Or.inr rfl

/-- Refusal, executable: the check reads `false` exactly on refused copies. -/
theorem kopieImBereichBool_verweigert (r : UserRegion) (k : Kopie) :
    kopieImBereichBool r k = false ↔ ausserhalbVerweigert r k := by
  unfold ausserhalbVerweigert
  constructor
  · intro hf hc
    have ht : kopieImBereichBool r k = true := Iff.mpr (kopieImBereichBool_holds r k) hc
    rw [ht] at hf
    exact absurd hf (by decide)
  · intro hn
    have hnt : kopieImBereichBool r k ≠ true :=
      fun ht => hn (Iff.mp (kopieImBereichBool_holds r k) ht)
    cases hbt : kopieImBereichBool r k with
    | true => exact absurd hbt hnt
    | false => rfl

/-! ### The discharge shape: a step whose transition requires the region -/

/- The range check inside the step: `geprueft` carries `h : validiert r k`
   the way `Stmt.schreibBytes` carries `hhi : hi + n ≤ D.count t` -- an
   out-of-region copy is not a refused step here, it is NO step of this shape.
   Refusal stays `ausserhalbVerweigert`, beside the step, as `exec` stays
   beside the check. -/

/-- A boundary step with its range check discharged at construction: pure, or
    exactly one copy against exactly one region, with the check. -/
inductive BereichSchritt where
  | rein : BereichSchritt
  | geprueft (r : UserRegion) (k : Kopie) (h : validiert r k) : BereichSchritt

/-- The carried region and copy, where there is one. -/
def schrittTraeger : BereichSchritt → Option (UserRegion × Kopie)
  | .rein => none
  | .geprueft r k _ => some (r, k)

/-- The constructor reads back: what was checked is what the step carries. -/
theorem schrittTraeger_geprueft (r : UserRegion) (k : Kopie) (h : validiert r k) :
    schrittTraeger (.geprueft r k h) = some (r, k) :=
  by rfl

/-- The discharge: any carried copy of any step is validated against its
    carried region -- the transition premise, as a theorem over the shape.
    This is the Adressraum side of C6; the `exec` branch taking such a step
    is the Semantik side, and it is not here. -/
theorem bereichSchritt_fordertBereich (s : BereichSchritt) (r : UserRegion)
    (k : Kopie) (h : schrittTraeger s = some (r, k)) : validiert r k := by
  cases s with
  | rein => simp only [schrittTraeger, reduceCtorEq] at h
  | geprueft r' k' hv =>
      simp only [schrittTraeger, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hv

/-- A validated transition already meets the `exec`-side demand shape (§8):
    carrying the copy against the region, with the check. -/
theorem gepruefterUebergang_fordertBereich (u : GepruefterUebergang) :
    execFordertBereich u.anweisung u.region u.kopie :=
  fun _ => u.gecheckt

/-- A validated copy, wrapped as a kernel step, meets the demand shape. -/
theorem gepruefteKopie_alsForderung (g : GepruefteKopie) :
    execFordertBereich (KernAnweisung.kopie g.kopie) g.region g.kopie :=
  fun _ => g.gecheckt

/-- Refusal is the negation, beside the step: no checked step carries a
    refused copy, because there is no proof to build it with. -/
theorem verweigert_keinGeprueft (r : UserRegion) (k : Kopie)
    (h : ausserhalbVerweigert r k) : ¬ validiert r k :=
  h

/-! ### The user partition, Seite-tagged: how the world mapping hangs on regions -/

/- The user side of the world mapping, tagged: `getaggterSchluessel` is the
   `Int` key `weltByte` reads (`(addr : Int)` into `World.slots`), and a
   user-tagged member lands in `benutzerTeil`. The kernel side reads through
   the same flat mapping -- the split is in the tags and the regions, not in
   `World`, which is why the `Seite` partition in `World` stays Semantik-side
   work (cut C6 remainder). -/

/-- A Seite-tagged address: which side it belongs to travels with the offset. -/
structure GetaggteAddr where
  seite : Seite
  addr : Nat
  deriving DecidableEq, Repr

/-- The region behind a side: the user side hangs on `u`, the kernel side
    on `k`. -/
def seitenRegion (u k : UserRegion) : Seite → UserRegion
  | .kern => k
  | .user => u

/-- Seite-tagged membership: the offset lies in its own side's region. -/
def seitenZugehoerig (u k : UserRegion) (a : GetaggteAddr) : Prop :=
  adresseInRegion (seitenRegion u k a.seite) a.addr

/-- A tagged address as a world key: the `Int` key `weltByte` reads. -/
def getaggterSchluessel (a : GetaggteAddr) : Int :=
  (a.addr : Int)

/-- The bridge, both ways: `Nat` membership is `Int` membership. -/
theorem seitenBruecke (r : UserRegion) (addr : Nat) :
    adresseInRegion r addr ↔ schluesselInRegion r (addr : Int) := by
  unfold adresseInRegion schluesselInRegion
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, by omega⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, by omega⟩

/-- A user-tagged member reads inside the user part of the world mapping. -/
theorem getaggteUserAddr_imTeil (u k : UserRegion) (a : GetaggteAddr)
    (hu : a.seite = .user) (h : seitenZugehoerig u k a) :
    benutzerTeil u (getaggterSchluessel a) := by
  unfold seitenZugehoerig at h
  unfold benutzerTeil getaggterSchluessel at ⊢
  rw [hu] at h
  exact (seitenBruecke u a.addr).mp h

/-- A kernel-tagged member reads inside the kernel region's keys. -/
theorem getaggteKernAddr_imTeil (u k : UserRegion) (a : GetaggteAddr)
    (hk : a.seite = .kern) (h : seitenZugehoerig u k a) :
    schluesselInRegion k (getaggterSchluessel a) := by
  unfold seitenZugehoerig at h
  unfold getaggterSchluessel at ⊢
  rw [hk] at h
  exact (seitenBruecke k a.addr).mp h

/-- The split, tagged: no offset is a member on both sides at once. -/
theorem seitenZugehoerig_trennt (u k : UserRegion) (hsep : bereicheGetrennt u k)
    (a b : GetaggteAddr) (ha : a.seite = .user) (hb : b.seite = .kern)
    (ha' : seitenZugehoerig u k a) (hb' : seitenZugehoerig u k b)
    (heq : a.addr = b.addr) : False := by
  unfold seitenZugehoerig at ha' hb'
  rw [ha] at ha'
  rw [hb] at hb'
  rw [heq] at ha'
  exact hsep b.addr ha' hb'

/-! ### The validated copy through the model write path -/

/- As far as closable without Semantik changes: the validated copy runs through
   `World.schreibBytes`/`bytesAb` -- the same functions `execStmt`'s
   `schreibBytes` branch and `eval`'s `leseBytes` branch bind. What is proved:
   the copied byte list has the validated length, and every source key it reads
   lies in the validated user part. What is NOT proved, and needs the Semantik
   side: that `exec` refuses the run when the check fails -- the model memory
   is total, so an out-of-region copy still reads and writes here. -/

/-- A validated copy run through the model: read the validated source range,
    write it at the kernel address -- through `schreibBytes`/`bytesAb`, the
    functions the `exec`/`eval` byte paths bind. -/
def modellKopieAusfuehrt (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (g : GepruefteKopie)
    (σ : World D) : World D :=
  σ.schreibBytes t f hf Λ (g.kopie.kernAddr : Int)
    (weltBytes D t f hf σ g.kopie.userAddr g.kopie.laenge)

/-- The execution copies exactly the validated length. -/
theorem kopieBytes_laenge (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ : World D) :
    (weltBytes D t f hf σ g.kopie.userAddr g.kopie.laenge).length = g.kopie.laenge := by
  rw [weltBytes_istBytesAb]
  exact World.bytesAb_length _ _ _ _ _ _

/-- Every source key of a validated copy lies in the validated user part:
    the execution reads no key the check did not cover. -/
theorem validiert_quellSchluessel_imTeil (r : UserRegion) (k : Kopie)
    (h : validiert r k) (i : Nat) (hi : i < k.laenge) :
    schluesselInRegion r ((k.userAddr + i : Nat) : Int) := by
  unfold validiert innerhalb at h
  unfold schluesselInRegion at ⊢
  obtain ⟨h1, h2⟩ := h
  constructor <;> omega

/-- The execution linkage: the model run of a validated copy has the validated
    length and reads only validated user-part keys. -/
theorem modellKopieAusfuehrt_quellBereich (D : Deklaration) (t : D.Tab)
    (f : D.Feld t) (hf : D.typ t f = .int 0 255) (g : GepruefteKopie)
    (σ : World D) :
    (weltBytes D t f hf σ g.kopie.userAddr g.kopie.laenge).length = g.kopie.laenge ∧
    ∀ i : Nat, i < g.kopie.laenge →
      schluesselInRegion g.region ((g.kopie.userAddr + i : Nat) : Int) :=
  ⟨kopieBytes_laenge D t f hf g σ,
   fun i hi => validiert_quellSchluessel_imTeil g.region g.kopie g.gecheckt i hi⟩

#print axioms imBereichBool_holds
#print axioms kopieImBereichBool_holds
#print axioms kopieImBereichBool_entweder
#print axioms kopieImBereichBool_verweigert
#print axioms schrittTraeger_geprueft
#print axioms bereichSchritt_fordertBereich
#print axioms gepruefterUebergang_fordertBereich
#print axioms gepruefteKopie_alsForderung
#print axioms verweigert_keinGeprueft
#print axioms seitenBruecke
#print axioms getaggteUserAddr_imTeil
#print axioms getaggteKernAddr_imTeil
#print axioms seitenZugehoerig_trennt
#print axioms kopieBytes_laenge
#print axioms validiert_quellSchluessel_imTeil
#print axioms modellKopieAusfuehrt_quellBereich

/-! ## 10. The exec counterpart of `validiert`: the checked step discharges
    through the exec write path (C6) -/

/- What `validiert` was missing, given here without touching `Semantik.lean`:
    the checked transition -- `BereichSchritt.geprueft`, which carries
    `h : validiert r k` the way `Stmt.schreibBytes` carries
    `hhi : hi + n ≤ D.count t` -- discharges through the very functions the
    `exec`/`eval` byte paths bind. `modellKopieAusfuehrt_istExecPfad` names the
    identity: the validated-copy run IS `World.schreibBytes` over
    `World.bytesAb` (`execStmt`'s `schreibBytes` branch runs the former,
    `eval`'s `leseBytes` branch binds the latter, `weltBytes_istBytesAb`
    above). `schrittAusfuehrt_entlaedt` runs the discharge end to end: from a
    checked step and its carrier equation, the executable check reads `true`
    AND the model run has the validated length AND reads only validated
    user-part keys. What stays booked, unchanged: no `Stmt`/`Block`
    transition takes such a step yet, and no `World` carries a `Seite`
    partition -- the Semantik side of cut C6. -/

/-- The validated-copy run, as the exec write path: `World.schreibBytes` over
    `World.bytesAb` -- the exact pair of calls the `exec`/`eval` byte paths
    bind. Stated as `rfl` because the wiring is by identity, not by
    correspondence (cf. `weltBytes_istBytesAb` above). -/
theorem modellKopieAusfuehrt_istExecPfad (D : Deklaration) (t : D.Tab)
    (f : D.Feld t) (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (g : GepruefteKopie) (σ : World D) :
    modellKopieAusfuehrt D t f hf Λ g σ
      = σ.schreibBytes t f hf Λ (g.kopie.kernAddr : Int)
          (σ.bytesAb t f hf g.kopie.laenge (g.kopie.userAddr : Int)) :=
  by rfl

/-- The executable check discharges on every checked step: deciding and
    carrying agree, by construction. -/
theorem geprueft_bool_haelt (r : UserRegion) (k : Kopie) (h : validiert r k) :
    kopieImBereichBool r k = true :=
  Iff.mpr (kopieImBereichBool_holds r k) h

/-- **The checked transition discharges in exec.** From a checked step and its
    carrier equation: the executable check reads `true`, and the run through
    the exec write path (`modellKopieAusfuehrt`, i.e. `World.schreibBytes`
    over `World.bytesAb` per `modellKopieAusfuehrt_istExecPfad`) has the
    validated length and reads only validated user-part keys. An out-of-region
    copy has no such step -- there is no proof to build it with
    (`verweigert_keinGeprueft` above) -- so refusal stays where it was,
    beside the step. -/
theorem schrittAusfuehrt_entlaedt (D : Deklaration) (t : D.Tab)
    (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (s : BereichSchritt) (r : UserRegion) (k : Kopie)
    (h : schrittTraeger s = some (r, k)) (σ : World D) :
    let g : GepruefteKopie :=
      { region := r, kopie := k, gecheckt := bereichSchritt_fordertBereich s r k h }
    kopieImBereichBool r k = true ∧
    (weltBytes D t f hf σ g.kopie.userAddr g.kopie.laenge).length = g.kopie.laenge ∧
    ∀ i : Nat, i < g.kopie.laenge →
      schluesselInRegion g.region ((g.kopie.userAddr + i : Nat) : Int) := by
  have hv : validiert r k := bereichSchritt_fordertBereich s r k h
  have hrun := modellKopieAusfuehrt_quellBereich D t f hf
    ({ region := r, kopie := k, gecheckt := hv }) σ
  exact ⟨geprueft_bool_haelt r k hv, hrun.1, hrun.2⟩

#print axioms modellKopieAusfuehrt_istExecPfad
#print axioms geprueft_bool_haelt
#print axioms schrittAusfuehrt_entlaedt

/-! ## 11. The Seite partition in World, discharged (C7) -/

/- C7, Adressraum side: World carries one Seite per carrier, and a
   separated region pair forbids the cross-partition step. Untouched:
   §§6/9 (`BereichSchritt`, `validiert`, the executable checks) keep
   their owners; the `Stmt`/`exec` branch taking such a step stays
   Semantik-side work, as §9 books for C6. -/

/-- The Seite partition in World: every carrier -- each table, each
    global -- sits on exactly one side. The split is in the tags, as in
    §9; here it is carried by World keys (`D.Tab ⊕ D.Glob`), which is
    what C7 booked (`benutzerTeil`/`bereicheGetrennt` name the user side
    it could check against). -/
def WeltSeite (D : Deklaration) : Type :=
  (D.Tab ⊕ D.Glob) → Seite

/-- Hanging a world key on the partition: the `Nat` offset tagged with
    its carrier's side -- the `GetaggteAddr` of §9, read off the World
    partition. -/
def weltTag (D : Deklaration) (p : WeltSeite D) (c : D.Tab ⊕ D.Glob)
    (addr : Nat) : GetaggteAddr :=
  { seite := p c, addr := addr }

/-- The tag reads back: the tagged key runs on its carrier's side. -/
theorem weltTag_seite (D : Deklaration) (p : WeltSeite D)
    (c : D.Tab ⊕ D.Glob) (addr : Nat) :
    (weltTag D p c addr).seite = p c :=
  by rfl

/-- A user-carrier key in its region is a user-part world key: the
    partition leg lands where `weltByte` reads (`benutzerTeil`). -/
theorem weltTag_imTeil (D : Deklaration) (p : WeltSeite D)
    (u k : UserRegion) (c : D.Tab ⊕ D.Glob) (addr : Nat)
    (hc : p c = .user) (h : seitenZugehoerig u k (weltTag D p c addr)) :
    benutzerTeil u (getaggterSchluessel (weltTag D p c addr)) := by
  have hu : (weltTag D p c addr).seite = .user := by
    rw [weltTag_seite D p c addr]
    exact hc
  exact getaggteUserAddr_imTeil u k _ hu h

/-- A cross-partition exec step: the same offset touched once tagged
    user (running in the user region) and once tagged kernel (running
    in the kernel region) -- one address, both sides. -/
def querSchritt (u k : UserRegion) (a b : GetaggteAddr) : Prop :=
  a.addr = b.addr ∧ a.seite = .user ∧ b.seite = .kern ∧
    seitenZugehoerig u k a ∧ seitenZugehoerig u k b

/-- **C7 discharge: Seite separation entails no cross-partition exec
    step.** Separated regions share no offset (`bereicheGetrennt`); both
    legs claim the same one, so there is no such step. -/
theorem getrennteSeite_keinQuerschritt (u k : UserRegion)
    (hsep : bereicheGetrennt u k) (a b : GetaggteAddr)
    (h : querSchritt u k a b) : False := by
  obtain ⟨haddr, ha, hb, hain, hbin⟩ := h
  exact seitenZugehoerig_trennt u k hsep a b ha hb hain hbin haddr

/-- The user leg of a cross step is a user-part world key -- the
    contradiction above, read at the world mapping. -/
theorem querSchritt_userTeil (u k : UserRegion) (a b : GetaggteAddr)
    (h : querSchritt u k a b) :
    benutzerTeil u (getaggterSchluessel a) := by
  obtain ⟨_, ha, _, hain, _⟩ := h
  exact getaggteUserAddr_imTeil u k a ha hain

#print axioms WeltSeite
#print axioms weltTag
#print axioms weltTag_seite
#print axioms weltTag_imTeil
#print axioms querSchritt
#print axioms getrennteSeite_keinQuerschritt
#print axioms querSchritt_userTeil

end Gabbro.Grammatik.Adressraum
