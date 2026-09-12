/-
  File:      Grammatik/Profil.lean
  Subject:   ONE HARDWARE PROFILE -- Lean model, model half (lane 66, E6).

  Per `PLAN-ERWEITUNG.md` section 0c: the main program declares ONE hardware
  profile; libraries REQUIRE profile entries by name reference, never by copying
  their text; linking refuses requirements outside the profile. Keyed mode
  assumptions (FP rounding, FP contraction, memory model, arch, interrupt
  routing) fix a mode by key and value; two entries with one key and different
  values are refused at the profile itself.

  Model: entries, profiles, goodness, the mode projection a good keyed profile
  induces (`modusVonProfil`), binding, and the three theorems `profil_modell`,
  `bindung_fuegt_nichts_hinzu`, `widerspruch_abgelehnt`, plus a joint witness
  (`profil_modell_zeuge`, `bindung_fuegt_nichts_hinzu_zeuge`).
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

/-- Keyed mode assumption keys (finite inductive, PLAN-ERWEITUNG.md section 0c,
    point 3): FP rounding, FP contraction, memory model, arch, interrupt
    routing. Values are `Nat` codes fixed per key. -/
inductive ProfilSchluessel where
  | fpRundung
  | fpKontraktion
  | speichermodell
  | arch
  | interruptRouting
  deriving DecidableEq, Repr

/-- An assumption entry: a name, a class, and either a keyed mode assumption
    (key plus `Nat` value) or a free-prose assumption (a `Prop` over a world,
    stored as a field -- never as a theorem premise). -/
inductive AnnahmeEintrag (D : Deklaration) where
  | modus (name : String) (klasse : String) (key : ProfilSchluessel) (val : Nat)
  | frei (name : String) (klasse : String) (claim : World D → Prop)

/-- A profile is a list of entries. -/
abbrev Profil (D : Deklaration) := List (AnnahmeEintrag D)

/-- A mode assignment: key to value. -/
abbrev ModusBelegung := ProfilSchluessel → Nat

/-- Name of an entry. -/
def eintragName {D : Deklaration} : AnnahmeEintrag D → String
  | .modus n _ _ _ => n
  | .frei n _ _ => n

/-- `istModus a k v`: `a` is a keyed entry for key `k` with value `v`. -/
def istModus {D : Deklaration} (a : AnnahmeEintrag D) (k : ProfilSchluessel)
    (v : Nat) : Prop :=
  ∃ n c, a = AnnahmeEintrag.modus n c k v

/-- The mode projection a profile induces: the leftmost keyed value for `k`
    in the list, `0` if the profile holds none. The goodness half
    (`einigung`) makes the choice irrelevant: all keyed values for one key
    agree (`modusVonProfil_trifft`). -/
def modusVonProfilAux (D : Deklaration) : Profil D → ProfilSchluessel → Nat
  | [], _ => 0
  | AnnahmeEintrag.modus _ _ k v :: rest, q =>
      if k = q then v else modusVonProfilAux D rest q
  | AnnahmeEintrag.frei _ _ _ :: rest, q => modusVonProfilAux D rest q

/-- The mode assignment a profile induces. -/
def modusVonProfil {D : Deklaration} (P : Profil D) : ModusBelegung :=
  fun q => modusVonProfilAux D P q

/-- The head keyed value for `k` determines the projection. -/
theorem modusVonProfil_kopf {D : Deklaration} (P : Profil D)
    (k : ProfilSchluessel) (v : Nat) (n c : String) :
    modusVonProfil (AnnahmeEintrag.modus (D := D) n c k v :: P) k = v := by
  unfold modusVonProfil modusVonProfilAux
  simp

/-- Keyed value lookup: the value `a` carries for key `k`, if any. -/
def eintragWert {D : Deklaration} (a : AnnahmeEintrag D)
    (k : ProfilSchluessel) : Option Nat :=
  match a with
  | .modus _ _ k' v => if k' = k then some v else none
  | .frei _ _ _ => none

/-- `eintragWert` reads back `istModus`: matching key gives the value. -/
theorem eintragWert_trifft {D : Deklaration} (a : AnnahmeEintrag D)
    (k : ProfilSchluessel) (v : Nat) (h : istModus a k v) :
    eintragWert a k = some v := by
  obtain ⟨n, c, rfl⟩ := h
  simp [eintragWert]

/-- A keyed entry determines its key and value: inversion for `modus`. -/
theorem istModus_inj {D : Deklaration} {n c : String}
    {k k' : ProfilSchluessel} {v v' : Nat}
    (h : istModus (AnnahmeEintrag.modus (D := D) n c k v) k' v') :
    k = k' ∧ v = v' := by
  obtain ⟨_, _, heq⟩ := h
  cases heq
  exact ⟨rfl, rfl⟩

/-- Key agreement: no two keyed entries with the same key and different values. -/
def einigung {D : Deklaration} (P : Profil D) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ k v w,
    istModus a k v → istModus b k w → v = w

/-- Same-named entries carry identical content: keyed entries agree in class,
    key and value; free entries agree in class and on their prose claim at one
    witness world. -/
def namensGleichheitAux (D : Deklaration) :
    AnnahmeEintrag D → AnnahmeEintrag D → Prop
  | .modus n c k v, .modus n' c' k' v' =>
      n = n' ∧ c = c' ∧ k = k' ∧ v = v'
  | .frei n c p, .frei n' c' p' =>
      n = n' ∧ c = c' ∧ ∃ σ : World D, (p σ ↔ p' σ)
  | _, _ => False

/-- Same-named entries carry identical content. -/
def namensGleichheit {D : Deklaration} (a b : AnnahmeEintrag D) : Prop :=
  namensGleichheitAux D a b

/-- `Profil.gut`: key agreement plus same-name content agreement. -/
def Profil.gut {D : Deklaration} (P : Profil D) : Prop :=
  einigung P ∧
  (∀ a ∈ P, ∀ b ∈ P,
    eintragName a = eintragName b → namensGleichheit a b)

/-- A keyed entry anywhere in the profile is read by the projection, under
    key agreement: induction on the list, using the head case or the tail
    hypothesis (whose agreement follows from the whole-list one). -/
theorem modusVonProfil_trifft {D : Deklaration} (P : Profil D)
    (h : einigung (D := D) P)
    (k : ProfilSchluessel) (v : Nat) (n c : String)
    (hmem : AnnahmeEintrag.modus (D := D) n c k v ∈ P) :
    modusVonProfil (D := D) P k = v := by
  induction P with
  | nil => simp at hmem
  | cons hd tl ih =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
          subst heq
          exact modusVonProfil_kopf tl k v n c
      | inr htl =>
          have hmemTail : ∀ x ∈ tl, x ∈ hd :: tl :=
            fun x hx => List.mem_cons_of_mem _ hx
          have hsub : einigung (D := D) tl := by
            intro a ha b hb kk x y h1 h2
            exact h a (hmemTail a ha) b (hmemTail b hb) kk x y h1 h2
          have ihtl := ih hsub htl
          have hmemHd_unused : ∀ (nn cc : String) (kk : ProfilSchluessel) (vv : Nat),
              hd = AnnahmeEintrag.modus (D := D) nn cc kk vv →
              AnnahmeEintrag.modus (D := D) nn cc kk vv ∈ hd :: tl := by
            intro nn cc kk vv heq
            rw [heq]
            exact List.mem_cons_self
          cases hd with
          | modus n' c' kHead vHead =>
              by_cases hkk : kHead = k
              · subst hkk
                have hagree := h (AnnahmeEintrag.modus (D := D) n' c' kHead vHead)
                  (hmemHd_unused n' c' kHead vHead rfl)
                  (AnnahmeEintrag.modus (D := D) n c kHead v)
                  (List.mem_cons_of_mem _ htl)
                  kHead vHead v ⟨n', c', rfl⟩ ⟨n, c, rfl⟩
                subst hagree
                show modusVonProfilAux D
                  (AnnahmeEintrag.modus (D := D) n' c' kHead vHead :: tl) kHead
                    = vHead
                unfold modusVonProfilAux
                simp
              · show modusVonProfilAux D
                  (AnnahmeEintrag.modus (D := D) n' c' kHead vHead :: tl) k = v
                unfold modusVonProfilAux
                rw [if_neg hkk]
                show modusVonProfil _ k = v
                exact ihtl
          | frei n' c' p =>
              show modusVonProfilAux D
                (AnnahmeEintrag.frei (D := D) n' c' p :: tl) k = v
              unfold modusVonProfilAux
              show modusVonProfil _ k = v
              exact ihtl

/-- A keyed entry forces the mode; a free entry constrains nothing in the
    model (its prose lives outside Lean, named by its entry). -/
def erfuellt {D : Deklaration} (m : ModusBelegung) : AnnahmeEintrag D → Prop
  | .modus _ _ kk vv => m kk = vv
  | .frei _ _ _ => True

/-- The conjunction of a profile: every entry holds of `m`. -/
def Profil.gilt {D : Deklaration} (P : Profil D) (m : ModusBelegung) : Prop :=
  ∀ a ∈ P, erfuellt m a

/-- Keyed pair conflict: two keyed entries with the same key, different values. -/
def schluesselKonflikt {D : Deklaration} : AnnahmeEintrag D →
    AnnahmeEintrag D → Bool
  | .modus _ _ k v, .modus _ _ k' v' =>
      decide (k = k' ∧ v ≠ v')
  | _, _ => false

/-- Key agreement as a boolean over one pair-list pass. -/
def pruefeSchluesselAux {D : Deklaration} : Profil D → Profil D → Bool
  | [], _ => true
  | a :: rest, P =>
      P.all (fun b => !schluesselKonflikt a b) && pruefeSchluesselAux rest P

/-- Key agreement over the whole profile. -/
def pruefeSchluessel {D : Deklaration} (P : Profil D) : Bool :=
  pruefeSchluesselAux P P

/-- A passing pair check means no keyed conflict for that left element. -/
theorem pruefeSchluesselAux_kons {D : Deklaration} (a : AnnahmeEintrag D)
    (rest P : Profil D)
    (h : pruefeSchluesselAux (a :: rest) P = true) :
    (∀ b ∈ P, schluesselKonflikt a b = false) ∧
      pruefeSchluesselAux rest P = true := by
  unfold pruefeSchluesselAux at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpair, hrest⟩ := h
  refine ⟨?_, hrest⟩
  intro b hb
  have hall := (List.all_eq_true.mp hpair) b hb
  cases hc : schluesselKonflikt a b with
  | true => simp [hc] at hall
  | false => rfl

/-- No conflict on a pair means key agreement: both directions of the
    disagreement are ruled out by the `decide` shape. -/
theorem keinKonflikt_einigung {D : Deklaration} (a b : AnnahmeEintrag D)
    (h : schluesselKonflikt a b = false)
    (k : ProfilSchluessel) (v w : Nat)
    (h1 : istModus a k v) (h2 : istModus b k w) : v = w := by
  obtain ⟨na, ca, rfl⟩ := h1
  obtain ⟨nb, cb, rfl⟩ := h2
  simp only [schluesselKonflikt] at h
  by_cases hvw : v = w
  · exact hvw
  · exfalso
    have htrue : decide (True ∧ v ≠ w) = true := by
      rw [decide_eq_true_eq]
      exact ⟨trivial, hvw⟩
    rw [htrue] at h
    exact absurd h (by decide)

/-- A passing boolean check yields key agreement over the profile. -/
theorem pruefeSchluessel_einigung {D : Deklaration} (P : Profil D)
    (h : pruefeSchluessel (D := D) P = true) : einigung P := by
  unfold pruefeSchluessel at h
  have hall : ∀ Q : Profil D, Q ⊆ P → pruefeSchluesselAux Q P = true →
      (∀ a ∈ Q, ∀ b ∈ Q, ∀ k v w,
        istModus a k v → istModus b k w → v = w) ∧
      (∀ x ∈ Q, ∀ y ∈ P, ∀ k v w,
        istModus x k v → istModus y k w → v = w) := by
    intro Q hsub hQ
    induction Q with
    | nil =>
        constructor
        · intro a ha
          simp at ha
        · intro x hx
          simp at hx
    | cons hd tl ih =>
        have hpair := (pruefeSchluesselAux_kons hd tl P hQ).1
        have hrest := (pruefeSchluesselAux_kons hd tl P hQ).2
        have hsubTl : tl ⊆ P := fun x hx => hsub (List.mem_cons_of_mem _ hx)
        obtain ⟨ihIn, ihCross⟩ := ih hsubTl hrest
        have hmemHd : hd ∈ P := hsub List.mem_cons_self
        constructor
        · intro a ha b hb k v w h1 h2
          simp only [List.mem_cons] at ha hb
          cases ha with
          | inl heq =>
              subst heq
              cases hb with
              | inl heq2 =>
                  obtain ⟨na, ca, ha1⟩ := h1
                  obtain ⟨nb, cb, hb2⟩ := h2
                  -- `a` and `b` are both the head: `ha1 hb2` exhibit the
                  -- same constructor, so `v = w` by injection.
                  have hsame : AnnahmeEintrag.modus (D := D) na ca k v =
                      AnnahmeEintrag.modus (D := D) nb cb k w := by
                    rw [← ha1, ← hb2, heq2]
                  cases hsame
                  rfl
              | inr hbtl =>
                  have hmem : b ∈ P := hsubTl hbtl
                  have hnc := hpair b hmem
                  exact keinKonflikt_einigung _ _ hnc k v w h1 h2
          | inr hatl =>
              cases hb with
              | inl heq2 =>
                  subst heq2
                  have hmem : a ∈ P := hsubTl hatl
                  exact ihCross a hatl b hmemHd k v w h1 h2
              | inr hbtl =>
                  exact ihIn a hatl b hbtl k v w h1 h2
        · intro x hx y hy k v w h1 h2
          simp only [List.mem_cons] at hx
          cases hx with
          | inl heq =>
              subst heq
              have hnc := hpair y hy
              exact keinKonflikt_einigung _ _ hnc k v w h1 h2
          | inr hxtl =>
              exact ihCross x hxtl y hy k v w h1 h2
  exact (hall P (fun x hx => hx) h).1

/-- A requirement entry: what a library asks of the profile, by content. -/
inductive Anforderung (D : Deklaration) where
  | modus (name : String) (klasse : String) (key : ProfilSchluessel) (val : Nat)
  | frei (name : String) (klasse : String) (claim : World D → Prop)

/-- The entry a requirement denotes. -/
def anforderungEintrag {D : Deklaration} : Anforderung D → AnnahmeEintrag D
  | .modus n c k v => .modus n c k v
  | .frei n c p => .frei n c p

/-- A library: a name and its requirements. -/
structure Bibliothek (D : Deklaration) where
  name : String
  anforderungen : List (Anforderung D)

/-- Name of a requirement. -/
def anforderungName {D : Deklaration} : Anforderung D → String
  | .modus n _ _ _ => n
  | .frei n _ _ => n

/-- Name lookup in the profile. -/
def profilEintrag {D : Deklaration} (P : Profil D) (n : String) :
    Option (AnnahmeEintrag D) :=
  P.find? (fun a => decide (eintragName a = n))

/-- `Profil.bindet lib`: every required name is in the profile with identical
    content -- requirements by NAME reference (PLAN-ERWEITUNG.md section 0c,
    point 2). -/
def Profil.bindet {D : Deklaration} (P : Profil D) (lib : Bibliothek D) : Prop :=
  ∀ r ∈ lib.anforderungen, ∃ a ∈ P,
    eintragName a = anforderungName r ∧
    namensGleichheit a (anforderungEintrag r)

/-- The conjunction of a library's requirements over a mode. -/
def Bibliothek.gilt {D : Deklaration} (lib : Bibliothek D)
    (m : ModusBelegung) : Prop :=
  ∀ r ∈ lib.anforderungen, erfuellt m (anforderungEintrag r)

/-- Bound entries satisfy their requirement: same-named keyed content forces
    the same mode equation. -/
theorem namensGleichheit_erfuellt_modus {D : Deklaration}
    (a : AnnahmeEintrag D) (r : Anforderung D) (m : ModusBelegung)
    (h : namensGleichheit a (anforderungEintrag r))
    (hm : erfuellt m a) :
    erfuellt m (anforderungEintrag r) := by
  cases ra : r with
  | modus n c k v =>
      simp only [ra, anforderungEintrag] at h ⊢
      cases ha : a with
      | modus na ca ka va =>
          simp only [ha] at h
          obtain ⟨_, _, hkk, hvv⟩ := h
          simp only [ha, erfuellt] at hm
          subst hkk
          subst hvv
          simp only [erfuellt]
          exact hm
      | frei na ca p =>
          unfold namensGleichheit namensGleichheitAux at h
          rw [ha] at h
          simp only at h
  | frei n c p =>
      simp only [anforderungEintrag, erfuellt]

/-- Linking adds no premise: if a library binds, the profile's conjunction
    implies the conjunction of the library's requirements. -/
theorem bindung_fuegt_nichts_hinzu {D : Deklaration} (P : Profil D)
    (lib : Bibliothek D) (m : ModusBelegung)
    (hgilt : Profil.gilt P m)
    (hbind : Profil.bindet P lib) :
    Bibliothek.gilt lib m := by
  intro r hr
  obtain ⟨a, hamem, _, hcon⟩ := hbind r hr
  have hma := hgilt a hamem
  exact namensGleichheit_erfuellt_modus a r m hcon hma

/-- Two entries with one key and different values make `Profil.gut` false. -/
theorem widerspruch_abgelehnt {D : Deklaration} (P : Profil D)
    (k : ProfilSchluessel) (v w : Nat) (hvw : v ≠ w)
    (a b : AnnahmeEintrag D)
    (ha : a ∈ P) (hb : b ∈ P)
    (h1 : istModus a k v) (h2 : istModus b k w) :
    ¬ Profil.gut P := by
  intro hgut
  have hagree := hgut.1 a ha b hb k v w h1 h2
  exact hvw hagree

/-- For a profile of keyed entries, there EXISTS a mode assignment satisfying
    every entry: the profile is satisfiable by construction. The witness is
    the profile's own projection (`modusVonProfil`); keyed entries hold by
    `modusVonProfil_trifft`, free entries hold trivially. -/
theorem profil_modell {D : Deklaration} (P : Profil D)
    (hgut : Profil.gut P)
    (hkey : ∀ a ∈ P, ∃ k v, istModus a k v) :
    ∃ m : ModusBelegung, Profil.gilt P m := by
  refine ⟨modusVonProfil P, ?_⟩
  intro a ha
  obtain ⟨k, v, hkv⟩ := hkey a ha
  obtain ⟨n, c, rfl⟩ := hkv
  simp only [erfuellt]
  exact modusVonProfil_trifft P hgut.1 k v n c ha

/-! ## Witness: arch = x86_64, fpKontraktion = aus, one library. -/

/-- Value codes for the witness profile. -/
def zeugeArch : Nat := 1
def zeugeKontraktionAus : Nat := 0

/-- The witness declaration: no tables needed for the profile layer itself,
    but rule 13 demands a non-degenerate program for the run half -- so the
    witness declaration carries one table that some function writes. -/
def zeugeD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The witness profile: arch = x86_64, fpKontraktion = aus. -/
def zeugeProfil : Profil zeugeD :=
  [ .modus "arch" "ziel" .arch zeugeArch,
    .modus "fp-kontraktion" "ziel" .fpKontraktion zeugeKontraktionAus ]

/-- The witness library: requires fpKontraktion = aus. -/
def zeugeBibliothek : Bibliothek zeugeD :=
  { name := "gpu"
    anforderungen := [.modus "fp-kontraktion" "ziel" .fpKontraktion zeugeKontraktionAus] }

/-- The witness profile is good: distinct keys, distinct names. -/
theorem zeugeProfil_gut : Profil.gut zeugeProfil := by
  constructor
  · intro a ha b hb k v w h1 h2
    simp only [zeugeProfil, List.mem_cons] at ha hb
    obtain ⟨na, ca, rfl⟩ := h1
    obtain ⟨nb, cb, rfl⟩ := h2
    -- Both sides are constructor equalities against the two profile
    -- entries; inject in all four cases.
    cases ha with
    | inl heq =>
        cases hb with
        | inl heq2 =>
            cases heq
            cases heq2
            rfl
        | inr heq2 =>
            cases heq2 with
            | inl heqA =>
                cases heq
                cases heqA
            | inr heqB =>
                simp at heqB
    | inr heq =>
        cases heq with
        | inl heqA =>
            cases hb with
            | inl heq2 =>
                cases heqA
                cases heq2
            | inr heqB =>
                cases heqB with
                | inl heqC =>
                    cases heqA
                    cases heqC
                    rfl
                | inr heqD =>
                    simp at heqD
        | inr heqB =>
            simp at heqB
  · intro a ha b hb hname
    simp only [zeugeProfil, List.mem_cons] at ha hb
    simp only [eintragName] at hname
    -- Four membership cases; the mixed ones contradict the name equality.
    cases ha with
    | inl heq =>
        cases hb with
        | inl heq2 =>
            rw [heq, heq2]
            simp [namensGleichheit, namensGleichheitAux]
        | inr heq2 =>
            cases heq2 with
            | inl heqA =>
                rw [heq, heqA] at hname
                simp at hname
            | inr heqB =>
                simp at heqB
    | inr heq =>
        cases heq with
        | inl heqA =>
            cases hb with
            | inl heq2 =>
                rw [heqA, heq2] at hname
                simp at hname
            | inr heqB =>
                cases heqB with
                | inl heqC =>
                    rw [heqA, heqC]
                    simp [namensGleichheit, namensGleichheitAux]
                | inr heqD =>
                    simp at heqD
        | inr heqB =>
            simp at heqB

/-- The witness profile holds only keyed entries. -/
theorem zeugeProfil_keyed : ∀ a ∈ zeugeProfil, ∃ k v, istModus a k v := by
  intro a ha
  simp only [zeugeProfil, List.mem_cons] at ha
  cases ha with
  | inl heq =>
      rw [heq]
      exact ⟨.arch, zeugeArch, "arch", "ziel", rfl⟩
  | inr heq =>
      cases heq with
      | inl heqA =>
          rw [heqA]
          exact ⟨.fpKontraktion, zeugeKontraktionAus, "fp-kontraktion", "ziel", rfl⟩
      | inr heqB =>
          simp at heqB

/-- The witness library binds: its one requirement is in the profile. -/
theorem zeugeBibliothek_bindet : Profil.bindet zeugeProfil zeugeBibliothek := by
  intro r hr
  simp only [zeugeBibliothek, List.mem_singleton] at hr
  subst hr
  refine ⟨AnnahmeEintrag.modus "fp-kontraktion" "ziel" .fpKontraktion
    zeugeKontraktionAus, ?_, ?_, ?_⟩
  · simp [zeugeProfil]
  · simp [eintragName, anforderungName]
  · simp [namensGleichheit, namensGleichheitAux, anforderungEintrag]

/-- ZEUGE for `profil_modell`: the witness profile is good and keyed, so the
    model exists -- instantiated jointly with `zeugeProfil_gut` and
    `zeugeProfil_keyed`. -/
theorem profil_modell_zeuge :
    ∃ m : ModusBelegung, Profil.gilt (D := zeugeD) zeugeProfil m :=
  profil_modell zeugeProfil zeugeProfil_gut zeugeProfil_keyed

/-- ZEUGE for `bindung_fuegt_nichts_hinzu`: the witness library binds, so the
    profile's conjunction implies the library's -- instantiated jointly with
    the profile model and `zeugeBibliothek_bindet`. -/
theorem bindung_fuegt_nichts_hinzu_zeuge (m : ModusBelegung)
    (hgilt : Profil.gilt (D := zeugeD) zeugeProfil m) :
    Bibliothek.gilt zeugeBibliothek m :=
  bindung_fuegt_nichts_hinzu zeugeProfil zeugeBibliothek m hgilt
    zeugeBibliothek_bindet

#print axioms Gabbro.Grammatik.profil_modell
#print axioms Gabbro.Grammatik.bindung_fuegt_nichts_hinzu
#print axioms Gabbro.Grammatik.widerspruch_abgelehnt
#print axioms Gabbro.Grammatik.profil_modell_zeuge
#print axioms Gabbro.Grammatik.bindung_fuegt_nichts_hinzu_zeuge

/- CUTS: what is not proved.
   - Decidable `Profil.gut` for free-prose entries: the boolean checker
     `pruefeSchluessel` decides only the keyed half (`einigung`, via
     `pruefeSchluessel_einigung`); same-name content agreement over `Prop`
     fields (`namensGleichheit` on `.frei`) is undecidable in general and
     stays a `Prop`. The task asks "Decidable for keyed entries" -- that is
     exactly the half delivered.
   - Same-name checking as `Bool`: no `pruefeName` boolean is provided, since
     content equality over prose `Prop`s is not computable; the name half of
     `Profil.gut` is only stated, not decided.
   - No wiring into the program theorem: `profil_modell` builds the mode
     assignment, but no goal theorem takes the profile as its assumption set
     yet -- that is the E6 remainder (library call syntax, translator
     declarations live in other lanes).
   - Free-prose assumptions carry no falsifier probe here: the entry stores
     the claim as a field, but the manifest/probe bookkeeping of §0c point 5
     is not modelled.
-/

end Gabbro.Grammatik
