/-
  File:      Grammatik/Gen/Abdeckung/ZellenSatz.lean
  Subject:   THE CELLS ARE THE CHECKER, as theorems (step 1 of making M and N complete in the sense of Theorem 4):
             for every program, the verdict recomputed from the cells of a component (`urteilAusZellen`) IS the
             component of the Lean model's Bool (`komp`). Until now this was only evaluated on generated programs
             (`zellenStimmen`); here it is proved for all of them, one component at a time.

  Hypotheses: the member lists are complete (`hvoll`: every function, `hls`: every lock, `hcs`: every carrier), as in
  `akzeptiert_iff`. All ten components are proved here (`urteil_0` .. `urteil_9`), and `akzeptiertX_zellen` puts them together.
-/
import Grammatik.Gen.Abdeckung.Zellen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-- A cell of a verdict kind is bad exactly when its test fails. -/
theorem schlecht_urteil {k a : Nat} {v : List Bool} :
    (Zelle.mk k a true v).schlecht = !(Zelle.mk k a true v).kern := by
  simp [Zelle.schlecht]

/-- **Component 5 (roots)**: the cells decide it. -/
theorem urteil_5 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 5 = komp P S fs ls cs ws 5 := by
  simp only [urteilAusZellen, zellen, komp, wurzelnB, List.all_map, Function.comp_def, Zelle.schlecht,
    Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]

/-- **Component 4 (lock sites)**: the cells decide it, over a complete list of carriers. -/
theorem urteil_4 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    urteilAusZellen P S fs ls cs ws 4 = komp P S fs ls cs ws 4 := by
  simp only [urteilAusZellen, zellen, komp, sperrOrteB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h L hL c hc
    rcases h L hL c (hcs c) with h1 | h1
    · rw [istIn_iff.mpr hc] at h1; cases h1
    · exact h1
  · intro h L hL c _
    cases hi : istIn (S.orte L) c
    · exact Or.inl rfl
    · exact Or.inr (h L hL c (istIn_iff.mp hi))

/-! ## `mE` is a conjunction over the sites of a body -/

/-- The conjunction of two feature sets. -/
def _root_.Gabbro.Grammatik.Merkmal.und (A B : Merkmal D) : Merkmal D :=
  ⟨fun g => A.ruf g && B.ruf g, fun n => A.ind n && B.ind n, fun L => A.sperre L && B.sperre L⟩

@[simp] theorem Merkmal.und_ruf (A B : Merkmal D) (g : D.Fn) : (A.und B).ruf g = (A.ruf g && B.ruf g) := rfl
@[simp] theorem Merkmal.und_ind (A B : Merkmal D) (n : Nat) : (A.und B).ind n = (A.ind n && B.ind n) := rfl
@[simp] theorem Merkmal.und_sperre (A B : Merkmal D) (L : D.Lock) :
    (A.und B).sperre L = (A.sperre L && B.sperre L) := rfl

mutual

theorem mS_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → mS (A.und B) s = (mS A s && mS B s)
  | .ite _ t e => by
      simp only [mS, mB_und A B t, mB_und A B e, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .onOption _ p a => by
      simp only [mS, mB_und A B p, mB_und A B a, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .onTag _ arms => by simp only [mS, mArms_und A B arms]
  | .onWhy _ arms => by simp only [mS, mGArms_und A B arms]
  | .call .. => by simp only [mS, Merkmal.und_ruf]
  | .callInd .. => by simp only [mS, Merkmal.und_ind]
  | .locks L _ body => by
      simp only [mS, mB_und A B body, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .breaking _ body => by simp only [mS, mB_und A B body]
  | .traverse _ _ body => by simp only [mS, mB_und A B body]
  | .retry _ _ body ueber => by
      simp only [mS, mB_und A B body, mB_und A B ueber, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .forever _ _ body => by simp only [mS, mB_und A B body]
  | .assignSlot .. => rfl
  | .assignThru .. => rfl
  | .assignGlob .. => rfl
  | .putBytes .. => rfl
  | .assignVar .. => rfl
  | .shift .. => rfl
  | .axiomCall .. => rfl
  | .regWrite .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .advances .. => rfl
  | .retires .. => rfl
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

theorem mB_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → mB (A.und B) b = (mB A b && mB B b)
  | .nil => rfl
  | .cons s rest => by
      simp only [mB, mS_und A B s, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bind _ rest => by simp only [mB, mB_und A B rest]
  | .bindCall g _ _ _ _ rest => by
      simp only [mB, mB_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindCallInd _ _ _ _ _ rest => by
      simp only [mB, mB_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindCallElse g _ _ _ _ err rest => by
      simp only [mB, mE_und A B err, mB_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [mB, mE_und A B err, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .regRead _ _ rest => by simp only [mB, mB_und A B rest]
  | .regReadElse _ _ _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .awaits _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .exchange _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .narrow _ _ _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .check _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .float _ _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .floatLit _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .floatOf _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .floatNarrow _ _ _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem mArms_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : (a : Arms D V l Γ Λ Λ' cs) → mArms (A.und B) a = (mArms A a && mArms B a)
  | .nil => rfl
  | .cons b rest => by
      simp only [mArms, mB_und A B b, mArms_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem mGArms_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → mGArms (A.und B) a = (mGArms A a && mGArms B a)
  | .nil => rfl
  | .cons b rest => by
      simp only [mGArms, mB_und A B b, mGArms_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem mE_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → mE (A.und B) e = (mE A e && mE B e)
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .cons s rest => by
      simp only [mE, mS_und A B s, mE_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bind _ rest => by simp only [mE, mE_und A B rest]
  | .bindCall g _ _ _ _ rest => by
      simp only [mE, mE_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindCallElse g _ _ _ _ err rest => by
      simp only [mE, mE_und A B err, mE_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mE, mE_und A B rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [mE, mE_und A B err, mE_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

end

/-! ## The trivial feature set, finite conjunctions -/

/-- The feature set that admits everything. -/
def _root_.Gabbro.Grammatik.Merkmal.top : Merkmal D := ⟨fun _ => true, fun _ => true, fun _ => true⟩

mutual

theorem mS_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → mS Merkmal.top s = true
  | .ite _ t e => by simp only [mS, mB_top t, mB_top e, Bool.and_self]
  | .onOption _ p a => by simp only [mS, mB_top p, mB_top a, Bool.and_self]
  | .onTag _ arms => by simp only [mS, mArms_top arms]
  | .onWhy _ arms => by simp only [mS, mGArms_top arms]
  | .call .. => rfl
  | .callInd .. => rfl
  | .locks _ _ body => by simp only [mS, mB_top body]; rfl
  | .breaking _ body => by simp only [mS, mB_top body]
  | .traverse _ _ body => by simp only [mS, mB_top body]
  | .retry _ _ body ueber => by simp only [mS, mB_top body, mB_top ueber, Bool.and_self]
  | .forever _ _ body => by simp only [mS, mB_top body]
  | .assignSlot .. => rfl
  | .assignThru .. => rfl
  | .assignGlob .. => rfl
  | .putBytes .. => rfl
  | .assignVar .. => rfl
  | .shift .. => rfl
  | .axiomCall .. => rfl
  | .regWrite .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .advances .. => rfl
  | .retires .. => rfl
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

theorem mB_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → mB Merkmal.top b = true
  | .nil => rfl
  | .cons s rest => by simp only [mB, mS_top s, mB_top rest, Bool.and_self]
  | .bind _ rest => by simp only [mB, mB_top rest]
  | .bindCall _ _ _ _ _ rest => by simp only [mB, mB_top rest]; rfl
  | .bindCallInd _ _ _ _ _ rest => by simp only [mB, mB_top rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [mB, mE_top err, mB_top rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [mB, mE_top err, mB_top rest, Bool.and_self]
  | .regRead _ _ rest => by simp only [mB, mB_top rest]
  | .regReadElse _ _ _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]
  | .awaits _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .exchange _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .narrow _ _ _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]
  | .check _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]
  | .float _ _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .floatLit _ _ _ rest => by simp only [mB, mB_top rest]
  | .floatOf _ _ _ rest => by simp only [mB, mB_top rest]
  | .floatNarrow _ _ _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]

theorem mArms_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → mArms Merkmal.top a = true
  | .nil => rfl
  | .cons b rest => by simp only [mArms, mB_top b, mArms_top rest, Bool.and_self]

theorem mGArms_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → mGArms Merkmal.top a = true
  | .nil => rfl
  | .cons b rest => by simp only [mGArms, mB_top b, mGArms_top rest, Bool.and_self]

theorem mE_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → mE Merkmal.top e = true
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .cons s rest => by simp only [mE, mS_top s, mE_top rest, Bool.and_self]
  | .bind _ rest => by simp only [mE, mE_top rest]
  | .bindCall _ _ _ _ _ rest => by simp only [mE, mE_top rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [mE, mE_top err, mE_top rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mE, mE_top rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [mE, mE_top err, mE_top rest, Bool.and_self]

end

/-- The conjunction of a list of feature sets. -/
def _root_.Gabbro.Grammatik.Merkmal.alle (As : List (Merkmal D)) : Merkmal D := As.foldr Merkmal.und Merkmal.top

theorem mE_alle (As : List (Merkmal D)) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) : mE (Merkmal.alle As) e = As.all fun A => mE A e := by
  induction As with
  | nil => exact mE_top e
  | cons A rest ih =>
    show mE (A.und (Merkmal.alle rest)) e = _
    rw [mE_und, ih]
    rfl

theorem Merkmal.gleich {A B : Merkmal D} (h1 : ∀ g, A.ruf g = B.ruf g) (h2 : ∀ n, A.ind n = B.ind n)
    (h3 : ∀ L, A.sperre L = B.sperre L) : A = B := by
  cases A; cases B
  simp only [Merkmal.mk.injEq]
  exact ⟨funext h1, funext h2, funext h3⟩

theorem alle_ruf (As : List (Merkmal D)) (g : D.Fn) : (Merkmal.alle As).ruf g = As.all fun A => A.ruf g := by
  induction As with
  | nil => rfl
  | cons A rest ih => show (A.ruf g && (Merkmal.alle rest).ruf g) = _; rw [ih]; rfl

theorem alle_ind (As : List (Merkmal D)) (n : Nat) : (Merkmal.alle As).ind n = As.all fun A => A.ind n := by
  induction As with
  | nil => rfl
  | cons A rest ih => show (A.ind n && (Merkmal.alle rest).ind n) = _; rw [ih]; rfl

theorem alle_sperre (As : List (Merkmal D)) (L : D.Lock) :
    (Merkmal.alle As).sperre L = As.all fun A => A.sperre L := by
  induction As with
  | nil => rfl
  | cons A rest ih => show (A.sperre L && (Merkmal.alle rest).sperre L) = _; rw [ih]; rfl

/-! ## Decomposing a lock-only and a call-only feature set -/

/-- The probe "does not take `L`". -/
def ohneSperre (L : D.Lock) : Merkmal D := ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩

/-- **A lock-only feature set** is the conjunction over a complete list of locks of "does not take `L`" for every lock
    it refuses. -/
theorem sperrMerkmal_zerlegt (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls) (Sp : D.Lock → Bool)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    mE ⟨fun _ => true, fun _ => true, Sp⟩ e = ls.all fun L => Sp L || mE (ohneSperre L) e := by
  have hA : (⟨fun _ => true, fun _ => true, Sp⟩ : Merkmal D) =
      Merkmal.alle (ls.map fun L => if Sp L then Merkmal.top else ohneSperre L) := by
    apply Merkmal.gleich
    · intro g; rw [alle_ruf]; simp only [List.all_map]
      symm; apply List.all_eq_true.2; intro L _; simp only [Function.comp_def]; split <;> rfl
    · intro n; rw [alle_ind]; simp only [List.all_map]
      symm; apply List.all_eq_true.2; intro L _; simp only [Function.comp_def]; split <;> rfl
    · intro L'
      rw [alle_sperre]; simp only [List.all_map, Function.comp_def]
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true]
      constructor
      · intro h L _
        split
        · rfl
        · rename_i hL
          show (!(decide (L' = L))) = true
          by_cases he : L' = L
          · subst he; exact absurd h hL
          · simp [he]
      · intro h
        have := h L' (hls L')
        split at this
        · assumption
        · simp [ohneSperre] at this
  rw [hA, mE_alle, List.all_map]
  apply congrArg (List.all ls); funext L
  simp only [Function.comp_def]
  split
  · rename_i h; rw [h, mE_top]; rfl
  · rename_i h; simp [h]

/-- The probe "does not call `g`, not even through `g`'s signature" (the probe of `ruftB`). -/
def ohneRuf (g : D.Fn) : Merkmal D :=
  ⟨fun h => !(decide (h = g)), fun n => !(decide (n = D.sig g)), fun _ => true⟩

/-- **The call graph feature set** `rufM fs Z` is the conjunction, over the complete function list, of "does not call
    `g`" for every `g` outside `Z`. -/
theorem rufM_zerlegt (fs : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (Z : D.Fn → Bool)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    mE (rufM fs Z) e = fs.all fun g => Z g || mE (ohneRuf g) e := by
  have hA : rufM fs Z = Merkmal.alle (fs.map fun g => if Z g then Merkmal.top else ohneRuf g) := by
    apply Merkmal.gleich
    · intro h
      rw [alle_ruf]; simp only [List.all_map, Function.comp_def]
      show Z h = _
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true]
      constructor
      · intro hz g _
        split
        · rfl
        · rename_i hg
          show (!(decide (h = g))) = true
          by_cases he : h = g
          · subst he; exact absurd hz hg
          · simp [he]
      · intro hh
        have := hh h (hvoll h)
        split at this
        · assumption
        · simp [ohneRuf] at this
    · intro n
      rw [alle_ind]; simp only [List.all_map, Function.comp_def]
      show (fs.all fun g => !(decide (D.sig g = n)) || Z g) = _
      apply congrArg (List.all fs); funext g
      split
      · rename_i h; simp [h, Merkmal.top]
      · rename_i h
        simp only [h, ohneRuf, Bool.or_false]
        by_cases he : D.sig g = n
        · subst he; simp
        · simp [he, Ne.symm he]
    · intro L
      rw [alle_sperre]; simp only [List.all_map, Function.comp_def]
      symm; apply List.all_eq_true.2; intro g _; split <;> rfl
  rw [hA, mE_alle, List.all_map]
  apply congrArg (List.all fs); funext g
  simp only [Function.comp_def]
  split
  · rename_i h; rw [h, mE_top]; rfl
  · rename_i h; simp [h]

theorem nimmtB_eq (P : Programm D) (f : D.Fn) (L : D.Lock) : nimmtB P f L = !(mE (ohneSperre L) (P.rumpf f)) := rfl

theorem ruftB_eq (P : Programm D) (f g : D.Fn) : ruftB P f g = !(mE (ohneRuf g) (P.rumpf f)) := rfl

/-! ## Components 1, 3, 9 -/

/-- **Component 3 (lock ranks)**. -/
theorem urteil_3 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hls : ∀ L : D.Lock, L ∈ ls) :
    urteilAusZellen P S fs ls cs ws 3 = komp P S fs ls cs ws 3 := by
  simp only [urteilAusZellen, zellen, komp, stufenB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext f
  rw [show bodenM f = (⟨fun _ => true, fun _ => true, (bodenM f).sperre⟩ : Merkmal D) from rfl,
    sperrMerkmal_zerlegt ls hls]
  apply congrArg (List.all ls); funext L
  rw [nimmtB_eq]
  generalize mE (ohneSperre L) (P.rumpf f) = x
  generalize (bodenM f).sperre L = y
  cases x <;> cases y <;> rfl

/-- **Component 9 (masks)**. -/
theorem urteil_9 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hls : ∀ L : D.Lock, L ∈ ls) :
    urteilAusZellen P S fs ls cs ws 9 = komp P S fs ls cs ws 9 := by
  simp only [urteilAusZellen, zellen, komp, maskenB, maskenDisziplinB, List.all_flatMap, List.all_map,
    Function.comp_def, Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext w
  cases P.unterbricht w
  · simp
  · simp only [Bool.not_true, Bool.false_or, Bool.true_and]
    apply congrArg (List.all fs); funext f
    cases reachB P fs w f
    · simp
    · simp only [Bool.not_true, Bool.false_or, Bool.true_and]
      rw [show NurMaskiert D = (⟨fun _ => true, fun _ => true, D.maskiert⟩ : Merkmal D) from rfl,
        sperrMerkmal_zerlegt ls hls]
      apply congrArg (List.all ls); funext L
      rw [nimmtB_eq]
      generalize mE (ohneSperre L) (P.rumpf f) = x
      generalize D.maskiert L = y
      cases x <;> cases y <;> rfl

/-- **Component 1 (closedness)**. -/
theorem urteil_1 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) :
    urteilAusZellen P S fs ls cs ws 1 = komp P S fs ls cs ws 1 := by
  simp only [urteilAusZellen, zellen, komp, abgAlleB, abgB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext w
  apply congrArg (List.all fs); funext f
  cases reachB P fs w f
  · simp
  · simp only [Bool.not_true, Bool.false_or, Bool.true_and]
    rw [rufM_zerlegt fs hvoll]
    apply congrArg (List.all fs); funext g
    rw [ruftB_eq]
    generalize mE (ohneRuf g) (P.rumpf f) = x
    generalize reachB P fs w g = y
    cases x <;> cases y <;> rfl

/-! ## Components 2, 6, 7, 8 -/

theorem all_wahr {α : Type} (l : List α) : (l.all fun _ => true) = true := by
  induction l <;> simp_all

theorem all_und {α : Type} (l : List α) (p q : α → Bool) :
    (l.all p && l.all q) = l.all fun x => p x && q x := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, ← ih]
    cases p a <;> cases q a <;> simp

theorem all_oder {α : Type} (l : List α) (b : Bool) (p : α → Bool) :
    (l.all fun x => b || p x) = (b || l.all p) := by
  cases b <;> simp [all_wahr]

/-- **Component 8 (answers)**, over the complete lists of foreign bodies and registers. -/
theorem urteil_8 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 8 = komp P S fs ls cs ws 8 := by
  simp only [urteilAusZellen, zellen, komp, antwortenB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext f
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  have hvoll : ∀ x : D.Ax ⊕ D.Reg, x ∈ (Aufz.ax (D := D)).map Sum.inl ++ (Aufz.reg (D := D)).map Sum.inr := by
    intro x; cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map_of_mem (Aufz.ax_mem a))
    | inr r => exact List.mem_append_right _ (List.mem_map_of_mem (Aufz.reg_mem r))
  constructor
  · intro h x hx
    have := h x (hvoll x)
    cases x <;> simp_all [stelleB]
  · intro h x _
    by_cases hx : x ∈ (P.rumpf f).ants
    · have := h x hx
      cases x <;> simp_all [stelleB]
    · simp [hx]

/-- **Component 7 (race freedom)**: its verdict cells decide it; the cells of `schreibGetrennt` are derived and never
    refuse. -/
theorem urteil_7 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 7 = komp P S fs ls cs ws 7 := by
  simp only [urteilAusZellen, zellen, komp, rennB, schreibGetrenntZellen, List.all_flatMap, List.all_append,
    List.all_cons, List.all_nil, List.all_map, Function.comp_def, Zelle.schlecht, Zelle.kern, Zelle.kern?,
    Option.getD_some, Bool.true_and, Bool.false_and, Bool.not_false, Bool.not_not, Bool.and_true, all_wahr]

/-- **Component 6 (single pool)**. -/
theorem urteil_6 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 6 = komp P S fs ls cs ws 6 := by
  simp only [urteilAusZellen, zellen, komp, einzelnPoolB, poolSicherWB, ausgenommenB, List.all_flatMap,
    List.all_append, List.all_map, Function.comp_def, Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some,
    Bool.true_and, Bool.not_not]
  rw [all_und]
  apply congrArg (List.all ws); funext w
  cases mehrfachB ws w <;> simp [all_oder, all_wahr, Bool.or_assoc]

/-- **Component 2 (footprint)**: its verdict cells (the footprint and the register part) decide it; the cells of
    `getrennt` and `geteilt` are derived and never refuse. -/
theorem urteil_2 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 2 = komp P S fs ls cs ws 2 := by
  simp only [urteilAusZellen, zellen, komp, fussWXB, getrenntZellen, geteiltZelle, List.all_flatMap,
    List.all_append, List.all_cons, List.all_nil, List.all_map, Function.comp_def, Zelle.schlecht, Zelle.kern,
    Zelle.kern?, Option.getD_some, Bool.true_and, Bool.false_and, Bool.not_false, Bool.not_not, Bool.and_true,
    all_wahr]
  rw [all_und]

/-! ## Component 0: the fragment is an `mE` over the indirect calls -/

/-- The feature set that checks only the signatures of indirect calls. -/
def indMerkmal (K : Nat → Bool) : Merkmal D := ⟨fun _ => true, K, fun _ => true⟩

mutual

theorem sGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.gOk K (fun _ => true) = mS (indMerkmal K) s
  | .ite _ t e => by simp only [Stmt.gOk, mS, bGOk K t, bGOk K e]
  | .onOption _ p a => by simp only [Stmt.gOk, mS, bGOk K p, bGOk K a]
  | .onTag _ arms => by simp only [Stmt.gOk, mS, aGOk K arms]
  | .onWhy _ arms => by simp only [Stmt.gOk, mS, gaGOk K arms]
  | .call .. => rfl
  | .callInd .. => rfl
  | .locks _ _ body => by simp only [Stmt.gOk, mS, bGOk K body]; rfl
  | .breaking _ body => by simp only [Stmt.gOk, mS, bGOk K body]
  | .traverse _ _ body => by simp only [Stmt.gOk, mS, bGOk K body]
  | .retry _ _ body ueber => by simp only [Stmt.gOk, mS, bGOk K body, bGOk K ueber]
  | .forever _ _ body => by simp only [Stmt.gOk, mS, bGOk K body]
  | .assignSlot .. => rfl
  | .assignThru .. => rfl
  | .assignGlob .. => rfl
  | .putBytes .. => rfl
  | .assignVar .. => rfl
  | .shift .. => rfl
  | .axiomCall .. => rfl
  | .regWrite .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .advances .. => rfl
  | .retires .. => rfl
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

theorem bGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.gOk K (fun _ => true) = mB (indMerkmal K) b
  | .nil => rfl
  | .cons s rest => by simp only [Block.gOk, mB, sGOk K s, bGOk K rest]
  | .bind _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .bindCall _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]; rfl
  | .bindCallInd _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [Block.gOk, mB, eGOk K err, bGOk K rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [Block.gOk, mB, eGOk K err, bGOk K rest]
  | .regRead _ _ rest => by simp only [Block.gOk, mB, bGOk K rest, Bool.true_and]
  | .regReadElse _ _ _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest, Bool.true_and]
  | .awaits _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .exchange _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .narrow _ _ _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest]
  | .check _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest]
  | .float _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .floatLit _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .floatOf _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .floatNarrow _ _ _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest]

theorem aGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : (a : Arms D V l Γ Λ Λ' cs) → a.gOk K (fun _ => true) = mArms (indMerkmal K) a
  | .nil => rfl
  | .cons b rest => by simp only [Arms.gOk, mArms, bGOk K b, aGOk K rest]

theorem gaGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → a.gOk K (fun _ => true) = mGArms (indMerkmal K) a
  | .nil => rfl
  | .cons b rest => by simp only [GrundArms.gOk, mGArms, bGOk K b, gaGOk K rest]

theorem eGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.gOk K (fun _ => true) = mE (indMerkmal K) e
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .cons s rest => by simp only [Endblock.gOk, mE, sGOk K s, eGOk K rest]
  | .bind _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]
  | .bindCall _ _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [Endblock.gOk, mE, eGOk K err, eGOk K rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [Endblock.gOk, mE, eGOk K err, eGOk K rest]

end

/-- **The atom "in the fragment without its indirect-call test" is always true**: the cells `0.0 0..` have no program. -/
theorem gOk_ohne_test {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    e.gOk (fun _ => true) (fun _ => true) = true := by
  rw [eGOk]; exact mE_top e

/-- The probe "calls through no pointer of signature `n`" (the probe of `indB`). -/
def ohneInd (n : Nat) : Merkmal D := ⟨fun _ => true, fun n' => !(decide (n' = n)), fun _ => true⟩

/-- The admissibility of indirect calls over the complete function list is the conjunction, over every function `g`
    whose contract carriers are not in the footprint, of "calls through no pointer of `g`'s signature". -/
theorem kand_zerlegt (fs : List D.Fn) (Ok : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) :
    mE (indMerkmal fun n => fs.all fun g => !(decide (D.sig g = n)) || Ok g) e =
      fs.all fun g => Ok g || mE (ohneInd (D.sig g)) e := by
  have hA : (indMerkmal fun n => fs.all fun g => !(decide (D.sig g = n)) || Ok g : Merkmal D) =
      Merkmal.alle (fs.map fun g => if Ok g then Merkmal.top else ohneInd (D.sig g)) := by
    apply Merkmal.gleich
    · intro h; rw [alle_ruf]; simp only [List.all_map, Function.comp_def]
      symm; apply List.all_eq_true.2; intro g _; split <;> rfl
    · intro n; rw [alle_ind]; simp only [List.all_map, Function.comp_def]
      show (fs.all fun g => !(decide (D.sig g = n)) || Ok g) = _
      apply congrArg (List.all fs); funext g
      split
      · rename_i h; simp [h, Merkmal.top]
      · rename_i h
        simp only [h, ohneInd, Bool.or_false]
        by_cases he : D.sig g = n
        · subst he; simp
        · simp [he, Ne.symm he]
    · intro L; rw [alle_sperre]; simp only [List.all_map, Function.comp_def]
      symm; apply List.all_eq_true.2; intro g _; split <;> rfl
  rw [hA, mE_alle, List.all_map]
  apply congrArg (List.all fs); funext g
  simp only [Function.comp_def]
  split
  · rename_i h; rw [h, mE_top]; rfl
  · rename_i h; simp [h]

theorem indB_eq (P : Programm D) (f : D.Fn) (n : Nat) : indB P f n = !(mE (ohneInd n) (P.rumpf f)) := rfl

theorem any_nicht {α : Type} (l : List α) (p : α → Bool) : (l.any fun x => !p x) = !(l.all p) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.any_cons, List.all_cons, ih, Bool.not_and]

/-- **Component 0 (fragment)**. -/
theorem urteil_0 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 0 = komp P S fs ls cs ws 0 := by
  simp only [urteilAusZellen, zellen, komp, programmImFragmentG, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not, gOk_ohne_test]
  apply congrArg (List.all fs); funext f
  rw [show kandB P fs (fussOrteG P f) = fun n => fs.all fun g => !(decide (D.sig g = n)) ||
      ((P.requires g).orte ++ (P.ensures g).orte).all fun o => (fussOrteG P f).any fun o' => decide (o' = o) from rfl,
    eGOk, kand_zerlegt]
  apply congrArg (List.all fs); funext g
  rw [indB_eq]
  generalize mE (ohneInd (D.sig g)) (P.rumpf f) = x
  have hc : ((vertragsOrte P g).any fun o => !(istIn (fussOrteG P f) o)) =
      !(((P.requires g).orte ++ (P.ensures g).orte).all fun o => (fussOrteG P f).any fun o' => decide (o' = o)) := by
    simp only [vertragsOrte, istIn]
    exact any_nicht _ _
  rw [hc]
  generalize (((P.requires g).orte ++ (P.ensures g).orte).all fun o => (fussOrteG P f).any fun o' => decide (o' = o)) = y
  cases x <;> cases y <;> rfl

/-! ## Step 1: the model's Bool is the conjunction over the cells -/

/-- Every component is decided by its cells, over complete member lists. -/
theorem urteil_komp (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (c : Fin 10) :
    urteilAusZellen P S fs ls cs ws c = komp P S fs ls cs ws c := by
  rcases c with ⟨n, hn⟩
  match n, hn with
  | 0, _ => exact urteil_0 P S fs ls cs ws
  | 1, _ => exact urteil_1 P S fs ls cs ws hvoll
  | 2, _ => exact urteil_2 P S fs ls cs ws
  | 3, _ => exact urteil_3 P S fs ls cs ws hls
  | 4, _ => exact urteil_4 P S fs ls cs ws hcs
  | 5, _ => exact urteil_5 P S fs ls cs ws
  | 6, _ => exact urteil_6 P S fs ls cs ws
  | 7, _ => exact urteil_7 P S fs ls cs ws
  | 8, _ => exact urteil_8 P S fs ls cs ws
  | 9, _ => exact urteil_9 P S fs ls cs ws hls
  | n + 10, hn => exact absurd hn (by omega)

/-- All cells of a program. -/
def alleZellen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : List Zelle :=
  (List.finRange 10).flatMap (zellen P S fs ls cs ws)

/-- **Step 1.** The Lean model's Bool accepts a program exactly when the program has no bad cell. This is what makes
    the checker of the goal theorem a CONJUNCTIVE checker over the cells (the class of Theorems 4 and 5). -/
theorem akzeptiertX_zellen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    AkzeptiertX P S fs ls cs ws = true ↔ ∀ z ∈ alleZellen P S fs ls cs ws, z.schlecht = false := by
  rw [akzeptiertX_iff]
  constructor
  · intro h z hz
    obtain ⟨c, _, hzc⟩ := List.mem_flatMap.1 hz
    have := urteil_komp P S fs ls cs ws hvoll hls hcs c
    rw [h c] at this
    have h2 := (List.all_eq_true.1 this) z hzc
    simpa using h2
  · intro h c
    rw [← urteil_komp P S fs ls cs ws hvoll hls hcs c]
    apply List.all_eq_true.2
    intro z hz
    have := h z (List.mem_flatMap.2 ⟨c, List.mem_finRange c, hz⟩)
    simp [this]

end Gabbro.Grammatik.Gen
