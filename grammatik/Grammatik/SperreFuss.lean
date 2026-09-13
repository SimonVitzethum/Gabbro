/-
  File:      Grammatik/SperreFuss.lean
  Subject:   THE FOOTPRINT CHECK WITH LOCK INVARIANTS -- the carriers a frame
             may rely on at a given point, the decidable program fact that
             replaces `fussOrtGB`, the residue predicate of the replay, and
             the user obligation `KoerperGutS`.

  `fussOrtGB` (the check of `ziel_ort_ganz`) asks every footprint carrier of
  a function to be guarded by a lock the function holds BY SIGNATURE, or to
  be written by no function: a carrier a thread reads inside
  `locks L { … }` falls (verdict probes B, C). Here a footprint carrier may
  also be PROTECTED BY A LOCK INVARIANT: guarded by a lock `L` that lists it
  (`c ∈ S.orte L`). Such a carrier is stable for the frame only while `L` is
  held -- at the access, which the typing guarantees (`Expr.orte_darf`: every
  guard of a carrier an expression reads is in its static holdings, from the
  signature or from an enclosing `locks` block). Between two critical
  sections other threads may change it; the sequential semantics
  (`SperreSem.lean`) lets the environment move it at the next acquire.

  * `stabilS P S lok f Λ`: the carriers the replay keeps equal between the
    sequential and the machine world while the frame's static holdings are
    `Λ` -- the footprint carriers guarded by a signature lock or written by
    no function (`sicher`), and the protected carriers of every lock held in
    `Λ`.
  * `fussSperreB`: every footprint carrier is `sicher`, or protected by an
    invariant of one of its guards; the device carriers of the registers a
    body reads (read without a guard at the access) must be `sicher`.
  * `KoerperGutS`: the obligation of `ziel_ort_ganz` over the semantics with
    acquire moves and release checks, for every move in `HavocOk S`.
-/
import Grammatik.SperreSem

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Held locks, safe carriers, stable carriers -/

/-- The locks named held by static holdings. -/
def heldL : List (Res D) → List D.Lock
  | [] => []
  | .held L :: Λ => L :: heldL Λ
  | .marke _ _ :: Λ => heldL Λ

theorem heldL_mem {Λ : List (Res D)} {L : D.Lock} : L ∈ heldL Λ ↔ Res.held L ∈ Λ := by
  induction Λ with
  | nil => simp [heldL]
  | cons r Λ ih =>
      cases r with
      | held K => simp [heldL, ih]
      | marke m s => simp [heldL, ih]

/-- The carrier is guarded by a lock `f` holds by signature. -/
def sigB (f : D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  (waechterVon c).any fun L => decide (L ∈ D.haelt f)

/-- No function of the member list writes the carrier. -/
def freiB (fs : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  fs.all fun g => !(TraegerSchreibt g c)

theorem sigB_ok {f : D.Fn} {c : D.Tab ⊕ D.Glob} (h : sigB f c = true) :
    ∃ L, Bewacht c L ∧ L ∈ D.haelt f := by
  obtain ⟨L, hL, hLh⟩ := List.any_eq_true.mp h
  exact ⟨L, waechterVon_mem.mp hL, of_decide_eq_true hLh⟩

theorem freiB_ok {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) {c : D.Tab ⊕ D.Glob}
    (h : freiB fs c = true) (g : D.Fn) : TraegerSchreibt g c = false := by
  have := (List.all_eq_true.mp h) g (hvoll g)
  simpa using this

/-- **The safe carriers of `f`**: footprint carriers that no other thread
    changes while a frame of `f` lives -- guarded by a signature lock of `f`,
    or LOCAL (`lok c`: in `ziel_ort_sperre`, written by no function,
    `freiB`; in `ziel_ort_einfaden`, every carrier -- only one thread
    moves). -/
def sicher (P : Programm D) (lok : D.Tab ⊕ D.Glob → Bool) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  (fussOrteG P f).filter fun c => sigB f c || lok c

/-- **The stable carriers of a frame of `f` at static holdings `Λ`**: the
    safe carriers, and the protected carriers of every lock `Λ` names held
    (no other thread can take such a lock while the frame holds it). -/
def stabilS (P : Programm D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (f : D.Fn)
    (Λ : List (Res D)) : List (D.Tab ⊕ D.Glob) :=
  sicher P lok f ++ (heldL Λ).flatMap S.orte

theorem sicher_mem {P : Programm D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    {c : D.Tab ⊕ D.Glob} :
    c ∈ sicher P lok f ↔ c ∈ fussOrteG P f ∧ (sigB f c || lok c) = true := by
  unfold sicher
  rw [List.mem_filter]

theorem stabilS_mem {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    {Λ : List (Res D)} {c : D.Tab ⊕ D.Glob} :
    c ∈ stabilS P S lok f Λ ↔ c ∈ sicher P lok f ∨ ∃ L, Res.held L ∈ Λ ∧ c ∈ S.orte L := by
  unfold stabilS
  rw [List.mem_append, List.mem_flatMap]
  simp only [heldL_mem]

theorem sicher_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (Λ : List (Res D)) : sicher P lok f ⊆ stabilS P S lok f Λ :=
  fun _ h => stabilS_mem.mpr (Or.inl h)

/-- The stable set depends only on the locks named held. -/
theorem stabilS_mono {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    {Λ Λ' : List (Res D)} (h : ∀ L, Res.held L ∈ Λ → Res.held L ∈ Λ') :
    stabilS P S lok f Λ ⊆ stabilS P S lok f Λ' := by
  intro c hc
  rcases stabilS_mem.mp hc with hc | ⟨L, hL, hc⟩
  · exact stabilS_mem.mpr (Or.inl hc)
  · exact stabilS_mem.mpr (Or.inr ⟨L, h L hL, hc⟩)

theorem stabilS_iff {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    {Λ Λ' : List (Res D)} (h : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) :
    stabilS P S lok f Λ' ⊆ stabilS P S lok f Λ :=
  stabilS_mono fun L hL => (h L).mp hL

/-- Agreement on the stable set, carried to holdings that name the same held
    locks (a leaf, a call, `advances`, `retires`). -/
theorem gleichAuf_stabil_iff {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    {Λ Λ' : List (Res D)} (h : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) {σ W : World D}
    (hg : GleichAuf (stabilS P S lok f Λ) σ W) : GleichAuf (stabilS P S lok f Λ') σ W :=
  GleichAuf.mono (fun _ hc => stabilS_iff h hc) hg

/-! ## 2. The footprint check -/

/-- **The footprint check with lock invariants.** For every function `f`:
    every footprint carrier (contract carriers, body reads, callee contract
    carriers) is guarded by a signature lock of `f`, or written by no
    function, or PROTECTED BY THE INVARIANT of one of its guards; every
    device carrier of a register `f` reads is guarded by a signature lock or
    written by no function. -/
def fussSperreB (P : Programm D) (S : SperrInv D) (fs : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || freiB fs c || (waechterVon c).any fun L => istIn (S.orte L) c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || freiB fs c)

/-- The property `fussSperreB` decides, per function, for the local
    carriers `lok`. -/
def FussS (P : Programm D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (f : D.Fn) : Prop :=
  (∀ c ∈ fussOrte P f, (sigB f c || lok c) = true ∨ ∃ L, Bewacht c L ∧ c ∈ S.orte L) ∧
  (∀ c ∈ (P.rumpf f).regs.flatMap D.rtraeger, (sigB f c || lok c) = true)

/-- With every carrier local the property holds for every function. -/
theorem fussS_alle (P : Programm D) (S : SperrInv D) (f : D.Fn) : FussS P S (fun _ => true) f :=
  ⟨fun _ _ => Or.inl (by simp), fun _ _ => by simp⟩

theorem fussSperreB_ok {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (h : fussSperreB P S fs = true) (f : D.Fn) :
    FussS P S (freiB fs) f := by
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  simp only [Bool.and_eq_true] at h1
  refine ⟨fun c hc => ?_, fun c hc => (List.all_eq_true.mp h1.2) c hc⟩
  have h2 := (List.all_eq_true.mp h1.1) c hc
  simp only [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact Or.inl (by simp only [Bool.or_eq_true]; exact h2)
  · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
    exact Or.inr ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩

/-- **The old check is the special case**: `fussOrtGB` gives `fussSperreB`
    for every family (the invariant disjunct is not used). -/
theorem fussSperreB_of_G (P : Programm D) (S : SperrInv D) (fs : List D.Fn)
    (h : fussOrtGB P fs = true) : fussSperreB P S fs = true := by
  refine List.all_eq_true.mpr fun f hf => ?_
  have h1 := (List.all_eq_true.mp h) f hf
  simp only [Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun c hc => ?_, List.all_eq_true.mpr fun c hc => ?_⟩
  · have h2 := (List.all_eq_true.mp h1) c (fuss_teilG P f hc)
    simp only [sigB, freiB, Bool.or_eq_true] at h2 ⊢
    exact Or.inl h2
  · have hc' : c ∈ fussOrteG P f := List.mem_append_right _ hc
    have h2 := (List.all_eq_true.mp h1) c hc'
    simpa [sigB, freiB] using h2

/-- **A footprint carrier whose guards are all held at the access is
    stable there.** -/
theorem stabil_of_fuss {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {Λ : List (Res D)} {c : D.Tab ⊕ D.Glob} (hc : c ∈ fussOrteG P f)
    (hw : ∀ L, Bewacht c L → Res.held L ∈ Λ) : c ∈ stabilS P S lok f Λ := by
  rcases List.mem_append.mp hc with hc1 | hc2
  · rcases hF.1 c hc1 with h | ⟨L, hB, hL⟩
    · exact stabilS_mem.mpr (Or.inl (sicher_mem.mpr ⟨hc, h⟩))
    · exact stabilS_mem.mpr (Or.inr ⟨L, hw L hB, hL⟩)
  · exact stabilS_mem.mpr (Or.inl (sicher_mem.mpr ⟨hc, hF.2 c hc2⟩))

/-- Every guard of a carrier an access may touch at holdings `Λ` is held in
    `Λ` (`OrtDarf`, the typing of every access). -/
theorem bewacht_held {Λ : List (Res D)} {c : D.Tab ⊕ D.Glob} (h : OrtDarf Λ c) {L : D.Lock}
    (hB : Bewacht c L) : Res.held L ∈ Λ := by
  cases c with
  | inl t => exact h (Sum.inl L) hB
  | inr g => exact h (Sum.inl L) hB

/-- **The carriers an expression reads are stable at its holdings.** -/
theorem orte_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {os : List (D.Tab ⊕ D.Glob)} {Λ : List (Res D)}
    (hd : ∀ o ∈ os, OrtDarf Λ o) (h : os ⊆ fussOrteG P f) : os ⊆ stabilS P S lok f Λ :=
  fun _ ho => stabil_of_fuss hF (h ho) fun _ hB => bewacht_held (hd _ ho) hB

theorem expr_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (h : e.orte ⊆ fussOrteG P f) : e.orte ⊆ stabilS P S lok f Λ :=
  orte_stabil hF e.orte_darf h

theorem args_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (a : Args D Γ Λ τs)
    (h : a.orte ⊆ fussOrteG P f) : a.orte ⊆ stabilS P S lok f Λ :=
  orte_stabil hF a.orte_darf h

theorem erg_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {Γ : Ctx} {Λ : List (Res D)} {τ : Option Ty} (e : ErgExpr D Γ Λ τ)
    (h : e.orte ⊆ fussOrteG P f) : e.orte ⊆ stabilS P S lok f Λ :=
  orte_stabil hF e.orte_darf h

/-- The guards of a callee's contract carriers are its signature locks. -/
theorem vertrag_darf (P : Programm D) (g : D.Fn) :
    ∀ o ∈ (P.requires g).orte ++ (P.ensures g).orte, ∀ L, Bewacht o L → L ∈ D.haelt g := by
  intro o ho L hB
  rcases List.mem_append.mp ho with ho | ho
  · have h := bewacht_held ((P.requires g).orte_darf o ho) hB
    unfold Signatur.anfang at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨K, hK, e⟩ := List.mem_map.mp h
      cases e
      exact hK
    · obtain ⟨m, _, e⟩ := List.mem_map.mp h
      cases m
      cases e
  · have h := bewacht_held ((P.ensures g).orte_darf o ho) hB
    unfold Vertrag.ende at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨K, hK, e⟩ := List.mem_map.mp h
      cases e
      exact hK
    · obtain ⟨m, _, e⟩ := List.mem_map.mp h
      cases m
      cases e

/-- **A callee's contract carriers are stable at the call**: their guards
    are the callee's signature locks, which the caller holds at the call
    (`RufPasst.hh`). -/
theorem vertrag_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {V : Vertrag D} {Λ : List (Res D)} (g : D.Fn)
    (hp : RufPasst D V (D.signatur g) Λ)
    (h : (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P f) :
    (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok f Λ :=
  fun _ ho => stabil_of_fuss hF (h ho) fun L hB =>
    (hp.hh L).mpr (vertrag_darf P g _ ho L hB)

/-- The same for a callee named through a pointer of signature `n`. -/
theorem vertrag_stabil_ind {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {V : Vertrag D} {Λ : List (Res D)} {n : Nat} (g : D.Fn)
    (hg : D.sig g = n) (hp : RufPasst D V (D.sigNr n) Λ)
    (h : (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P f) :
    (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok f Λ := by
  subst hg
  exact vertrag_stabil hF g hp h

/-- **The own `ensures` carriers are stable at a return**: at `ret` the
    holdings are a permutation of the signature's end holdings. -/
theorem ens_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {Λ : List (Res D)} (hperm : Λ.Perm (vertragVon D f).ende) :
    (P.ensures f).orte ⊆ stabilS P S lok f Λ :=
  fun _ ho => stabil_of_fuss hF (fuss_ensG P f ho) fun _ hB =>
    hperm.symm.mem_iff.mp (bewacht_held ((P.ensures f).orte_darf _ ho) hB)

/-- The device carriers of a register read, in the safe set of the frame. -/
theorem regP_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    {Λ : List (Res D)} {r : D.Reg} (h : regP (sicher P lok f) r = true) :
    ∀ o ∈ D.rtraeger r, o ∈ stabilS P S lok f Λ :=
  fun o ho => sicher_stabil Λ (regP_ok h o ho)

/-! ## 3. The residues the replay follows -/

/-- `GRest.okG` with the register test against a second set (the safe
    carriers): a residue in the widened fragment whose reads lie in the
    footprint `S` and whose register reads have their device carriers in
    `S'`. -/
def GRest.okS (P : Programm D) (S S' : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.gOk (kandP P S) (regP S') = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.gOk (kandP P S) (regP S') = true ∧ blockOrteP P b ⊆ S ∧ k.okS P S S'
  | _, _, _, .schrumpf k => k.okS P S S'
  | _, _, _, .frei _ k => k.okS P S S'
  | _, _, _, .trav _ inv body _ k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S') = true ∧ blockOrteP P body ⊆ S ∧ k.okS P S S'
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S') = true ∧ blockOrteP P body ⊆ S ∧ k.okS P S S'
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.gOk (kandP P S) (regP S') = true ∧ blockOrteP P body ⊆ S ∧
        ueber.gOk (kandP P S) (regP S') = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okS P S S'
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.gOk (kandP P S) (regP S') = true ∧ blockOrteP P body ⊆ S ∧
        ueber.gOk (kandP P S) (regP S') = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okS P S S'
  | _, _, _, .ewig _ _ inv body k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S') = true ∧ blockOrteP P body ⊆ S ∧ k.okS P S S'
  | _, _, _, .ewigRest _ _ inv body k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S') = true ∧ blockOrteP P body ⊆ S ∧ k.okS P S S'
  | _, _, _, .wartet b k => b.gOk (kandP P S) (regP S') = true ∧ blockOrteP P b ⊆ S ∧ k.okS P S S'
  | _, _, _, .wartetSonst _ err b k =>
      err.gOk (kandP P S) (regP S') = true ∧ endblockOrteP P err ⊆ S ∧
        b.gOk (kandP P S) (regP S') = true ∧ blockOrteP P b ⊆ S ∧ k.okS P S S'

section OkS

variable {P : Programm D} {S S' : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okS_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okS P S S') :
    s.gOk (kandP P S) (regP S') = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okS P S S' := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.gOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okS_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okS P S S') :
    s.gOk (kandP P S) (regP S') = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okS P S S' := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.gOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

end OkS

/-- **The fragment the replay reads**, from the decided fragment and the
    footprint check: every body is in `gOk` with the admissibility of its
    footprint, and every register it reads has its device carriers among
    the safe carriers. -/
theorem programmImFragmentS_ok (P : Programm D) (S : SperrInv D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmImFragmentG P fs = true)
    {lok : D.Tab ⊕ D.Glob → Bool} (hF : ∀ f, FussS P S lok f) (f : D.Fn) :
    (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true :=
  Endblock.gOk_mono (kandB_kandP P hvoll _) _ ((List.all_eq_true.mp h) f (hvoll f))
    (fun r hr => regP_of fun o ho => sicher_mem.mpr ⟨fuss_regG P f r hr o ho,
      (hF f).2 o (List.mem_flatMap.mpr ⟨r, hr, ho⟩)⟩)

/-- A fresh frame's residue is followed. -/
theorem okS_start (P : Programm D) (S : SperrInv D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmImFragmentG P fs = true)
    {lok : D.Tab ⊕ D.Glob → Bool} (hF : ∀ f, FussS P S lok f) (f : D.Fn) :
    (GRest.ende (V := vertragVon D f) (l := false) (P.rumpf f)).okS P (fussOrteG P f)
      (sicher P lok f) :=
  ⟨programmImFragmentS_ok P S hvoll h hF f, fuss_rumpfG P f⟩

/-! ## 4. The user obligation -/

/-- **THE USER OBLIGATION WITH LOCK INVARIANTS, one per function.** The two
    clauses of `KoerperGutZ` (`ZielOrtGanz.lean`) -- the body triple with
    the caller duty, and no `logik` outcome -- over the semantics with
    acquire moves and release checks (`execEndH`), for every environment
    move in `HavocOk S`:
    * at every `locks L` the body may ASSUME `S.inv L` of the protected
      carriers (whatever other threads did while `L` was free);
    * at every release it must RE-ESTABLISH `S.inv L` -- a failed release
      check is a `logik` outcome, which the second clause excludes.
    Still a statement about `f`'s body over the SEQUENTIAL semantics only,
    against handlers and oracles as before. -/
def KoerperGutS (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) :
    Prop :=
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        (∀ (σ' : World D) (v : ErgVal D (D.erg f)),
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ =
            EndAusgang.zurueck σ' v → EnsAmRueck P f σ σ' ρ v) ∧
        (∀ g : D.Fn,
          execEndH (V := vertragVon D f) S O' U passes (torRuf P R) (P.rumpf f) σ ρ ≠
            EndAusgang.logik (Logik.vorbedingung g))) ∧
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneLogik R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ e : Logik D, execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ ≠
          EndAusgang.logik e)

/-- **Today's obligation is the special case of the empty family**: every
    move in its class is the identity and the semantics is `execEnd`. -/
theorem koerperGutS_leer {P : Programm D} {passes : Nat} {Q : AxEns D} {f : D.Fn}
    (h : KoerperGutZ P passes Q f) : KoerperGutS P passes Q (SperrInv.leer D) f := by
  refine ⟨fun O' hr hl hq U hU R hR hOV σ ρ hreq => ?_,
    fun O' hr hl hq U hU R hR hOL σ ρ hreq e => ?_⟩
  · have hid := havocOk_leer hU
    rw [Endblock.execH_leer O' U passes R hid, Endblock.execH_leer O' U passes (torRuf P R) hid]
    exact h.1 O' hr hl hq R hR hOV σ ρ hreq
  · have hid := havocOk_leer hU
    rw [Endblock.execH_leer O' U passes R hid]
    exact h.2 O' hr hl hq R hR hOL σ ρ hreq e

/-- **A body without `locks` owes nothing new**: for every family, its new
    obligation is its old one (the semantics does not reach an acquire). -/
theorem koerperGutS_ohne {P : Programm D} {passes : Nat} {Q : AxEns D} (S : SperrInv D)
    {f : D.Fn} (hl : (P.rumpf f).ohneLocks = true) (h : KoerperGutZ P passes Q f) :
    KoerperGutS P passes Q S f := by
  refine ⟨fun O' hr hlk hq U _ R hR hOV σ ρ hreq => ?_,
    fun O' hr hlk hq U _ R hR hOL σ ρ hreq e => ?_⟩
  · rw [Endblock.execH_ohne S O' U passes R _ hl, Endblock.execH_ohne S O' U passes (torRuf P R) _ hl]
    exact h.1 O' hr hlk hq R hR hOV σ ρ hreq
  · rw [Endblock.execH_ohne S O' U passes R _ hl]
    exact h.2 O' hr hlk hq R hR hOL σ ρ hreq e

/-! ## 5. Records of the environment's moves -/

/-- A recorded acquire: lock, key world, the memory the protected carriers
    were taken from. -/
abbrev UEintrag (D : Deklaration) := D.Lock × World D × Speicher D

def FunkU (HU : List (UEintrag D)) : Prop :=
  ∀ (L : D.Lock) (σ : World D) (s s' : Speicher D), (L, σ, s) ∈ HU → (L, σ, s') ∈ HU → s = s'

def KurzU (N : Nat) (HU : List (UEintrag D)) : Prop :=
  ∀ e ∈ HU, e.2.1.spur.length < N

/-- Every recorded source memory meets the lock's invariant. -/
def InvU (S : SperrInv D) (HU : List (UEintrag D)) : Prop :=
  ∀ (L : D.Lock) (σ : World D) (s : Speicher D), (L, σ, s) ∈ HU → S.inv L s = true

def PasstU (S : SperrInv D) (U : Umwelt D) (HU : List (UEintrag D)) : Prop :=
  ∀ (L : D.Lock) (σ : World D) (s : Speicher D), (L, σ, s) ∈ HU → U L σ = mischU S L σ s

/-- The move of a record: the recorded source at a recorded key, the
    reference memory `sp` everywhere else. -/
noncomputable def umweltAus (S : SperrInv D) (sp : Speicher D) (HU : List (UEintrag D)) :
    Umwelt D :=
  fun L σ =>
    haveI := Classical.propDecidable (∃ s : Speicher D, (L, σ, s) ∈ HU)
    if h : ∃ s : Speicher D, (L, σ, s) ∈ HU then mischU S L σ (Classical.choose h)
    else mischU S L σ sp

theorem umweltAus_passt (S : SperrInv D) (sp : Speicher D) {HU : List (UEintrag D)}
    (hf : FunkU HU) : PasstU S (umweltAus S sp HU) HU := by
  intro L σ s hmem
  have hex : ∃ s : Speicher D, (L, σ, s) ∈ HU := ⟨s, hmem⟩
  simp only [umweltAus, dif_pos hex]
  rw [hf L σ _ s (Classical.choose_spec hex) hmem]

/-- **The move of a record is in the class**, when every recorded source
    and the reference memory meet the invariants. -/
theorem umweltAus_ok {S : SperrInv D} (hS : SperrInvOk S) {sp : Speicher D}
    (hsp : ∀ L, S.inv L sp = true) {HU : List (UEintrag D)} (hi : InvU S HU) :
    HavocOk S (umweltAus S sp HU) := by
  intro L σ
  unfold umweltAus
  split
  · rename_i hex
    exact ⟨rfl, mischU_aussen S L σ _, (mischU_inv hS L σ _).trans
      (hi L σ _ (Classical.choose_spec hex))⟩
  · exact ⟨rfl, mischU_aussen S L σ _, (mischU_inv hS L σ _).trans (hsp L)⟩

theorem funkU_nil : FunkU ([] : List (UEintrag D)) := fun _ _ _ _ h => absurd h List.not_mem_nil

theorem invU_nil (S : SperrInv D) : InvU S ([] : List (UEintrag D)) :=
  fun _ _ _ h => absurd h List.not_mem_nil

theorem kurzU_nil (N : Nat) : KurzU N ([] : List (UEintrag D)) :=
  fun _ h => absurd h List.not_mem_nil

theorem kurzU_mono {N N' : Nat} {HU : List (UEintrag D)} (h : KurzU N HU) (hN : N ≤ N') :
    KurzU N' HU :=
  fun e he => Nat.lt_of_lt_of_le (h e he) hN

theorem passtU_append {S : SperrInv D} {U : Umwelt D} {HU : List (UEintrag D)} {e : UEintrag D}
    (h : PasstU S U (HU ++ [e])) : PasstU S U HU :=
  fun L σ s hmem => h L σ s (List.mem_append_left _ hmem)

theorem funkU_append {HU : List (UEintrag D)} (hf : FunkU HU) {N : Nat} (hk : KurzU N HU)
    (e : UEintrag D) (he : N ≤ e.2.1.spur.length) : FunkU (HU ++ [e]) := by
  intro L σ s s' h1 h2
  rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
  · exact hf L σ s s' h1 h2
  · have := hk _ h1
    rw [List.mem_singleton] at h2
    subst h2
    exact absurd he (Nat.not_le.mpr this)
  · have := hk _ h2
    rw [List.mem_singleton] at h1
    subst h1
    exact absurd he (Nat.not_le.mpr this)
  · rw [List.mem_singleton] at h1 h2
    rw [← h1] at h2
    simp only [Prod.mk.injEq] at h2
    exact h2.2.2.symm

theorem invU_append {S : SperrInv D} {HU : List (UEintrag D)} (hi : InvU S HU) (L : D.Lock)
    (σ : World D) (s : Speicher D) (hs : S.inv L s = true) : InvU S (HU ++ [(L, σ, s)]) := by
  intro L' σ' s' hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hi L' σ' s' hm
  · rw [List.mem_singleton] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact hs

#print axioms Gabbro.Grammatik.fussSperreB_ok
#print axioms Gabbro.Grammatik.fussSperreB_of_G
#print axioms Gabbro.Grammatik.vertrag_stabil
#print axioms Gabbro.Grammatik.koerperGutS_leer
#print axioms Gabbro.Grammatik.umweltAus_ok

end Gabbro.Grammatik
