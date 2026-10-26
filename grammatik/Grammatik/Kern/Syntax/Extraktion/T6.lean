/- Part 6 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T5

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

mutual

/-- The atoms of one statement: a leaf emits its singleton (`Λa` IS the
    statement's `Λ`, `cs` the written carrier plus the read hull);
    compounds emit their sub-bodies' atoms (`locks` bracketed by its sides);
    calls emit none (they open into further steps, S9). -/
def stmtAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (PCAtom D)
  | .ite _ t e => blockAtome tabs globs t ++ blockAtome tabs globs e
  | .onOption _ p a => blockAtome tabs globs p ++ blockAtome tabs globs a
  | .onTag _ arms => armsAtome tabs globs arms
  | .onWhy _ arms => grundArmsAtome tabs globs arms
  | .call _ _ _ _ => []
  | .callInd _ _ _ _ => []
  | .locks L _ body =>
      [PCAtom.take L] ++ blockAtome tabs globs body ++ [PCAtom.rel L]
  | .breaking _ body => blockAtome tabs globs body
  | .traverse _ _ body => blockAtome tabs globs body
  | .retry _ _ body ueber =>
      blockAtome tabs globs body ++ blockAtome tabs globs ueber
  | .forever _ _ body => blockAtome tabs globs body
  | s@(.assignSlot _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignThru _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignSlotRef _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignGlob _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.putBytes _ _ _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignVar _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.shift _ _ _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.axiomCall _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.regWrite _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.transition _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.publish _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.advances _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.retires _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.ret _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.retWhy _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.leave _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.next _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]

/-- The atoms of one block: the statement atoms in order; pure reads
    (`bind`, `awaits`, `exchange`, conditions) emit none (S8); else-branches
    emit theirs (either side may run). -/
def blockAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (PCAtom D)
  | .nil => []
  | .cons s rest => stmtAtome tabs globs s ++ blockAtome tabs globs rest
  | .bind _ rest => blockAtome tabs globs rest
  | .bindCall _ _ _ _ _ rest => blockAtome tabs globs rest
  | .bindCallInd _ _ _ _ _ rest => blockAtome tabs globs rest
  | .bindCallElse _ _ _ _ _ err rest =>
      endblockAtome tabs globs err ++ blockAtome tabs globs rest
  | .bindAxiom _ _ _ _ _ _ _ rest => blockAtome tabs globs rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => endblockAtome tabs globs err ++ blockAtome tabs globs rest
  | .regRead _ _ rest => blockAtome tabs globs rest
  | .regReadElse _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest
  | .awaits _ _ _ _ _ rest => blockAtome tabs globs rest
  | .exchange _ _ _ _ rest => blockAtome tabs globs rest
  | .narrow _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest
  | .check _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest
  | .float _ _ _ _ _ rest => blockAtome tabs globs rest
  | .floatLit _ _ _ rest => blockAtome tabs globs rest
  | .floatOf _ _ _ rest => blockAtome tabs globs rest
  | .floatNarrow _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest

/-- The atoms of a non-falling block: terminals emit none (they never fire,
    S10); the chain emits its statements' atoms. -/
def endblockAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (PCAtom D)
  | .ret _ _ => []
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtAtome tabs globs s ++ endblockAtome tabs globs rest
  | .bind _ rest => endblockAtome tabs globs rest
  | .bindCall _ _ _ _ _ rest => endblockAtome tabs globs rest
  | .bindCallElse _ _ _ _ _ err rest =>
      endblockAtome tabs globs err ++ endblockAtome tabs globs rest
  | .bindAxiom _ _ _ _ _ _ _ rest => endblockAtome tabs globs rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => endblockAtome tabs globs err ++ endblockAtome tabs globs rest
  | .regRead _ _ rest => endblockAtome tabs globs rest
  | .regReadElse _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ endblockAtome tabs globs rest
  | .awaits _ _ _ _ _ rest => endblockAtome tabs globs rest
  | .bindCallInd _ _ _ _ _ rest => endblockAtome tabs globs rest
  | .narrow _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ endblockAtome tabs globs rest
  | .exchange _ _ _ _ rest => endblockAtome tabs globs rest
  | .ite _ t e => endblockAtome tabs globs e ++ endblockAtome tabs globs t

/-- The atoms of a case split: every arm may run. -/
def armsAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List (PCAtom D)
  | .nil => []
  | .cons b rest => blockAtome tabs globs b ++ armsAtome tabs globs rest

/-- The atoms of a ground case split: every arm may run. -/
def grundArmsAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List (PCAtom D)
  | .nil => []
  | .cons b rest => blockAtome tabs globs b ++ grundArmsAtome tabs globs rest

end
/-- **The thread program from bodies.** Thread `f` runs `code f`: its
    program text is that body's flattened atoms. This is the annotation the
    goal's build-time premise consumes (`Ziel.lean` §9b) -- computed here
    instead of handed in by hand. -/
def progAus (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) : PCProg D :=
  fun f => endblockAtome tabs globs (P.rumpf (code f))

/-- `progAus` unfolds to the body's atoms. -/
theorem progAus_aus_rumpf (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) (f : Faden) :
    progAus P code tabs globs f = endblockAtome tabs globs (P.rumpf (code f)) :=
  rfl

/-- A `locks` body extracts to its bracketed atoms: the sides a
    `PCSchritt.take`/`rel` step points at. -/
theorem stmtAtome_locks (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) :
    stmtAtome tabs globs (Stmt.locks L hr body) =
      [PCAtom.take L] ++ blockAtome tabs globs body ++ [PCAtom.rel L] :=
  rfl

/-- **The leaf match.** A leaf statement extracts to exactly one atom, and
    its `Λa` IS the statement's `Λ`: a witness firing this statement takes
    the pointed-to atom to be this one, and `hΛa` closes by `rfl`. -/
theorem stmtAtome_blatt_eq {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (tabs : List D.Tab) (globs : List D.Glob) (h : s.istBlatt = true) :
    stmtAtome tabs globs s =
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)] := by
  cases s <;> first | exact rfl | (simp [Stmt.istBlatt] at h)

/-- **Mark cover.** Every held mark of a leaf statement is named in its
    atom's mark text: what `hmark` must find is there. -/
theorem stmtAtome_marken_deckt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (tabs : List D.Tab) (globs : List D.Glob) (h : s.istBlatt = true)
    (m : D.Marke) (st : Nat) (hm : Res.marke m st ∈ Λ) :
    m ∈ (stmtAtome tabs globs s).flatMap PCAtom.marks := by
  rw [stmtAtome_blatt_eq s tabs globs h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    PCAtom.marks]
  exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩

/-- **Carrier cover.** The written carrier and every read-hull carrier of a
    leaf statement sit in its atom's carrier text: what `hcar` must find is
    there. -/
theorem stmtAtome_traeger_deckt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (tabs : List D.Tab) (globs : List D.Glob) (h : s.istBlatt = true)
    (o : D.Tab ⊕ D.Glob)
    (ho : o ∈ stmtTraeger tabs globs s ++ stmtOrte s) :
    o ∈ (stmtAtome tabs globs s).flatMap PCAtom.carriers := by
  rw [stmtAtome_blatt_eq s tabs globs h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    PCAtom.carriers]
  exact ho

/-- **Program fidelity.** Every atom the body traversal yields is program
    text: the computed `prog` covers the flattened bodies, never less (the
    `kantenTreue` shape of §8, one level down: atoms, not edges). -/
def progTreue (prog : PCProg D) (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) : Prop :=
  ∀ f, ∀ a ∈ endblockAtome tabs globs (P.rumpf (code f)), a ∈ prog f

/-- The computed program is faithful: what the bodies flatten to is text. -/
theorem progTreue_aus_progAus (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) :
    progTreue (progAus P code tabs globs) P code tabs globs := by
  intro f a ha
  exact ha

/-- Sprechprobe: the probe bodies are bare terminals (S10: never fired), so
    the extracted thread program is empty -- the computation runs to the
    end, loudly (`rfl` fails at elaboration on a wrong atom). -/
example : progAus miniP (fun _ => true) miniTabs miniGlobs 0 = [] := rfl

#print axioms Gabbro.Grammatik.Extraktion.progAus_aus_rumpf
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_locks
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_blatt_eq
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_marken_deckt
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_traeger_deckt
#print axioms Gabbro.Grammatik.Extraktion.progTreue_aus_progAus

/-! ## 17. The execution link: fired leaf events against extracted atoms

    (Tasked as §15; §§15-16 are already taken and the file ends with a second
    §14 -- the `prog` extraction -- so this section is §17: numbers stay
    unique, content stays appended, nothing existing moves.)

    What the English §14 (`prog` extraction) books as its remainder: discharging
    a fired step's `hmark`/`hcar` against the extracted atom needs the per-leaf
    `execStmt` event characterization. This section proves it and discharges
    the checks.

    * `mem_leseEr` is the read-event shape (one `World.lese`): statement `Λ`
      exactly, carriers inside the read list.
    * `rep_append_single`/`schreibBytes_spur_eq` are the byte-write shape:
      `World.schreibBytes` emits one `zugriff` per byte; lock state is untouched
      by `zugriff`, so every event shares the entry `haelt`.
    * `uebergang_ereignis_aus_blatt` is the `uebergang` branch case, split off:
      `split` with bullets inside `cases ... with` breaks the outer
      alternatives (measured: every later alternative reports "not provided"),
      so it lives here as its own lemma.
    * `execEreignis_aus_blatt_ohne_axiomCall` is the characterization per leaf:
      a fired non-oracle leaf step's every new event carries exactly the
      statement's `Λ`, and every carrier it touches sits in the written
      carrier plus the `stmtOrte` read hull.
    * `hmark_hcar_aus_progAus_ohne_axiomCall` discharges the `PCSchritt`
      footprint checks (`hmark`/`hcar`) against `progAus` atoms: a fired
      non-oracle leaf whose counter points at its extracted atom names only
      that atom's marks and touches only its carriers -- hence the thread's
      program text (`pcAtom_mem_marks`/`pcAtom_mem_carriers`).

    Remainder (booked, not hidden; continuing the S-series of §14):
    S12. Atom identity (`hcs`): the counter must point at the atom
         `stmtAtome_blatt_eq` yields for the fired statement. Positing the
         pointed-to atom is the scheduler/witness duty (as `hpc` is); proving
         the counter always does so is the scheduling argument, not this
         section.
    S13. `axiomCall`: the oracle (`O.wirkt`) answers with an arbitrary world,
         so its events carry arbitrary `Λ`/carriers. Closing it needs an
         oracle-event contract (every oracle event names the statement `Λ`
         within the declared writes plus `args.orte`) -- carried as a
         hypothesis by `GenSchritt`/`PCSchritt`, never derived here.
-/

/-- Read events of one `World.lese`: they carry the statement `Λ` exactly,
    and every carrier they name sits in the read list. -/
theorem mem_leseEr {Λ : List (Res D)} {h : List D.Lock}
    {os : List (D.Tab ⊕ D.Glob)} {e : Ereignis D}
    (hm : e ∈ os.map fun o => match o with
      | .inl t => Ereignis.zugriff t false Λ h
      | .inr g => Ereignis.gzugriff g false Λ h) :
    e.lambda = Λ ∧ ∀ o, e.traeger = some o → o ∈ os := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
  cases o with
  | inl t =>
      refine ⟨rfl, fun o' h' => ?_⟩
      have h2 : o' = .inl t := by simpa [Ereignis.traeger] using h'.symm
      rw [h2]; exact ho
  | inr g =>
      refine ⟨rfl, fun o' h' => ?_⟩
      have h2 : o' = .inr g := by simpa [Ereignis.traeger] using h'.symm
      rw [h2]; exact ho

/-- Appending one more copy on the right is consing on the left, for
    `replicate`. -/
theorem rep_append_single {α : Type} (n : Nat) (a : α) :
    List.replicate n a ++ [a] = a :: List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- `schreibBytes` emits exactly one `zugriff` event per byte, all with the
    statement `Λ` on the written carrier (lock state is untouched by
    `zugriff`, so every event shares the entry `haelt`). -/
theorem schreibBytes_spur_eq (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte) :
    (σ.schreibBytes t f hf Λ k bs).spur =
      List.replicate bs.length (Ereignis.zugriff t true Λ σ.haelt) ++ σ.spur := by
  induction bs generalizing σ k with
  | nil => rfl
  | cons b bs ih =>
      simp only [World.schreibBytes]
      rw [ih]
      have hhaelt : (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).haelt =
          σ.haelt := rfl
      have hspur1 : (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).spur =
          [Ereignis.zugriff t true Λ σ.haelt] ++ σ.spur := rfl
      rw [hhaelt, hspur1, List.length_cons, ← List.append_assoc,
        rep_append_single, List.replicate_succ]

/-- `uebergang` through the taken branch: one write plus the
    `.inl t :: i.orte` reads. Split off from `execEreignis_aus_blatt_ohne_axiomCall`:
    `split` with bullets inside `cases ... with` breaks the outer alternatives,
    so this branch case lives here as its own lemma. -/
theorem uebergang_ereignis_aus_blatt (O : Orakel D) (passes : Nat)
    {V : Vertrag D} (l : Bool) {Γ : Ctx} {Λ : List (Res D)}
    (tabs : List D.Tab) (globs : List D.Glob)
    (t : D.Tab) (f : D.Feld t) {lo hi : Int} (hτ : D.typ t f = .int lo hi)
    (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int)
    (hn : lo ≤ nach ∧ nach ≤ hi)
    (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true)
    (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      ((Stmt.shift t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    (∀ e ∈ neu, e.lambda = Λ) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs
          ((Stmt.shift t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ)) ++
          stmtOrte ((Stmt.shift t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ))) := by
  simp only [execStmt] at hstep
  split at hstep
  · simp only [Ausgang.welt, Option.some.injEq] at hstep
    have hspur : σ'.spur =
        [Ereignis.zugriff t true Λ (σ.lese Λ (.inl t :: i.orte)).haelt] ++
        (.inl t :: i.orte).map (fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
      rw [← hstep]; rfl
    rw [hspur] at hneu
    have hneueq := List.append_cancel_right hneu
    subst hneueq
    constructor
    · intro e' he'
      rcases List.mem_append.mp he' with h1 | h1
      · obtain rfl := List.mem_singleton.mp h1
        rfl
      · exact (mem_leseEr h1).1
    · intro e' he' o ho
      rcases List.mem_append.mp he' with h1 | h1
      · obtain rfl := List.mem_singleton.mp h1
        have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
        subst ho'
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
      · have hmem : o ∈ .inl t :: i.orte := (mem_leseEr h1).2 o ho
        simp only [stmtTraeger, stmtOrte]
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · exact List.mem_append.mpr (Or.inr hm)
  · simp only [Ausgang.welt] at hstep
    simp at hstep


end Gabbro.Grammatik.Extraktion
