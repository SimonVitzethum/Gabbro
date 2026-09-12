/-
  File:      Grammatik/RufAdaequatG.lean
  Subject:   ADEQUACY OF THE CALL MACHINE G -- the machine computes what the
             sequential semantics computes (single thread, call-free bodies).

  Why: the Hoare rules (`HoareRegeln.lean`, `HoareRuf.lean`) are stated over
  `execStmt`/`execBlock`/`execEnd`. A contract proved with them talks about
  MACHINE runs only if the machine `RufSchrittG` computes the sequential
  result. This file proves that for the covered fragment: a head frame
  whose residue is `.ende b` for a call-free end block `b`, run by steps of
  its own thread only, pops with a `rueck` event carrying EXACTLY the value
  `execEnd` returns, and the shared memory ends where `execEnd` ends.

  The proof is a simulation, mutual over `Stmt`/`Block`/`Arms`/`GrundArms`
  like `execStmt`: a block `b` in `dann b k` position, started at world `σ`
  and environment `ρ`, runs to the continuation `k` at the world and
  environment `execBlock` returns (`.ok`), or pops the frame with the value
  `execBlock` returns (`.zurueck`).
-/
import Grammatik.RufMaschineG
import Grammatik.HoareRegeln

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Runs of one thread -/

/-- The reflexive-transitive closure of `RufSchrittG`, restricted to steps of
    thread `f`. -/
inductive RufLaufG (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) :
    RufMaschineG D → RufMaschineG D → Prop where
  | refl (M : RufMaschineG D) : RufLaufG P O passes f M M
  | schritt {M M' M'' : RufMaschineG D} (h : RufSchrittG P O passes M f M')
      (hr : RufLaufG P O passes f M' M'') : RufLaufG P O passes f M M''

theorem RufLaufG.trans {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' M'' : RufMaschineG D} (h1 : RufLaufG P O passes f M M')
    (h2 : RufLaufG P O passes f M' M'') : RufLaufG P O passes f M M'' := by
  induction h1 with
  | refl => exact h2
  | schritt h _ ih => exact RufLaufG.schritt h (ih h2)

theorem RufLaufG.einzeln {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (h : RufSchrittG P O passes M f M') :
    RufLaufG P O passes f M M' :=
  RufLaufG.schritt h (RufLaufG.refl M')

/-- A step of thread `f` leaves every other thread untouched. -/
theorem rufSchrittG_fremd {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (h : RufSchrittG P O passes M f M') (g : Faden) (hg : g ≠ f) :
    M'.faeden g = M.faeden g := by
  cases h <;> exact rufUpdateG_noteq _ _ _ hg _

/-- A run of thread `f` leaves every other thread untouched. -/
theorem rufLaufG_fremd {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (h : RufLaufG P O passes f M M') (g : Faden) (hg : g ≠ f) :
    M'.faeden g = M.faeden g := by
  induction h with
  | refl => rfl
  | schritt h1 _ ih => rw [ih, rufSchrittG_fremd h1 g hg]

/-- No other thread holds any lock admitted by `A`. -/
def FreiA (A : D.Lock → Prop) (M : RufMaschineG D) (f : Faden) : Prop :=
  ∀ L, A L → RufFreiG M f L

/-- Lock freedom is about the OTHER threads, so a run of `f` keeps it. -/
theorem FreiA.lauf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {A : D.Lock → Prop} {M M' : RufMaschineG D} (h : RufLaufG P O passes f M M')
    (hA : FreiA A M f) : FreiA A M' f := by
  intro L hL g hg
  rw [rufLaufG_fremd h g hg]
  exact hA L hL g hg

/-! ## 2. The thread state the simulation talks about -/

/-- Thread `f` of `M` runs a frame of `fn` (parameters `rho`, entry world
    `s0`) above `stapel`, with log `log`, residue `r` at environment `ρ`,
    and its current world IS `σ`: trace `σ.spur`, shared memory
    `σ.speicher`. -/
def ZustandG (M : RufMaschineG D) (f : Faden) (stapel : List (RufRahmenG D))
    (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D)
    (log : List (RufEreignisF D)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D fn) l Γ Λ) (σ : World D) : Prop :=
  M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩, σ.spur, log⟩ ∧
    M.speicher = σ.speicher

/-- Thread `f` of `M'` has popped the frame of `fn` to `caller` above `rst`,
    logging `rueck fn rho v s0 σ'`, and the shared memory is `σ'.speicher`. -/
def GepopptG (M' : RufMaschineG D) (f : Faden) (caller : RufRahmenG D)
    (rst : List (RufRahmenG D)) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (log : List (RufEreignisF D)) (v : ErgVal D (D.erg fn))
    (σ' : World D) : Prop :=
  M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
    M'.speicher = σ'.speicher

theorem ZustandG.welt {M : RufMaschineG D} {f : Faden} {stapel : List (RufRahmenG D)}
    {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {log : List (RufEreignisF D)} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D fn) l Γ Λ} {σ : World D}
    (h : ZustandG M f stapel fn rho s0 log ρ r σ) : M.weltVon f = σ := by
  unfold RufMaschineG.weltVon
  rw [h.1, h.2]
  exact Speicher.welt_speicher σ

theorem ZustandG.spur {M : RufMaschineG D} {f : Faden} {stapel : List (RufRahmenG D)}
    {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {log : List (RufEreignisF D)} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D fn) l Γ Λ} {σ : World D}
    (h : ZustandG M f stapel fn rho s0 log ρ r σ) : (M.faeden f).spur = σ.spur := by
  rw [h.1]

/-- Building the state after a step: the updated thread is the target shape. -/
theorem zustandG_neu {M : RufMaschineG D} {f : Faden} {sp : Speicher D}
    {z : RufFadenG D} {lauf : Lauf D} {st : World D}
    {stapel : List (RufRahmenG D)} {fn : D.Fn} {rho : Env D (D.params fn)}
    {s0 : World D} {log : List (RufEreignisF D)} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D fn) l Γ Λ}
    {σ : World D}
    (hz : z = ⟨stapel, ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩, σ.spur, log⟩)
    (hsp : sp = σ.speicher) :
    ZustandG ⟨sp, rufUpdateG M.faeden f z, lauf, st⟩ f stapel fn rho s0 log ρ r σ :=
  ⟨by rw [← hz]; exact rufUpdateG_self M.faeden f z, hsp⟩

theorem gepopptG_neu {M : RufMaschineG D} {f : Faden} {sp : Speicher D}
    {z : RufFadenG D} {lauf : Lauf D} {st : World D} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} {fn : D.Fn} {rho : Env D (D.params fn)}
    {s0 : World D} {log : List (RufEreignisF D)} {v : ErgVal D (D.erg fn)}
    {σ' : World D}
    (hz : z = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩)
    (hsp : sp = σ'.speicher) :
    GepopptG ⟨sp, rufUpdateG M.faeden f z, lauf, st⟩ f caller rst fn rho s0 log v σ' :=
  ⟨by rw [← hz]; exact rufUpdateG_self M.faeden f z, hsp⟩

/-! ## 3. Leaves extend the trace by access events only -/

/-- The read events `World.lese` prepends. -/
def leseEv (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    List (Ereignis D) :=
  os.map fun o => match o with
    | .inl t => Ereignis.zugriff t false Λ σ.haelt
    | .inr g => Ereignis.gzugriff g false Λ σ.haelt

theorem lese_spur (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ os).spur = leseEv σ Λ os ++ σ.spur := rfl

/-- An access event (table or global), never a lock event. -/
def Ereignis.istZugriff : Ereignis D → Bool
  | .zugriff .. => true
  | .gzugriff .. => true
  | _ => false

/-- Every event of `neu` is an access event. -/
def NurZugriff (neu : List (Ereignis D)) : Prop :=
  ∀ e ∈ neu, e.istZugriff = true

theorem offen_nurZugriff : ∀ (neu s : List (Ereignis D)), NurZugriff neu →
    offen (neu ++ s) = offen s
  | [], _, _ => rfl
  | e :: neu, s, h => by
      have he := h e List.mem_cons_self
      have ih := offen_nurZugriff neu s (fun x hx => h x (List.mem_cons_of_mem _ hx))
      cases e with
      | zugriff => simpa [offen] using ih
      | gzugriff => simpa [offen] using ih
      | nimmt => simp [Ereignis.istZugriff] at he
      | gibt => simp [Ereignis.istZugriff] at he

theorem kein_nimmt {neu : List (Ereignis D)} (h : NurZugriff neu) :
    ∀ (L : D.Lock) (hs : List D.Lock), Ereignis.nimmt L hs ∉ neu := by
  intro L hs hm
  have := h _ hm
  simp [Ereignis.istZugriff] at this

/-- `σ'` extends `σ` by access events only. -/
def Erw (σ σ' : World D) : Prop :=
  ∃ neu, σ'.spur = neu ++ σ.spur ∧ NurZugriff neu

theorem Erw.refl (σ : World D) : Erw σ σ :=
  ⟨[], rfl, fun e he => by simp at he⟩

theorem Erw.trans {a b c : World D} (h1 : Erw a b) (h2 : Erw b c) : Erw a c := by
  obtain ⟨n1, e1, z1⟩ := h1
  obtain ⟨n2, e2, z2⟩ := h2
  refine ⟨n2 ++ n1, by rw [e2, e1, List.append_assoc], ?_⟩
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact z2 e h
  · exact z1 e h

theorem Erw.offen {σ σ' : World D} (h : Erw σ σ') : offen σ'.spur = offen σ.spur := by
  obtain ⟨neu, e, z⟩ := h
  rw [e]
  exact offen_nurZugriff neu σ.spur z

theorem Erw.lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    Erw σ (σ.lese Λ os) := by
  refine ⟨_, rfl, ?_⟩
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨o, _, rfl⟩ := he
  cases o <;> rfl

theorem Erw.schreibSlot (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : Erw σ (σ.schreibSlot t Λ k f v) :=
  ⟨[.zugriff t true Λ σ.haelt], rfl, by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    rfl⟩

theorem Erw.schreibGlob (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : Erw σ (σ.schreibGlob g Λ v) :=
  ⟨[.gzugriff g true Λ σ.haelt], rfl, by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    rfl⟩

theorem Erw.schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : ∀ (bs : List Byte) (σ : World D) (k : Int),
    Erw σ (σ.schreibBytes t f hf Λ k bs)
  | [], σ, _ => Erw.refl σ
  | _ :: bs, σ, k =>
      (Erw.schreibSlot σ t Λ k f _).trans (Erw.schreibBytes t f hf Λ bs _ (k + 1))

/-! ## 4. The covered fragment -/

/-- The leaves the machine runs atomically (`blatt`/`dannBlatt`) and whose
    new trace events are accesses only. `axiomCall` is NOT here: the oracle
    may answer with any world, but the machine step demands a trace that
    extends the old one without `nimmt` (`hneu`/`hkein_nimmt`). -/
inductive BlattG {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Prop where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      BlattG (l := l) (.assignSlot t f i e hw hL)
  | assignDurch (n : Nat) (p : Expr D Γ Λ (.ptr n true)) (t : D.Tab)
      (ht : D.tabNr n = some t) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      BlattG (l := l) (.assignDurch p t ht f i e hw hL)
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) :
      BlattG (l := l) (.assignGlob g e hw hL)
  | schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true)
      (hL : darf D t Λ) :
      BlattG (l := l) (.schreibBytes t f hf n i hlo hhi e hw hL)
  | assignVar {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ) :
      BlattG (l := l) (.assignVar (τ := τ) x e)
  | uebergang (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      BlattG (l := l) (.uebergang t f hτ i von nach hn he hw hL)
  | regSchreib (r : D.Reg) (hk : (D.rklasse r).schreibbar = true)
      (e : Expr D Γ Λ (D.rtyp r)) :
      BlattG (l := l) (.regSchreib r hk e)
  | transition (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      BlattG (l := l) (Γ := Γ) (Λ := Λ) (.transition r hk m hm hl maske bits)
  | publish (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) :
      BlattG (l := l) (.publish g e payload hp hw hL)
  | advances (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      BlattG (l := l) (Γ := Γ) (.advances m a h hs)
  | retires (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ) (a : D.Annahme) :
      BlattG (l := l) (Γ := Γ) (.retires m s h a)

theorem BlattG.istBlatt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) : s.istBlatt = true := by
  cases h <;> rfl

/-- The leaf forms of `BlattG`, as a decidable classifier (used to refute
    impossible cases without dependent elimination on the indices). -/
def Stmt.blattArt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .assignSlot .. | .assignDurch .. | .assignGlob .. | .schreibBytes .. | .assignVar ..
  | .uebergang .. | .regSchreib .. | .transition .. | .publish .. | .advances ..
  | .retires .. => true
  | _ => false

theorem BlattG.art {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) : s.blattArt = true := by
  cases h <;> rfl

/-- A covered leaf that ends normally extends the trace by accesses only. -/
theorem BlattG.erw {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hex : execStmt O passes R s σ ρ = .ok σ' ρ') : Erw σ σ' := by
  cases h with
  | assignSlot t f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
  | assignDurch n p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _)
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibBytes _ _ _ _ _ _ _)
  | assignVar x e =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.lese _ _ _
  | uebergang t f hτ i von nach hn he hw hL =>
      simp only [execStmt] at hex
      split at hex
      · simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, -⟩ := hex
        exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
      · cases hex
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.lese _ _ _
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.refl _
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _)
  | advances m a h hs =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.refl _
  | retires m s h a =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.refl _

/-- A covered leaf never returns. -/
theorem BlattG.nicht_zurueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) (σ σ' : World D) (ρ : Env D Γ)
    (v : ErgVal D V.erg) : execStmt O passes R s σ ρ ≠ .zurueck σ' v := by
  intro hex
  cases h <;> simp only [execStmt] at hex <;> (try split at hex) <;> cases hex

/- **The covered fragment.** `A` admits the locks a body may take (the
    lock-freedom premise talks about exactly these), `mr` says whether a
    `ret` may occur (`false` under a `locks` body: the machine's `dannRet`
    pops without the `gibt` that `execStmt`'s `locks` appends to a return
    world -- and a `ret` inside a `locks` body is untypable in a function
    body anyway, since `V.ende` names only the entry locks). Excluded, with
    reasons in the CUTS block at the end: calls of every form, `axiomCall`,
    `bindAxiom`, `traverse`, `retry`, `forever`, `leave`, `next`,
    `retGrund`, and every else-branch (`sonst`) that does not end in `ret`
    at loop level `false`. -/
mutual

inductive StmtG {V : Vertrag D} (A : D.Lock → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Prop where
  | blatt {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (s : Stmt D V l Γ Λ Λ') (h : BlattG s) : StmtG A mr s
  | ite {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
      (ht : BlockG A mr t) (he : BlockG A mr e) : StmtG A mr (.ite c t e)
  | onOption {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Int}
      (o : Expr D Γ Λ (.opt n)) (p : Block D V l (.index n :: Γ) Λ Λ')
      (a : Block D V l Γ Λ Λ') (hp : BlockG A mr p) (ha : BlockG A mr a) :
      StmtG A mr (.onOption o p a)
  | onTag {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
      (arms : Arms D V l Γ Λ Λ' cs) (ha : ArmsG A mr arms) :
      StmtG A mr (.onTag v arms)
  | onGrund {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (r : Expr D Γ Λ (.grund n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (ha : GrundArmsG A mr arms) : StmtG A mr (.onGrund r arms)
  | breaking {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (i : D.Inv) (body : Block D V l Γ Λ Λ') (hb : BlockG A mr body) :
      StmtG A mr (.breaking i body)
  | locks {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ))
      (hA : A L) (hb : BlockG A false body) : StmtG A mr (.locks L hr body)
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      StmtG A true (l := l) (.ret e hΛ)

inductive BlockG {V : Vertrag D} (A : D.Lock → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Prop where
  | nil {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      BlockG A mr (.nil : Block D V l Γ Λ Λ)
  | cons {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
      (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
      (hs : StmtG A mr s) (hr : BlockG A mr rest) : BlockG A mr (.cons s rest)
  | bind {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.bind e rest)
  | regLies {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hr : BlockG A mr rest) :
      BlockG A mr (.regLies r hk rest)
  | regLiesElse {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (D.rtyp r :: Γ) Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.regLiesElse r hk zusage sonst rest)
  | awaits {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.awaits g payload hp hL rest)
  | exchange {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
      (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') (hr : BlockG A mr rest) :
      BlockG A mr (.exchange g neu hw hL rest)
  | narrow {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
      (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (.int lo' hi' :: Γ) Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.narrow e lo' hi' sonst rest)
  | pruefung {Γ : Ctx} {Λ Λ' : List (Res D)}
      (c : Expr D Γ Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false Γ Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.pruefung c sonst rest)
  | gleit {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int}
      (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.gleit op a b lo hi rest)
  | gleitLit {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (q lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.gleitLit q lo hi rest)
  | gleitVon {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int}
      (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockG A mr rest) :
      BlockG A mr (.gleitVon e lo hi rest)
  | gleitNarrow {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
      (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (.fl lo hi :: Γ) Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.gleitNarrow e lo hi sonst rest)

/-- Covered end blocks: at loop level `false` (a function body), ending in
    `ret`, with covered statements (a `ret` allowed) and `let` bindings. -/
inductive EndG {V : Vertrag D} (A : D.Lock → Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Prop where
  | ret {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      EndG A (.ret (l := false) e hΛ)
  | cons {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V false Γ Λ Λ')
      (rest : Endblock D V false Γ Λ') (hs : StmtG A true s) (hr : EndG A rest) :
      EndG A (.cons s rest)
  | bind {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
      (rest : Endblock D V false (τ :: Γ) Λ) (hr : EndG A rest) :
      EndG A (.bind e rest)

inductive ArmsG {V : Vertrag D} (A : D.Lock → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → Prop where
  | nil {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      ArmsG A mr (.nil : Arms D V l Γ Λ Λ [])
  | cons {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      {c : Option (Int × Int)} {cs : List (Option (Int × Int))}
      (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs)
      (hb : BlockG A mr b) (hr : ArmsG A mr rest) : ArmsG A mr (.cons b rest)

inductive GrundArmsG {V : Vertrag D} (A : D.Lock → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n → Prop where
  | nil {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      GrundArmsG A mr (.nil : GrundArms D V l Γ Λ Λ 0)
  | cons {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
      (hb : BlockG A mr b) (hr : GrundArmsG A mr rest) : GrundArmsG A mr (.cons b rest)

end

/-- The statement forms of `StmtG`, as a decidable classifier. -/
def Stmt.gArt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Bool :=
  match s with
  | .ite .. | .onOption .. | .onTag .. | .onGrund .. | .breaking .. | .locks ..
  | .ret .. => true
  | s => s.blattArt

theorem StmtG.art {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : StmtG A mr s) : s.gArt = true := by
  cases h with
  | blatt _ hb => cases hb <;> rfl
  | _ => rfl

/-! Inversion lemmas: the simulation recurses on the SYNTAX, so it must not
    `cases` the coverage proof (that would rename the recursive subterms). -/

section Inv

variable {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}

theorem StmtG.ite_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {t e : Block D V l Γ Λ Λ'} (h : StmtG A mr (.ite c t e)) :
    BlockG A mr t ∧ BlockG A mr e := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | ite _ _ _ ht he => exact ⟨ht, he⟩

theorem StmtG.onOption_inv {Λ Λ' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {p : Block D V l (.index n :: Γ) Λ Λ'} {a : Block D V l Γ Λ Λ'}
    (h : StmtG A mr (.onOption o p a)) : BlockG A mr p ∧ BlockG A mr a := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | onOption _ _ _ hp ha => exact ⟨hp, ha⟩

theorem StmtG.onTag_inv {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D V l Γ Λ Λ' cs}
    (h : StmtG A mr (.onTag v arms)) : ArmsG A mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | onTag _ _ ha => exact ha

theorem StmtG.onGrund_inv {Λ Λ' : List (Res D)} {n : Nat}
    {r : Expr D Γ Λ (.grund n)} {arms : GrundArms D V l Γ Λ Λ' n}
    (h : StmtG A mr (.onGrund r arms)) : GrundArmsG A mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | onGrund _ _ ha => exact ha

theorem StmtG.breaking_inv {Λ Λ' : List (Res D)} {i : D.Inv}
    {body : Block D V l Γ Λ Λ'} (h : StmtG A mr (.breaking i body)) : BlockG A mr body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | breaking _ _ hb => exact hb

theorem StmtG.locks_inv {Λ : List (Res D)} {L : D.Lock}
    {hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L}
    {body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)}
    (h : StmtG A mr (.locks L hr body)) : A L ∧ BlockG A false body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | locks _ _ _ hA hb => exact ⟨hA, hb⟩

theorem StmtG.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : StmtG A mr (.ret (l := l) e hΛ)) : mr = true := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | ret _ _ => rfl

theorem BlockG.cons_inv {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} (h : BlockG A mr (.cons s rest)) :
    StmtG A mr s ∧ BlockG A mr rest := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr⟩

theorem BlockG.bind_inv {Λ Λ' : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Block D V l (τ :: Γ) Λ Λ'} (h : BlockG A mr (.bind e rest)) : BlockG A mr rest := by
  cases h with
  | bind _ _ hr => exact hr

theorem BlockG.regLies_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockG A mr (.regLies r hk rest)) : BlockG A mr rest := by
  cases h with
  | regLies _ _ _ hr => exact hr

theorem BlockG.awaits_inv {Λ Λ' : List (Res D)} {g : D.Glob} {payload : List D.Glob}
    {hp : payload = D.nutzlast g} {hL : gdarf D g Λ}
    {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockG A mr (.awaits g payload hp hL rest)) : BlockG A mr rest := by
  cases h with
  | awaits _ _ _ _ _ hr => exact hr

theorem BlockG.exchange_inv {Λ Λ' : List (Res D)} {g : D.Glob}
    {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {hw : V.gschreibt g = true}
    {hL : gdarf D g Λ} {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockG A mr (.exchange g neu hw hL rest)) : BlockG A mr rest := by
  cases h with
  | exchange _ _ _ _ _ hr => exact hr

theorem BlockG.gleit_inv {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int} {op : GleitOp}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.gleit op a b lo hi rest)) : BlockG A mr rest := by
  cases h with
  | gleit _ _ _ _ _ _ hr => exact hr

theorem BlockG.gleitLit_inv {Λ Λ' : List (Res D)} {q lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.gleitLit q lo hi rest)) : BlockG A mr rest := by
  cases h with
  | gleitLit _ _ _ _ hr => exact hr

theorem BlockG.gleitVon_inv {Λ Λ' : List (Res D)} {l1 h1 : Int}
    {e : Expr D Γ Λ (.int l1 h1)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.gleitVon e lo hi rest)) : BlockG A mr rest := by
  cases h with
  | gleitVon _ _ _ _ hr => exact hr

theorem BlockG.regLiesElse_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {zusage : Expr D (D.rtyp r :: Γ) Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockG A mr (.regLiesElse r hk zusage sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | regLiesElse _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockG.narrow_inv {Λ Λ' : List (Res D)} {lo hi : Int}
    {e : Expr D Γ Λ (.int lo hi)} {lo' hi' : Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.int lo' hi' :: Γ) Λ Λ'}
    (h : BlockG A mr (.narrow e lo' hi' sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | narrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockG.pruefung_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l Γ Λ Λ'}
    (h : BlockG A mr (.pruefung c sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | pruefung _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockG.gleitNarrow_inv {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
    {e : Expr D Γ Λ (.fl l1 h1)} {lo hi : Int × Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.gleitNarrow e lo hi sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | gleitNarrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem ArmsG.cons_inv {Λ Λ' : List (Res D)} {c : Option (Int × Int)}
    {cs : List (Option (Int × Int))} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {rest : Arms D V l Γ Λ Λ' cs} (h : ArmsG A mr (.cons b rest)) :
    BlockG A mr b ∧ ArmsG A mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem GrundArmsG.cons_inv {Λ Λ' : List (Res D)} {n : Nat}
    {b : Block D V l Γ Λ Λ'} {rest : GrundArms D V l Γ Λ Λ' n}
    (h : GrundArmsG A mr (.cons b rest)) : BlockG A mr b ∧ GrundArmsG A mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem EndG.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : EndG A (.ret (l := l) e hΛ)) : l = false := by
  cases h with
  | ret _ _ => rfl

theorem EndG.cons_inv {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : EndG A (.cons s rest)) :
    StmtG A true s ∧ EndG A rest ∧ l = false := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr, rfl⟩

theorem EndG.bind_inv {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D V l (τ :: Γ) Λ} (h : EndG A (.bind e rest)) : EndG A rest := by
  cases h with
  | bind _ _ hr => exact hr

end Inv

/-! ## 5. The step rules, re-stated over a thread state `z`

    Each `w_*` lemma fires one `RufSchrittG` constructor on a machine whose
    thread `f` IS `z` (`hz`), with every argument typed at `z.kopf.f`; the
    `subst` turns it into the constructor verbatim. Instantiated with a
    literal `z`, the arguments are typed at the literal's function. -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_blatt {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = .ok σ' ρ')
    (herw : Erw (M.weltVon f) σ') :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ' (.ende rest) σ' := by
  subst hz
  obtain ⟨neu, hneu, hnz⟩ := herw
  exact ⟨_, RufSchrittG.blatt M f l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu
    (kein_nimmt hnz), zustandG_neu rfl rfl⟩

theorem w_dannBlatt {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = .ok σ' ρ')
    (herw : Erw (M.weltVon f) σ') :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ' (.dann rest k) σ' := by
  subst hz
  obtain ⟨neu, hneu, hnz⟩ := herw
  exact ⟨_, RufSchrittG.dannBlatt M f l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu
    hstep hneu (kein_nimmt hnz), zustandG_neu rfl rfl⟩

theorem w_dannLeer {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann .nil k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannLeer M f l Γ Λ k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_endeEntf {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hent : GEntfaltbar s = true)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons s .nil) (.ende rest)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.endeEntf M f l Γ Λ Λ' s rest ρ hent hhead, zustandG_neu rfl rfl⟩

theorem w_iteWahr {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (c : Expr D Γ Λ .bool) (t e : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = true) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.dann t (.dann rest k))
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannIteWahr M f l Γ Λ Λ' Λ'' c t e rest k ρ hhead _ rfl hw _ rfl,
    zustandG_neu rfl rfl⟩

theorem w_iteFalsch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (c : Expr D Γ Λ .bool) (t e : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.dann e (.dann rest k))
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannIteFalsch M f l Γ Λ Λ' Λ'' c t e rest k ρ hhead _ rfl hw _ rfl,
    zustandG_neu rfl rfl⟩

theorem w_optSome {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {n : Int}
    (o : Expr D Γ Λ (.opt n))
    (p : Block D (vertragVon D z.kopf.f) l (.index n :: Γ) Λ Λ')
    (a : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
    (v : Wert D (.index n))
    (hv : eval ((M.weltVon f).lese Λ o.orte) o ((M.weltVon f).lese Λ o.orte) ρ =
      Option.some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann p (.schrumpf (.dann rest k))) ((M.weltVon f).lese Λ o.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnOptionSome M f l Γ Λ Λ' Λ'' n o p a rest k ρ hhead _ rfl
    v hv _ rfl, zustandG_neu rfl rfl⟩

theorem w_optNone {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {n : Int}
    (o : Expr D Γ Λ (.opt n))
    (p : Block D (vertragVon D z.kopf.f) l (.index n :: Γ) Λ Λ')
    (a : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
    (hv : eval ((M.weltVon f).lese Λ o.orte) o ((M.weltVon f).lese Λ o.orte) ρ =
      Option.none) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann a (.dann rest k)) ((M.weltVon f).lese Λ o.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnOptionNone M f l Γ Λ Λ' Λ'' n o p a rest k ρ hhead _ rfl
    hv _ rfl, zustandG_neu rfl rfl⟩

theorem w_tagSome {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
    (arms : Arms D (vertragVon D z.kopf.f) l Γ Λ Λ' cs)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
    (lo hi : Int)
    (b : Block D (vertragVon D z.kopf.f) l (.int lo hi :: Γ) Λ Λ')
    (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval ((M.weltVon f).lese Λ v.orte) v
      ((M.weltVon f).lese Λ v.orte) ρ) = ⟨some (lo, hi), b, nutz⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (armEnv nutz ρ)
        (.dann b (.schrumpf (.dann rest k))) ((M.weltVon f).lese Λ v.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnTagSome M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead _ rfl
    lo hi b nutz hw _ rfl, zustandG_neu rfl rfl⟩

theorem w_tagNone {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
    (arms : Arms D (vertragVon D z.kopf.f) l Γ Λ Λ' cs)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
    (b : Block D (vertragVon D z.kopf.f) l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval ((M.weltVon f).lese Λ v.orte) v
      ((M.weltVon f).lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (armEnv nutz ρ)
        (.dann b (.dann rest k)) ((M.weltVon f).lese Λ v.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnTagNone M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead _ rfl
    b nutz hw _ rfl, zustandG_neu rfl rfl⟩

theorem w_grund {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {n : Nat}
    (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D (vertragVon D z.kopf.f) l Γ Λ Λ' n)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onGrund r arms) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (grundWahlG arms (eval ((M.weltVon f).lese Λ r.orte) r
          ((M.weltVon f).lese Λ r.orte) ρ)) (.dann rest k)) ((M.weltVon f).lese Λ r.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnGrund M f l Γ Λ Λ' Λ'' n r arms rest k ρ hhead _ rfl
    _ rfl _ rfl, zustandG_neu rfl rfl⟩

theorem w_breaking {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (i : D.Inv) (body : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.breaking i body) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBreaking M f l Γ Λ Λ' Λ'' i body rest k ρ hhead,
    zustandG_neu rfl rfl⟩

theorem w_locks {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (hfrei : RufFreiG M f L) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.frei L (.dann rest k))) ((M.weltVon f).nimmt L) := by
  subst hz
  have hn := nicht_gehalten L hr hΛ
  exact ⟨_, RufSchrittG.dannLocks M f l Γ Λ Λ'' L hr body rest k ρ hhead hn.2 hn.1 hfrei,
    zustandG_neu rfl rfl⟩

theorem w_freiGib {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (L : D.Lock) (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).gibt L) := by
  subst hz
  exact ⟨_, RufSchrittG.freiGib M f l Γ Λ L k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_schrumpf {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (v : Wert D τ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, τ :: Γ, Λ, .cons v ρ, .schrumpf k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.schrumpfVergiss M f l Γ Λ τ k v ρ hhead, zustandG_neu rfl rfl⟩

theorem w_endeBind {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (rest : Endblock D (vertragVon D z.kopf.f) l (τ :: Γ) Λ)
    (ρ : Env D Γ) (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bind e rest)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ) ρ)
        (.ende rest) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.endeBind M f l Γ Λ τ e rest ρ hhead _ rfl _ rfl, zustandG_neu rfl rfl⟩

theorem w_dannBind {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bind e rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ) ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBind M f l Γ Λ Λ' Λ' τ e rest k ρ hhead _ rfl _ rfl,
    zustandG_neu rfl rfl⟩

theorem w_narrowOk {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (lo' hi' : Int) (e : Expr D Γ Λ (.int lo hi))
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
    {σ : World D} (hW : M.weltVon f = σ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
        (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) := by
  subst hz
  subst hW
  exact ⟨_, RufSchrittG.dannNarrowOk M f l Γ Λ Λ' Λ' lo hi lo' hi' e sonst rest k ρ hhead
    _ rfl h _ rfl, zustandG_neu rfl rfl⟩

theorem w_narrowElse {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (lo' hi' : Int) (e : Expr D Γ Λ (.int lo hi))
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
    (h : ¬ (lo' ≤ (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ).n ∧
      (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ).n ≤ hi')) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ende sonst) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannNarrowElse M f l Γ Λ Λ' Λ' lo hi lo' hi' e sonst rest k ρ hhead
    _ rfl h _ rfl, zustandG_neu rfl rfl⟩

theorem w_pruefWahr {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.pruefung c sonst rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = true) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.dann rest k)
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannPruefWahr M f l Γ Λ Λ' Λ' c sonst rest k ρ hhead _ rfl hw _ rfl,
    zustandG_neu rfl rfl⟩

theorem w_pruefFalsch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.pruefung c sonst rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.ende sonst)
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannPruefFalsch M f l Γ Λ Λ' Λ' c sonst rest k ρ hhead _ rfl hw _ rfl,
    zustandG_neu rfl rfl⟩

theorem w_regLies {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D (vertragVon D z.kopf.f) l (D.rtyp r :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.regLies r hk rest) k⟩)
    (v : Wert D (D.rtyp r))
    (hv : einpassen (D.rtyp r) (O.regLies r (M.weltVon f)) = some v)
    (hzs : D.rzusage r v = true) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRegLies M f l Γ Λ Λ' r hk rest k ρ hhead v hv hzs,
    zustandG_neu rfl rfl⟩

theorem w_regLiesElseWahr {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.rtyp r :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.regLiesElse r hk zusage sonst rest) k⟩)
    (v : Wert D (D.rtyp r))
    (hv : einpassen (D.rtyp r) (O.regLies r (M.weltVon f)) = some v)
    (hw : wahr? (eval ((M.weltVon f).lese Λ zusage.orte) zusage
      ((M.weltVon f).lese Λ zusage.orte) (.cons v ρ)) = true) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ zusage.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRegLiesElseWahr M f l Γ Λ Λ' r hk zusage sonst rest k ρ hhead
    v hv _ rfl hw _ rfl, zustandG_neu rfl rfl⟩

theorem w_regLiesElseFalsch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.rtyp r :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.regLiesElse r hk zusage sonst rest) k⟩)
    (v : Wert D (D.rtyp r))
    (hv : einpassen (D.rtyp r) (O.regLies r (M.weltVon f)) = some v)
    (hw : wahr? (eval ((M.weltVon f).lese Λ zusage.orte) zusage
      ((M.weltVon f).lese Λ zusage.orte) (.cons v ρ)) = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ende sonst) ((M.weltVon f).lese Λ zusage.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRegLiesElseFalsch M f l Γ Λ Λ' r hk zusage sonst rest k ρ hhead
    v hv _ rfl hw _ rfl, zustandG_neu rfl rfl⟩

theorem w_awaits {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
    (hL : gdarf D g Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.awaits g payload hp hL rest) k⟩)
    (hvis : O.sichtbar g (M.weltVon f) = true) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (((M.weltVon f).lese Λ [.inr g]).globs g) ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ [.inr g]) := by
  subst hz
  exact ⟨_, RufSchrittG.dannAwaits M f l Γ Λ Λ' g payload hp hL rest k ρ hhead hvis _ rfl
    _ rfl, zustandG_neu rfl rfl⟩

theorem w_exchange {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g : D.Glob) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
    (hw : (vertragVon D z.kopf.f).gschreibt g = true) (hL : gdarf D g Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.exchange g neuE hw hL rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ)
        (.dann rest (.schrumpf k))
        (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) neuE
            ((M.weltVon f).lese Λ (.inr g :: neuE.orte))
            (.cons (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ))) := by
  subst hz
  exact ⟨_, RufSchrittG.dannExchange M f l Γ Λ Λ' g neuE hw hL rest k ρ hhead _ rfl _ rfl
    ([Ereignis.gzugriff g true Λ ((M.weltVon f).lese Λ (.inr g :: neuE.orte)).haelt] ++
      leseEv (M.weltVon f) Λ (.inr g :: neuE.orte))
    (by rw [List.append_assoc]; rfl), zustandG_neu rfl rfl⟩

theorem w_gleit {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l₁ h₁))
    (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleit op a b lo hi rest) k⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval ((M.weltVon f).lese Λ (a.orte ++ b.orte)) a
        ((M.weltVon f).lese Λ (a.orte ++ b.orte)) ρ).x
      (eval ((M.weltVon f).lese Λ (a.orte ++ b.orte)) b
        ((M.weltVon f).lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ (a.orte ++ b.orte)) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleit M f l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead
    _ rfl v hv _ rfl, zustandG_neu rfl rfl⟩

theorem w_gleitLit {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q lo hi : Int × Int)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleitLit q lo hi rest) k⟩)
    (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitLit M f l Γ Λ Λ' q lo hi rest k ρ hhead v hv,
    zustandG_neu rfl rfl⟩

theorem w_gleitVon {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁)) (lo hi : Int × Int)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleitVon e lo hi rest) k⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (Float.ofInt (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).n) = some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitVon M f l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead _ rfl v hv
    _ rfl, zustandG_neu rfl rfl⟩

theorem w_gleitNarrowOk {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ : Int × Int} (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleitNarrow e lo hi sonst rest) k⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).x = some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitNarrowOk M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead
    _ rfl v hv _ rfl, zustandG_neu rfl rfl⟩

theorem w_gleitNarrowElse {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ : Int × Int} (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleitNarrow e lo hi sonst rest) k⟩)
    (hn : gleitPasst lo hi (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).x = none) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.ende sonst)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitNarrowElse M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead
    _ rfl hn _ rfl, zustandG_neu rfl rfl⟩

theorem w_rueck {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨false, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rueck M f caller rst hpop Γ Λ e hperm ρ hhead _ rfl
    (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl, gepopptG_neu rfl rfl⟩

theorem w_rueckCons {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Endblock D (vertragVon D z.kopf.f) false Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨false, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rueckCons M f caller rst hpop Γ Λ e hperm rest ρ hhead _ rfl
    (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl, gepopptG_neu rfl rfl⟩

theorem w_dannRet {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRet M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ
    _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl _ rfl, gepopptG_neu rfl rfl⟩

end Schritte

/-! ## 6. Sequential inversion lemmas -/

section Inversion

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem schrumpf_ok {τ : Ty} {o : Ausgang V l (τ :: Γ)} {σ' : World D} {ρ' : Env D Γ}
    (h : o.schrumpf = .ok σ' ρ') : ∃ v, o = .ok σ' (.cons v ρ') := by
  cases o with
  | ok σ ρ =>
      cases ρ with
      | cons v ρt =>
          simp only [Ausgang.schrumpf, Env.tail, Ausgang.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨v, rfl⟩
  | _ => simp [Ausgang.schrumpf] at h

theorem schrumpf_zurueck {τ : Ty} {o : Ausgang V l (τ :: Γ)} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.schrumpf = .zurueck σ' v) : o = .zurueck σ' v := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem endSchrumpf_zurueck {τ : Ty} {o : EndAusgang V l (τ :: Γ)} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.schrumpf = .zurueck σ' v) : o = .zurueck σ' v := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem mapWelt_ok {o : Ausgang V l Γ} {g : World D → World D} {σ' : World D}
    {ρ' : Env D Γ} (h : o.mapWelt g = .ok σ' ρ') : ∃ σ1, o = .ok σ1 ρ' ∧ σ' = g σ1 := by
  cases o with
  | ok σ ρ =>
      simp only [Ausgang.mapWelt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ, rfl, rfl⟩
  | _ => simp [Ausgang.mapWelt] at h

theorem mapWelt_zurueck {o : Ausgang V l Γ} {g : World D → World D} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.mapWelt g = .zurueck σ' v) :
    ∃ σ1, o = .zurueck σ1 v ∧ σ' = g σ1 := by
  cases o with
  | zurueck σ w =>
      simp only [Ausgang.mapWelt, Ausgang.zurueck.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ, rfl, rfl⟩
  | _ => simp [Ausgang.mapWelt] at h

theorem zuAusgang_ne_ok (o : EndAusgang V l Γ) (σ' : World D) (ρ' : Env D Γ) :
    o.zuAusgang ≠ .ok σ' ρ' := by
  cases o <;> simp [EndAusgang.zuAusgang]

theorem zuAusgang_zurueck {o : EndAusgang V l Γ} {σ' : World D} {v : ErgVal D V.erg}
    (h : o.zuAusgang = .zurueck σ' v) : o = .zurueck σ' v := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem execBlock_cons_ok (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    {σ σ' : World D} {ρ ρ' : Env D Γ}
    (h : execBlock O passes R (.cons s rest) σ ρ = .ok σ' ρ') :
    ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
      execBlock O passes R rest σ1 ρ1 = .ok σ' ρ' := by
  simp only [execBlock] at h
  split at h
  · rename_i σ1 ρ1 hs
    exact ⟨σ1, ρ1, hs, h⟩
  · rename_i hne
    exact absurd h (hne σ' ρ')

theorem execBlock_cons_zurueck (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    {σ σ' : World D} {ρ : Env D Γ} {v : ErgVal D V.erg}
    (h : execBlock O passes R (.cons s rest) σ ρ = .zurueck σ' v) :
    execStmt O passes R s σ ρ = .zurueck σ' v ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        execBlock O passes R rest σ1 ρ1 = .zurueck σ' v := by
  simp only [execBlock] at h
  split at h
  · rename_i σ1 ρ1 hs
    exact Or.inr ⟨σ1, ρ1, hs, h⟩
  · exact Or.inl h

theorem execEnd_cons_zurueck (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    {σ σ' : World D} {ρ : Env D Γ} {v : ErgVal D V.erg}
    (h : execEnd O passes R (.cons s rest) σ ρ = .zurueck σ' v) :
    execStmt O passes R s σ ρ = .zurueck σ' v ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        execEnd O passes R rest σ1 ρ1 = .zurueck σ' v := by
  simp only [execEnd] at h
  split at h
  · rename_i σ1 ρ1 hs
    exact Or.inr ⟨σ1, ρ1, hs, h⟩
  · rename_i σ1 w hs
    simp only [EndAusgang.zurueck.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl hs
  all_goals simp at h

/-- `execArms` runs the arm `armWahlG` selects. -/
theorem execArms_wahl (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
      (σ : World D) (ρ : Env D Γ),
    execArms O passes R arms v σ ρ =
      (execBlock O passes R (armWahlG arms v).2.1 σ (armEnv (armWahlG arms v).2.2 ρ)).schrumpfArm
        (armWahlG arms v).1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArms, armWahlG]
      exact execArms_wahl O passes R rest _ σ ρ

/-- `execGrund` runs the arm `grundWahlG` selects. -/
theorem execGrund_wahl (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrund O passes R arms r σ ρ = execBlock O passes R (grundWahlG arms r) σ ρ
  | _, .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨k + 1, h⟩, σ, ρ => by
      simp only [execGrund, grundWahlG]
      exact execGrund_wahl O passes R rest _ σ ρ

/-- `execGrund_wahl` with the selector typed as a `Wert`, as `execStmt` passes it. -/
theorem execGrund_wahlW (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Λ Λ' : List (Res D)}
    {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Wert D (.grund n)) (σ : World D)
    (ρ : Env D Γ) :
    execGrund O passes R arms r σ ρ = execBlock O passes R (grundWahlG arms r) σ ρ :=
  execGrund_wahl O passes R arms r σ ρ

end Inversion

theorem heldGenau_lese {Λ Λ₀ : List (Res D)} {σ : World D} (os : List (D.Tab ⊕ D.Glob))
    (h : HeldGenau Λ (offen σ.spur)) : HeldGenau Λ (offen (σ.lese Λ₀ os).spur) := by
  rw [(Erw.lese σ Λ₀ os).offen]
  exact h

theorem heldGenau_iff {Λ Λ' : List (Res D)} {hs : List D.Lock}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (h : HeldGenau Λ hs) : HeldGenau Λ' hs := by
  intro L
  rw [hm L]
  exact h L

theorem offen_gibt_nimmt (σ σ1 : World D) (L : D.Lock)
    (h : offen σ1.spur = offen (σ.nimmt L).spur) :
    offen (σ1.gibt L).spur = offen σ.spur := by
  show (offen σ1.spur).erase L = offen σ.spur
  rw [h]
  show (L :: offen σ.spur).erase L = offen σ.spur
  exact List.erase_cons_head L _

/-! ## 7. Normal completion: the machine reaches the continuation -/

section SimOk

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (log : List (RufEreignisF D)) (A : D.Lock → Prop)

/-- Block simulation, normal completion: `dann b k` at `σ, ρ` runs (steps of
    `f` only) to `k` at the world and environment `execBlock` returns. -/
def SimOkB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ ρ' : Env D Γ), execBlock O passes keinRuf b σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldGenau Λ (offen σ.spur) →
    FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ ZustandG M' f stapel fn rho s0 log ρ' k σ' ∧
      offen σ'.spur = offen σ.spur

/-- Statement simulation, normal completion: `dann (s; rest) k` runs to
    `dann rest k`. -/
def SimOkS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ ρ' : Env D Γ), execStmt O passes keinRuf s σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 log ρ' (.dann rest k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- A covered leaf: one `dannBlatt` step. -/
theorem blattOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimOkS P O passes f fn stapel rho s0 log A s := by
  intro σ σ' ρ ρ' hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  have herw := h.erw O passes keinRuf σ σ' ρ ρ' hex
  obtain ⟨M', hs, hZ'⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) hZ.1 s rest k ρ
    h.istBlatt rfl hΛ σ' ρ' (by rw [hW]; exact hex) (by rw [hW]; exact herw)
  exact ⟨M', RufLaufG.einzeln hs, hZ', herw.offen⟩

/-- A `schrumpf` layer after a sub-block: one `schrumpfVergiss` step. -/
theorem schrumpfOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {M : RufMaschineG D} {k : GRest D (vertragVon D fn) l Γ Λ} {v : Wert D τ}
    {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log (.cons v ρ) (.schrumpf k) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧ ZustandG M' f stapel fn rho s0 log ρ k σ := by
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_schrumpf (P := P) (O := O) (passes := passes) hZ.1 k v ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩


mutual

theorem stmtOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtG A mr s →
    SimOkS P O passes f fn stapel rho s0 log A s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignGlob g e hw hL)
  | _, _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignVar x e)
  | _, _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regSchreib r hk e, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.regSchreib r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk t ht _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk e he _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk p hp _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hv
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk a ha _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, Λ₀, _, .onTag v arms, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsOk arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = w
        at hex hsim
      obtain ⟨c, b, nutz⟩ := w
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨w', hw'⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ hw' M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onGrund r arms, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes keinRuf arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := grundOk arms ha _ _ _ _ _ hex M1 _ hZ1
        (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .call .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hAL, hb⟩ := hs.locks_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨σ1, hb1, rfl⟩ := mapWelt_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_locks (P := P) (O := O) (passes := passes) hZ.1
        L hr body rest k ρ rfl hΛ (hA L hAL)
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk body hb _ _ _ _ hb1 M1 _ hZ1
        (heldGenau_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      have hW2 := hZ2.welt
      obtain ⟨M3, hs3, hZ3⟩ := w_freiGib (P := P) (O := O) (passes := passes) hZ2.1
        L (.dann rest k) ρ' rfl
      rw [hW2] at hZ3
      exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        offen_gibt_nimmt σ σ1 L ho2⟩
  | _, _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk body hb _ _ _ _ hex M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .traverse .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .retry .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .forever .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .ret .., _ => by
      intro σ σ' ρ ρ' hex
      simp [execStmt] at hex
  | _, _, _, _, _, .retGrund .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .leave .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .next .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockG A mr b →
    SimOkB P O passes f fn stapel rho s0 log A b
  | _, _, _, _, _, .nil, _ => by
      intro σ σ' ρ ρ' hex M k hZ _ _
      simp only [execBlock, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      have hW := hZ.welt
      obtain ⟨M1, hs1, hZ1⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ.1 k ρ rfl
      rw [hW] at hZ1
      exact ⟨M1, RufLaufG.einzeln hs1, hZ1, rfl⟩
  | _, _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      obtain ⟨σ1, ρ1, hs1, hr1⟩ := execBlock_cons_ok O passes keinRuf s rest hex
      obtain ⟨M1, hl1, hZ1, ho1⟩ := stmtOk s hs _ _ _ _ hs1 M rest k hZ hΛ hA
      have hΛ1 := heldGenau_iff (s.held_iff) hΛ
      rw [← ho1] at hΛ1
      obtain ⟨M2, hl2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hr1 M1 k hZ1 hΛ1 (hA.lauf hl1)
      exact ⟨M2, hl1.trans hl2, hZ2, by rw [ho2, ho1]⟩
  | _, _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
        (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
      exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .regLies r hk rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hzs
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
          rw [hW] at hZ1
          obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
            hΛ (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
          exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
        · cases hex
      · cases hex
  | _, _, _, _, _, .regLiesElse r hk zusage sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLiesElse_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hw0
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl v (by rw [hW]; exact hv)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
            (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
          exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        · exact absurd hex (zuAusgang_ne_ok _ _ _)
      · cases hex
  | _, _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw'⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw' M1 _ hZ1
        (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
      exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, herw.offen]⟩
  | _, _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.narrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .pruefung c sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.pruefung_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .gleit op a b lo hi rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .gleitLit q lo hi rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl v hv
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          hΛ (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
      · cases hex
  | _, _, _, _, _, .gleitVon e lo hi rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .gleitNarrow e lo hi sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitNarrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes)
          hZ.1 e lo hi sonst rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)

theorem armsOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsG A mr arms → ∀ (v : Wert D (.sum cs)),
    SimOkB P O passes f fn stapel rho s0 log A (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockOk b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsOk rest ha.cons_inv.2 _

theorem grundOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsG A mr arms →
    ∀ (r : Fin n), SimOkB P O passes f fn stapel rho s0 log A (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockOk b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundOk rest ha.cons_inv.2 _

end

end SimOk

/-! ## 8. Under a `locks` body nothing returns -/

section KeinRueck

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop)

/-- A block never ends in `.zurueck`. -/
def KeinRueckB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
    execBlock O passes keinRuf b σ ρ ≠ .zurueck σ' v

mutual

theorem stmtKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtG A false s →
    ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
      execStmt O passes keinRuf s σ ρ ≠ .zurueck σ' v
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignGlob g e hw hL)
  | _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.assignVar x e)
  | _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regSchreib r hk e, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.regSchreib r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      BlattG.nicht_zurueck O passes keinRuf (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ v hex
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [execStmt] at hex
      split at hex
      · exact blockKein t ht _ _ _ _ hex
      · exact blockKein e he _ _ _ _ hex
  | _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ v hex
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [execStmt] at hex
      split at hex
      · exact blockKein p hp _ _ _ _ (schrumpf_zurueck hex)
      · exact blockKein a ha _ _ _ _ hex
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro σ σ' ρ v hex
      have ha := hs.onTag_inv
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hk := armsKein arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x at hex hk
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none => exact hk _ _ _ _ hex
      | some lh => exact hk _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .onGrund r arms, hs => by
      intro σ σ' ρ v hex
      have ha := hs.onGrund_inv
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes keinRuf arms] at hex
      exact grundKein arms ha _ _ _ _ _ hex
  | _, _, _, _, .call .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ v hex
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [execStmt] at hex
      obtain ⟨σ1, h1, _⟩ := mapWelt_zurueck hex
      exact blockKein body hb _ _ _ _ h1
  | _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ v hex
      have hb := hs.breaking_inv
      simp only [execStmt] at hex
      exact blockKein body hb _ _ _ _ hex
  | _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .ret .., hs => absurd hs.ret_inv (by decide)
  | _, _, _, _, .retGrund .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockG A false b → KeinRueckB O passes b
  | _, _, _, _, .nil, _ => by
      intro σ σ' ρ v hex
      simp [execBlock] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ v hex
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, _, h⟩
      · exact stmtKein s hs _ _ _ _ h
      · exact blockKein rest hr _ _ _ _ h
  | _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.bind_inv
      simp only [execBlock] at hex
      exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .regLies r hk rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.regLies_inv
      simp only [execBlock] at hex
      split at hex
      · split at hex
        · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
        · cases hex
      · cases hex
  | _, _, _, _, .regLiesElse .., hb => absurd hb.regLiesElse_inv.1 (by decide)
  | _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.awaits_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.exchange_inv
      simp only [execBlock] at hex
      exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .narrow .., hb => absurd hb.narrow_inv.1 (by decide)
  | _, _, _, _, .pruefung .., hb => absurd hb.pruefung_inv.1 (by decide)
  | _, _, _, _, .gleit op a b lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleit_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .gleitLit q lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleitLit_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .gleitVon e lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleitVon_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKein rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .gleitNarrow .., hb => absurd hb.gleitNarrow_inv.1 (by decide)

theorem armsKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsG A false arms → ∀ (v : Wert D (.sum cs)),
    KeinRueckB O passes (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockKein b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsKein rest ha.cons_inv.2 _

theorem grundKein : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A false arms →
    ∀ (r : Fin n), KeinRueckB O passes (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockKein b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundKein rest ha.cons_inv.2 _

end

end KeinRueck

/-! ## 9. Statements at `ende` position: `blatt`, or `endeEntf` into `dann` -/

section Ende

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (log : List (RufEreignisF D)) (A : D.Lock → Prop)

/-- A covered statement at `ende (s; rest)` that ends normally runs to
    `ende rest`: a leaf by `blatt`, a compound by `endeEntf`, its `dann`
    simulation and `dannLeer`. -/
theorem endeConsOk {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtG A mr s)
    (hok : SimOkS P O passes f fn stapel rho s0 log A s)
    (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hex : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ M', RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 log ρ' (.ende rest) σ' ∧
      offen σ'.spur = offen σ.spur := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ M', RufLaufG P O passes f M M' ∧
        ZustandG M' f stapel fn rho s0 log ρ' (.ende rest) σ' ∧
        offen σ'.spur = offen σ.spur := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    obtain ⟨M2, hr2, hZ2, ho2⟩ := hok σ σ' ρ ρ' hex M1 .nil (.ende rest) hZ1 hΛ
      (hA.lauf (RufLaufG.einzeln hs1))
    have hW2 := hZ2.welt
    obtain ⟨M3, hs3, hZ3⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ2.1
      (.ende rest) ρ' rfl
    rw [hW2] at hZ3
    exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  cases hs with
  | blatt _ h =>
    have herw := h.erw O passes keinRuf σ σ' ρ ρ' hex
    obtain ⟨M1, hs1, hZ1⟩ := w_blatt (P := P) (O := O) (passes := passes) hZ.1 s rest ρ
      h.istBlatt rfl hΛ σ' ρ' (by rw [hW]; exact hex) (by rw [hW]; exact herw)
    exact ⟨M1, RufLaufG.einzeln hs1, hZ1, herw.offen⟩
  | ret _ _ => simp [execStmt] at hex
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onGrund => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

end Ende

/-! ## 10. Return: the machine pops with the value `execBlock` returns -/

section SimRet

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (log : List (RufEreignisF D)) (A : D.Lock → Prop)

/-- Block simulation, return: `dann b k` pops the frame with the value and
    the world `execBlock` returns. -/
def SimRetB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg),
    execBlock O passes keinRuf b σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann b k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ'

/-- Statement simulation, return, at `dann (s; rest) k`. -/
def SimRetS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg),
    execStmt O passes keinRuf s σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ'

/-- End-block simulation, return, at `ende e`. -/
def SimRetE {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ) : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg),
    execEnd O passes keinRuf e σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende e) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ'

theorem blattRet {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimRetS P O passes f fn caller rst rho s0 log A s := by
  intro σ σ' ρ v hex
  exact absurd hex (h.nicht_zurueck O passes keinRuf σ σ' ρ v)

/-- Lift a pop after one step. -/
theorem gepoppt_vor {M M1 : RufMaschineG D} {v : ErgVal D (D.erg fn)} {σ' : World D}
    (hs : RufSchrittG P O passes M f M1)
    (h : ∃ M', RufLaufG P O passes f M1 M' ∧ GepopptG M' f caller rst fn rho s0 log v σ') :
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
  obtain ⟨M', hr, hG⟩ := h
  exact ⟨M', RufLaufG.schritt hs hr, hG⟩

/-- Lift a pop after a run. -/
theorem gepoppt_lauf {M M1 : RufMaschineG D} {v : ErgVal D (D.erg fn)} {σ' : World D}
    (hl : RufLaufG P O passes f M M1)
    (h : ∃ M', RufLaufG P O passes f M1 M' ∧ GepopptG M' f caller rst fn rho s0 log v σ') :
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
  obtain ⟨M', hr, hG⟩ := h
  exact ⟨M', hl.trans hr, hG⟩

/-- A statement at `ende (s; rest)` that returns: `rueckCons` for `ret`,
    `endeEntf` and the `dann` simulation for a compound. -/
theorem endeConsRet {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtG A true s) (hl : l = false)
    (hret : SimRetS P O passes f fn caller rst rho s0 log A s)
    (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg)
    (hex : execStmt O passes keinRuf s σ ρ = .zurueck σ' v) (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ M', RufLaufG P O passes f M M' ∧ GepopptG M' f caller rst fn rho s0 log v σ' := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
      (hret σ σ' ρ v hex M1 .nil (.ende rest) hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  cases hs with
  | blatt _ h => exact absurd hex (h.nicht_zurueck O passes keinRuf σ σ' ρ v)
  | ret e hperm =>
    subst hl
    simp only [execStmt, Ausgang.zurueck.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    obtain ⟨M1, hs1, hG⟩ := w_rueckCons (P := P) (O := O) (passes := passes) hZ.1
      caller rst rfl e hperm rest ρ rfl hΛ
    rw [hW] at hG
    exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onGrund => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

mutual

theorem stmtRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtG A true s →
    SimRetS P O passes f fn caller rst rho s0 log A s
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignGlob g e hw hL)
  | _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A
        (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.assignVar x e)
  | _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A
        (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regSchreib r hk e, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.regSchreib r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      blattRet P O passes f fn caller rst rho s0 log A (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet t ht _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet e he _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet p hp _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet a ha _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsRet arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x
        at hex hsim
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (hsim _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (hsim _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onGrund r arms, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes keinRuf arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (grundRet arms ha _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .call .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ v hex
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [execStmt] at hex
      obtain ⟨σ1, h1, _⟩ := mapWelt_zurueck hex
      exact absurd h1 (blockKein O passes A body hb _ _ _ _)
  | _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (blockRet body hb _ _ _ _ hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .ret e hperm, _ => by
      intro σ σ' ρ v hex M _ rest k hZ hΛ _
      have hW := hZ.welt
      simp only [execStmt, Ausgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRet (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl e hperm rest k ρ rfl hΛ
      rw [hW] at hG
      exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | _, _, _, _, .retGrund .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockG A true b →
    SimRetB P O passes f fn caller rst rho s0 log A b
  | _, _, _, _, .nil, _ => by
      intro σ σ' ρ v hex
      simp [execBlock] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtRet s hs _ _ _ _ h M rest k hZ hΛ hA
      · obtain ⟨M1, hl1, hZ1, ho1⟩ := stmtOk P O passes f fn (caller :: rst) rho s0 log A
          s hs _ _ _ _ h1 M rest k hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_lauf P O passes f fn caller rst rho s0 log hl1
          (blockRet rest hr _ _ _ _ h2 M1 k hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .regLies r hk rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hzs
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl w (by rw [hW]; exact hw) hzs
          rw [hW] at hZ1
          exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
            (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
              (hA.lauf (RufLaufG.einzeln hs1)))
        · cases hex
      · cases hex
  | _, _, _, _, .regLiesElse r hk zusage sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.regLiesElse_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hw0
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
            (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
        · rename_i hw0
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseFalsch (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; simpa using hw0)
          rw [hW] at hZ1
          exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
            (endRet sonst hs _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1
          (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hin
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowElse (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl (by rw [hW]; exact hin)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (endRet sonst hs _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .pruefung c sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefFalsch (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (endRet sonst hs _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .gleit op a b lo hi rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .gleitLit q lo hi rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl w hw
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .gleitVon e lo hi rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .gleitNarrow e lo hi sonst rest, hb => by
      intro σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (blockRet rest hr _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hn
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl (by rw [hW]; exact hn)
        rw [hW] at hZ1
        exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
          (endRet sonst hs _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))

theorem endRet : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ), EndG A e →
    SimRetE P O passes f fn caller rst rho s0 log A e
  | _, _, _, .ret e hperm, he => by
      intro σ σ' ρ v hex M hZ hΛ _
      have hl := he.ret_inv
      subst hl
      have hW := hZ.welt
      simp only [execEnd, EndAusgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_rueck (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl e hperm ρ rfl hΛ
      rw [hW] at hG
      exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | _, _, _, .retGrund .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro σ σ' ρ v hex M hZ hΛ hA
      obtain ⟨hs, hr, hl⟩ := he.cons_inv
      rcases execEnd_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact endeConsRet P O passes f fn caller rst rho s0 log A hs hl (stmtRet s hs)
          σ σ' ρ v h M rest hZ hΛ hA
      · obtain ⟨M1, hl1, hZ1, ho1⟩ := endeConsOk P O passes f fn (caller :: rst) rho s0 log A
          hs (stmtOk P O passes f fn (caller :: rst) rho s0 log A s hs) σ σ1 ρ ρ1 h1 M rest
          hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_lauf P O passes f fn caller rst rho s0 log hl1
          (endRet rest hr _ _ _ _ h2 M1 hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, .bind e rest, he => by
      intro σ σ' ρ v hex M hZ hΛ hA
      have hr := he.bind_inv
      have hW := hZ.welt
      simp only [execEnd] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_endeBind (P := P) (O := O) (passes := passes) hZ.1
        e rest ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vor P O passes f fn caller rst rho s0 log hs1
        (endRet rest hr _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))

theorem armsRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsG A true arms → ∀ (v : Wert D (.sum cs)),
    SimRetB P O passes f fn caller rst rho s0 log A (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockRet b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsRet rest ha.cons_inv.2 _

theorem grundRet : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsG A true arms →
    ∀ (r : Fin n), SimRetB P O passes f fn caller rst rho s0 log A (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockRet b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundRet rest ha.cons_inv.2 _

end

end SimRet

/-! ## 11. TARGET A: the machine realises the sequential result -/

/-- **TARGET A -- adequacy of the call machine G for call-free bodies.**
    Thread `f` of `M` runs a frame of `fn` (actual parameters `rho`, entry
    world `s0`) above a caller frame, with residue `.ende b` for a covered
    (call-free, `EndG`) end block `b` at environment `ρ`; its static
    holdings `Λ` name exactly the locks its trace holds; no other thread
    holds a lock `b` may take (`A`). If the sequential semantics, started at
    the thread's current world `M.weltVon f`, returns `v` in world `σ'`,
    then steps of thread `f` alone reach a machine `M'` that has popped the
    frame, logged `rueck fn rho v s0 σ'` with THE SAME value `v`, and whose
    shared memory is `σ'.speicher`.

    How the machine's read world relates: the `rueck` step reads the result
    at `s1 = (M'.weltVon f).lese Λ e.orte` (`e` the returned expression)
    and logs `s1`; `execEnd`'s `ret` returns `σ.lese Λ e.orte`. The theorem
    shows these are EQUAL: the logged `s1` IS `σ'` -- trace included --
    and the new memory is `s1.speicher = σ'.speicher`. Other threads are
    untouched. -/
theorem rufG_adaequat (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndG A b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes keinRuf b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ M', RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  have hsp : (M.weltVon f).spur = spur := by
    show (M.faeden f).spur = spur
    rw [hM]
  have hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende b) (M.weltVon f) :=
    ⟨by rw [hsp]; exact hM, rfl⟩
  obtain ⟨M', hl, hG⟩ := endRet P O passes f fn caller rst rho s0 log A b hb
    (M.weltVon f) σ' ρ v hexec M hZ (by rw [hsp]; exact hΛ) hfrei
  exact ⟨M', hl, hG.1, hG.2, rufLaufG_fremd hl⟩

-- @ENDE

