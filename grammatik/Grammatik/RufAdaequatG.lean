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

  Main results: `rufG_adaequat` (TARGET A), `rufG_adaequat_R` (A under any
  call handler), `rufG_adaequat_umkehr` (TARGET B: every f-only run that
  pops the frame logs the value `execEnd` returns -- proved through a frame
  semantics `semR` that each of the 70 step rules preserves,
  `schrittErhalt`), with witnesses `rufG_adaequat_zeuge`,
  `rufG_adaequat_umkehr_zeuge`. Two findings against G's rules were
  machine-checked here (`traverse` with a false invariant; `ruf` re-entering
  the callee after `rueck`); both rule families are repaired in
  `RufMaschineG.lean`, and the findings became agreement theorems
  (`trav_falsch_steht`, `trav_einig`, `ruf_fortsetzung`). Bodies WITH calls:
  `RufAdaequatRufG.lean`.
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
    (hΛ : HeldGenau Λ (offen z.spur)) (hnw : caller.wartend = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rueck M f caller rst hpop Γ Λ e hperm ρ hhead _ rfl
    (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩

theorem w_rueckCons {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Endblock D (vertragVon D z.kopf.f) false Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨false, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (hnw : caller.wartend = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rueckCons M f caller rst hpop Γ Λ e hperm rest ρ hhead _ rfl
    (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩

theorem w_dannRet {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (hnw : caller.wartend = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRet M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ
    _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩

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

variable (hnw : caller.wartend = false)
include hnw

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
      caller rst rfl e hperm rest ρ rfl hΛ hnw
    rw [hW] at hG
    exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onGrund => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

-- `hnw` is used at the returns; `blockRet` and the arm recursions reach it
-- only through `stmtRet`/`endRet`, which the linter does not count as a use.
set_option linter.unusedSectionVars false in
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
        caller rst rfl e hperm rest k ρ rfl hΛ hnw
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
        caller rst rfl e hperm ρ rfl hΛ hnw
      rw [hW] at hG
      exact ⟨M1, RufLaufG.einzeln hs1, hG⟩
  | _, _, _, .retGrund .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro σ σ' ρ v hex M hZ hΛ hA
      obtain ⟨hs, hr, hl⟩ := he.cons_inv
      rcases execEnd_cons_zurueck O passes keinRuf s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact endeConsRet P O passes f fn caller rst rho s0 log A hnw hs hl (stmtRet s hs)
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
    world `s0`) above a caller frame that does not wait for a bound value
    (`hnw`: the verbatim pop demands it since 2026-09-13), with residue
    `.ende b` for a covered (call-free, `EndG`) end block `b` at environment
    `ρ`; its static holdings `Λ` name exactly the locks its trace holds; no
    other thread holds a lock `b` may take (`A`). If the sequential semantics, started at
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
    (hnw : caller.wartend = false)
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
  obtain ⟨M', hl, hG⟩ := endRet P O passes f fn caller rst rho s0 log A hnw b hb
    (M.weltVon f) σ' ρ v hexec M hZ (by rw [hsp]; exact hΛ) hfrei
  exact ⟨M', hl, hG.1, hG.2, rufLaufG_fremd hl⟩

/-! ### The covered fragment is call-free in the sense of `HoareRegeln.lean`

    `EndG` refines `EndOhneRuf`: every covered body is a body the Hoare
    rules' call-freedom predicate accepts, so the sequential side of
    TARGET A is `R`-independent (`endOhneRuf_Runabhaengig`). -/

theorem blattG_ohneRuf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) : StmtOhneRuf s := by
  cases h <;> constructor

mutual

theorem stmtG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    StmtG A mr s → StmtOhneRuf s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ => blattG_ohneRuf (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      blattG_ohneRuf (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ => blattG_ohneRuf (.assignGlob g e hw hL)
  | _, _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattG_ohneRuf (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ => blattG_ohneRuf (.assignVar x e)
  | _, _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      blattG_ohneRuf (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regSchreib r hk e, _ => blattG_ohneRuf (.regSchreib r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattG_ohneRuf (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattG_ohneRuf (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ => blattG_ohneRuf (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ => blattG_ohneRuf (.retires m s h a)
  | _, _, _, _, _, .ite _ t e, hs =>
      .ite _ _ _ (blockG_ohneRuf t hs.ite_inv.1) (blockG_ohneRuf e hs.ite_inv.2)
  | _, _, _, _, _, .onOption _ p a, hs =>
      .onOption _ _ _ (blockG_ohneRuf p hs.onOption_inv.1) (blockG_ohneRuf a hs.onOption_inv.2)
  | _, _, _, _, _, .onTag _ arms, hs => .onTag _ _ (armsG_ohneRuf arms hs.onTag_inv)
  | _, _, _, _, _, .onGrund _ arms, hs => .onGrund _ _ (grundG_ohneRuf arms hs.onGrund_inv)
  | _, _, _, _, _, .call .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .locks _ _ body, hs => .locks _ _ _ (blockG_ohneRuf body hs.locks_inv.2)
  | _, _, _, _, _, .breaking _ body, hs => .breaking _ _ (blockG_ohneRuf body hs.breaking_inv)
  | _, _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .ret e hΛ, _ => .ret e hΛ
  | _, _, _, _, _, .retGrund .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    BlockG A mr b → BlockOhneRuf b
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons s rest, hb =>
      .cons _ _ (stmtG_ohneRuf s hb.cons_inv.1) (blockG_ohneRuf rest hb.cons_inv.2)
  | _, _, _, _, _, .bind _ rest, hb => .bind _ _ (blockG_ohneRuf rest hb.bind_inv)
  | _, _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .regLies _ _ rest, hb => .regLies _ _ _ (blockG_ohneRuf rest hb.regLies_inv)
  | _, _, _, _, _, .regLiesElse _ _ _ sonst rest, hb =>
      .regLiesElse _ _ _ _ _ (endG_ohneRuf sonst hb.regLiesElse_inv.2.2.1)
        (blockG_ohneRuf rest hb.regLiesElse_inv.2.1)
  | _, _, _, _, _, .awaits _ _ _ _ rest, hb =>
      .awaits _ _ _ _ _ (blockG_ohneRuf rest hb.awaits_inv)
  | _, _, _, _, _, .exchange _ _ _ _ rest, hb =>
      .exchange _ _ _ _ _ (blockG_ohneRuf rest hb.exchange_inv)
  | _, _, _, _, _, .narrow _ _ _ sonst rest, hb =>
      .narrow _ _ _ _ _ (endG_ohneRuf sonst hb.narrow_inv.2.2.1)
        (blockG_ohneRuf rest hb.narrow_inv.2.1)
  | _, _, _, _, _, .pruefung _ sonst rest, hb =>
      .pruefung _ _ _ (endG_ohneRuf sonst hb.pruefung_inv.2.2.1)
        (blockG_ohneRuf rest hb.pruefung_inv.2.1)
  | _, _, _, _, _, .gleit _ _ _ _ _ rest, hb =>
      .gleit _ _ _ _ _ _ (blockG_ohneRuf rest hb.gleit_inv)
  | _, _, _, _, _, .gleitLit _ _ _ rest, hb =>
      .gleitLit _ _ _ _ (blockG_ohneRuf rest hb.gleitLit_inv)
  | _, _, _, _, _, .gleitVon _ _ _ rest, hb =>
      .gleitVon _ _ _ _ (blockG_ohneRuf rest hb.gleitVon_inv)
  | _, _, _, _, _, .gleitNarrow _ _ _ sonst rest, hb =>
      .gleitNarrow _ _ _ _ _ (endG_ohneRuf sonst hb.gleitNarrow_inv.2.2.1)
        (blockG_ohneRuf rest hb.gleitNarrow_inv.2.1)

theorem endG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    EndG A e → EndOhneRuf e
  | _, _, _, .ret e hΛ, _ => .ret e hΛ
  | _, _, _, .retGrund .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he =>
      .cons _ _ (stmtG_ohneRuf s he.cons_inv.1) (endG_ohneRuf rest he.cons_inv.2.1)
  | _, _, _, .bind _ rest, he => .bind _ _ (endG_ohneRuf rest he.bind_inv)

theorem armsG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs), ArmsG A mr arms → ArmsOhneRuf arms
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .cons b rest, ha =>
      .cons _ _ (blockG_ohneRuf b ha.cons_inv.1) (armsG_ohneRuf rest ha.cons_inv.2)

theorem grundG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A mr arms → GrundArmsOhneRuf arms
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .cons b rest, ha =>
      .cons _ _ (blockG_ohneRuf b ha.cons_inv.1) (grundG_ohneRuf rest ha.cons_inv.2)

end

/-- **TARGET A for any call handler.** A covered body is call-free, so the
    sequential run under ANY handler `R` (e.g. `rufAt P O passes fuel`, the
    one the program semantics and the Hoare rules use) is the run under
    `keinRuf`; `rufG_adaequat` applies verbatim. -/
theorem rufG_adaequat_R (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndG A b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes R b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ M', RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  rw [endOhneRuf_Runabhaengig O passes R keinRuf b (endG_ohneRuf b hb)] at hexec
  exact rufG_adaequat P O passes M f fn rho s0 caller rst spur log ρ b A hb hM hnw hΛ hfrei σ' v hexec

/-! ## 12. Witness: a `locks` block around an `if` whose taken branch writes

    `adD` has one table `konto` (2 slots, one `.int 0 100` field) guarded by
    one lock (`braucht`), and two functions over `Bool`: `true` (no
    parameters, returns `.int 0 100`, holds NO lock at entry, may write the
    table) and `false` (the caller, returns nothing). The body of `true` is

        locks m { if true { konto[0] := 5 } else { } }; return 7

    The frame of `true` runs above a caller frame; every thread's trace is
    empty, so no other thread holds `m`. -/

def adSigA : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def adSigB : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def adD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => adSigA | _ => adSigB
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
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The witness function (`true`) and the caller (`false`). -/
def adFn : adD.Fn := show adD.Fn from true

def adCallerFn : adD.Fn := show adD.Fn from false

/-- The holdings inside the `locks` body. -/
def adΛL : List (Res adD) := [Res.held (D := adD) ()]

theorem adDarf : darf adD () adΛL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

def adIdx : Expr adD [] adΛL (.index (adD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

def adFuenf : Expr adD [] adΛL (adD.typ () ()) :=
  .weiter (by decide) (by decide) (.lit 5)

/-- `konto[0] := 5`. -/
def adWrite : Stmt adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .assignSlot () () adIdx adFuenf rfl adDarf

/-- The taken branch: the write. -/
def adThen : Block adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .cons adWrite .nil

/-- `if true { konto[0] := 5 } else { }`. -/
def adIte : Stmt adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .ite .wahr adThen .nil

def adBody : Block adD (vertragVon adD adFn) false [] adΛL adΛL :=
  .cons adIte .nil

/-- `locks m { … }`: nothing is held before, so the rank side is empty. -/
def adLocks : Stmt adD (vertragVon adD adFn) false [] [] [] :=
  .locks () (fun _ h => absurd h List.not_mem_nil) adBody

def adSieben : Expr adD [] [] (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 7)

/-- The body: `locks m { if true { konto[0] := 5 } else { } }; return 7`. -/
def adRumpf : Endblock adD (vertragVon adD adFn) false [] [] :=
  .cons adLocks (.ret (.wert adSieben) List.Perm.nil)

def adCallerRumpf : Endblock adD (vertragVon adD adCallerFn) false [] [] :=
  .ret .keine List.Perm.nil

def adP : Programm adD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | true => adRumpf
    | false => adCallerRumpf

def adO : Orakel adD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- Start memory: every slot reads `0`. -/
def adSp0 : Speicher adD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- The suspended caller frame. -/
def adCaller : RufRahmenG adD :=
  ⟨adCallerFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adCallerRumpf⟩⟩

/-- Every thread: the witness frame above the caller, empty trace, empty log. -/
def adFaden : RufFadenG adD :=
  ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adRumpf⟩⟩,
    [], []⟩

def adM : RufMaschineG adD := ⟨adSp0, fun _ => adFaden, [], adSp0.welt []⟩

/-- The body is in the covered fragment, with the one lock admitted. -/
theorem adRumpf_G : EndG (fun L : adD.Lock => L = ()) adRumpf :=
  EndG.cons _ _
    (StmtG.locks (A := fun L : adD.Lock => L = ()) () _ adBody rfl
      (BlockG.cons _ _
        (StmtG.ite _ _ _
          (BlockG.cons _ _ (StmtG.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockG.nil)
          BlockG.nil)
        BlockG.nil))
    (EndG.ret _ _)

/-- No thread of `adM` holds any lock. -/
theorem adM_frei : ∀ L : adD.Lock, L = () → RufFreiG adM 0 L := by
  intro L _ g _ hm
  simp [adM, adFaden, offen] at hm

/-- The frame's holdings are exactly the (empty) held locks. -/
theorem adM_held : HeldGenau ([] : List (Res adD)) (offen ([] : List (Ereignis adD))) := by
  intro L
  simp [offen]

/-- The sequential run of the body: a normal return with the written slot. -/
theorem adRumpf_exec : ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
    execEnd adO 0 keinRuf adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (show Zahl 0 100 from v).n = 7 :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat`.** Every premise is instantiated jointly
    on the non-degenerate program above: the body takes a lock (`locks`)
    and, inside, runs an `if` whose taken branch WRITES the table. The
    sequential semantics returns `7` in a world where slot 0 moved `0 -> 5`;
    the machine, by steps of thread 0 alone, pops the frame logging that
    same `7` and that same world, and its memory holds the moved slot. -/
theorem rufG_adaequat_zeuge :
    ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
      execEnd adO 0 keinRuf adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ ((adM.weltVon 0).slots () 0 ()).n = 0 ∧
      (show Zahl 0 100 from v).n = 7 ∧
      ∃ M', RufLaufG adP adO 0 0 adM M' ∧
        M'.faeden 0 = ⟨[], adCaller, σ'.spur,
          [RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) σ']⟩ ∧
        M'.speicher = σ'.speicher ∧ (M'.speicher.slots () 0 ()).n = 5 ∧
        (∀ g, g ≠ 0 → M'.faeden g = adM.faeden g) := by
  obtain ⟨σ', v, hex, h5, h7⟩ := adRumpf_exec
  obtain ⟨M', hl, hf, hsp, hfr⟩ := rufG_adaequat adP adO 0 adM 0 adFn Env.nil
    (adSp0.welt []) adCaller [] [] [] Env.nil adRumpf (fun L : adD.Lock => L = ())
    adRumpf_G rfl rfl adM_held adM_frei σ' v hex
  refine ⟨σ', v, hex, h5, rfl, h7, M', hl, hf, hsp, ?_, hfr⟩
  rw [hsp]
  exact h5

/-! ## 13. Toward TARGET B: forms that never consult the oracle

    The converse must survive the machine's bare `nimmt`/`gibt` steps (a
    thread may take and release a free lock at any time, outside any
    `locks` statement). They change only the thread's trace. The sequential
    semantics depends on the trace only through the oracle (`regLies`,
    `regLiesElse`, `awaits` hand the whole world to `O`), so the converse
    is stated for bodies without those forms. -/

mutual

/-- The statement never hands the world to the oracle. -/
def Stmt.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ohneOrakel && e.ohneOrakel
  | .onOption _ p a => p.ohneOrakel && a.ohneOrakel
  | .onTag _ arms => arms.ohneOrakel
  | .onGrund _ arms => arms.ohneOrakel
  | .locks _ _ body => body.ohneOrakel
  | .breaking _ body => body.ohneOrakel
  | .traverse _ _ body => body.ohneOrakel
  | .retry _ _ body u => body.ohneOrakel && u.ohneOrakel
  | .forever _ _ body => body.ohneOrakel
  | .axiomCall .. => false
  | _ => true

def Block.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ohneOrakel && rest.ohneOrakel
  | .bind _ rest => rest.ohneOrakel
  | .bindCall _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallInd _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallElse _ _ _ _ _ err rest => err.ohneOrakel && rest.ohneOrakel
  | .bindAxiom .. => false
  | .regLies .. => false
  | .regLiesElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.ohneOrakel
  | .narrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .pruefung _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .gleit _ _ _ _ _ rest => rest.ohneOrakel
  | .gleitLit _ _ _ rest => rest.ohneOrakel
  | .gleitVon _ _ _ rest => rest.ohneOrakel
  | .gleitNarrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel

def Endblock.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .cons s rest => s.ohneOrakel && rest.ohneOrakel
  | .bind _ rest => rest.ohneOrakel
  | _ => true

def Arms.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ohneOrakel && rest.ohneOrakel

def GrundArms.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ohneOrakel && rest.ohneOrakel

end

/-- `armWahlG` selects an oracle-free arm of oracle-free arms. -/
theorem armWahlG_ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.ohneOrakel = true → (armWahlG arms v).2.1.ohneOrakel = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at h
      exact armWahlG_ohneOrakel rest _ h.2

theorem grundWahlG_ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.ohneOrakel = true → (grundWahlG arms r).ohneOrakel = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at h
      exact grundWahlG_ohneOrakel rest _ h.2

/-! ## 14. The sequential semantics does not see the trace (oracle-free) -/

/-- Two worlds with the same shared memory (traces may differ). -/
def SG (σ σ' : World D) : Prop := σ.slots = σ'.slots ∧ σ.globs = σ'.globs

theorem SG.speicher {σ σ' : World D} (h : SG σ σ') : σ.speicher = σ'.speicher := by
  unfold World.speicher
  rw [h.1, h.2]

theorem SG.lese {σ σ' : World D} (h : SG σ σ') (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) : SG (σ.lese Λ os) (σ'.lese Λ os) := h

theorem SG.nimmt {σ σ' : World D} (h : SG σ σ') (L : D.Lock) : SG (σ.nimmt L) (σ'.nimmt L) := h

theorem SG.gibt {σ σ' : World D} (h : SG σ σ') (L : D.Lock) : SG (σ.gibt L) (σ'.gibt L) := h

theorem SG.schreibSlot {σ σ' : World D} (h : SG σ σ') (t : D.Tab) (Λ : List (Res D))
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    SG (σ.schreibSlot t Λ k f v) (σ'.schreibSlot t Λ k f v) := by
  refine ⟨?_, h.2⟩
  show (σ.storeSlot t k f v).slots = (σ'.storeSlot t k f v).slots
  simp only [World.storeSlot]
  rw [h.1]

theorem SG.schreibGlob {σ σ' : World D} (h : SG σ σ') (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : SG (σ.schreibGlob g Λ v) (σ'.schreibGlob g Λ v) := by
  refine ⟨h.1, ?_⟩
  show (σ.storeGlob g v).globs = (σ'.storeGlob g v).globs
  simp only [World.storeGlob]
  rw [h.2]

theorem SG.schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : ∀ (bs : List Byte) (σ σ' : World D) (k : Int), SG σ σ' →
    SG (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | _ :: bs, _, _, k, h =>
      SG.schreibBytes t f hf Λ bs _ _ (k + 1) (h.schreibSlot t Λ k f _)

theorem SG.eval {σ σ' : World D} (h : SG σ σ') {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (ρ : Env D Γ) : eval σ e σ ρ = eval σ' e σ' ρ :=
  eval_liest_nur_speicher_diag e σ σ' ρ (fun t k f => by rw [h.1]) (fun g => by rw [h.2])

theorem SG.evalErg {σ σ' : World D} (h : SG σ σ') {Γ : Ctx} {Λ : List (Res D)}
    {e : Option Ty} (x : ErgExpr D Γ Λ e) (ρ : Env D Γ) :
    evalErg σ x σ ρ = evalErg σ' x σ' ρ := by
  cases x with
  | keine => rfl
  | wert e => exact h.eval e ρ

/-- Outcomes that agree up to the trace: same kind, same memory, same
    environment or value; every other kind agrees on the kind only. -/
def AusSG {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Ausgang V l Γ → Prop
  | .ok σ ρ, .ok σ' ρ' => SG σ σ' ∧ ρ = ρ'
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .ok .., _ => False
  | _, .ok .. => False
  | .zurueck .., _ => False
  | _, .zurueck .. => False
  | _, _ => True

def EndSG {V : Vertrag D} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → EndAusgang V l Γ → Prop
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .zurueck .., _ => False
  | _, .zurueck .. => False
  | _, _ => True

section AusSGLemmas

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- Continuing after a statement preserves agreement. -/
theorem AusSG.weiter {o o' : Ausgang V l Γ} (h : AusSG o o')
    (g g' : World D → Env D Γ → Ausgang V l Γ)
    (hg : ∀ σ σ' ρ, SG σ σ' → AusSG (g σ ρ) (g' σ' ρ)) :
    AusSG (match o with | .ok σ ρ => g σ ρ | o => o)
      (match o' with | .ok σ ρ => g' σ ρ | o => o) := by
  cases o with
  | ok σ ρ =>
    cases o' with
    | ok σ' ρ' =>
      obtain ⟨hs, rfl⟩ := h
      exact hg σ σ' ρ hs
    | _ => exact False.elim h
  | _ =>
    cases o' with
    | ok => exact False.elim h
    | _ => exact h

theorem AusSG.schrumpf {τ : Ty} {o o' : Ausgang V l (τ :: Γ)} (h : AusSG o o') :
    AusSG o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp_all [AusSG, Ausgang.schrumpf]

theorem AusSG.schrumpfArm (c : Option (Int × Int)) {o o' : Ausgang V l (ArmCtx Γ c)}
    (h : AusSG o o') : AusSG (o.schrumpfArm c) (o'.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => exact AusSG.schrumpf h

theorem AusSG.gibt {o o' : Ausgang V l Γ} (h : AusSG o o') (L : D.Lock) :
    AusSG (o.mapWelt (·.gibt L)) (o'.mapWelt (·.gibt L)) := by
  cases o <;> cases o' <;> simp_all [AusSG, Ausgang.mapWelt, SG, World.gibt]

theorem EndSG.zuAusgang {o o' : EndAusgang V l Γ} (h : EndSG o o') :
    AusSG o.zuAusgang o'.zuAusgang := by
  cases o <;> cases o' <;> simp_all [AusSG, EndSG, EndAusgang.zuAusgang]

theorem EndSG.schrumpf {τ : Ty} {o o' : EndAusgang V l (τ :: Γ)} (h : EndSG o o') :
    EndSG o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp_all [EndSG, EndAusgang.schrumpf]

/-- `execEnd` of `s; rest` from agreeing statement outcomes. -/
theorem EndSG.weiter {o o' : Ausgang V l Γ} (h : AusSG o o')
    (g g' : World D → Env D Γ → EndAusgang V l Γ)
    (hg : ∀ σ σ' ρ, SG σ σ' → EndSG (g σ ρ) (g' σ' ρ)) :
    EndSG (match o with
        | .ok σ' ρ' => g σ' ρ'
        | .zurueck σ' v => .zurueck σ' v
        | .grund σ' r => .grund σ' r
        | .leave h σ' ρ' => .leave h σ' ρ'
        | .next h σ' ρ' => .next h σ' ρ'
        | .logik e => .logik e
        | .hardware e => .hardware e)
      (match o' with
        | .ok σ' ρ' => g' σ' ρ'
        | .zurueck σ' v => .zurueck σ' v
        | .grund σ' r => .grund σ' r
        | .leave h σ' ρ' => .leave h σ' ρ'
        | .next h σ' ρ' => .next h σ' ρ'
        | .logik e => .logik e
        | .hardware e => .hardware e) := by
  cases o with
  | ok σ ρ =>
    cases o' with
    | ok σ' ρ' =>
      obtain ⟨hs, rfl⟩ := h
      exact hg σ σ' ρ hs
    | _ => exact False.elim h
  | zurueck σ v =>
    cases o' with
    | zurueck σ' v' => exact h
    | _ => exact False.elim h
  | _ =>
    cases o' with
    | ok => exact False.elim h
    | zurueck => exact False.elim h
    | _ => trivial

end AusSGLemmas

/-- The `narrow` step of `execBlock` with the narrowed value abstracted
    (the `dite` carries proofs about it, so it cannot be rewritten in place). -/
def narrowWeiter (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int}
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (sonst : Endblock D V l Γ Λ)
    (ρ : Env D Γ) (v : Zahl lo hi) (σ₁ : World D) : Ausgang V l Γ :=
  if h : lo' ≤ v.n ∧ v.n ≤ hi' then
    (execBlock O passes keinRuf rest σ₁ (.cons (τ := .int lo' hi') ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
  else (execEnd O passes keinRuf sonst σ₁ ρ).zuAusgang

theorem execBlock_narrow (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes keinRuf (.narrow e lo' hi' sonst rest) σ ρ =
      narrowWeiter O passes rest sonst ρ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)
        (σ.lese Λ e.orte) := rfl

section Spur

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop)

/-- A block's outcome agrees, up to the trace, from worlds with one memory. -/
def SGB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
    AusSG (execBlock O passes keinRuf b σ ρ) (execBlock O passes keinRuf b σ' ρ)

mutual

theorem stmtSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtG A mr s → s.ohneOrakel = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      AusSG (execStmt O passes keinRuf s σ ρ) (execStmt O passes keinRuf s σ' ρ)
  | _, _, _, Λ₀, _, .assignSlot t f' i e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignDurch p t ht f' i e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignGlob g e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1.schreibGlob _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨SG.schreibBytes _ _ _ _ _ _ _ _ h1, rfl⟩
  | _, _, _, Λ₀, _, .assignVar x e, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1, rfl⟩
  | _, _, _, Λ₀, _, .uebergang t f' hτ i von nach hn he hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (.inl t :: i.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.1]
      split
      · exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
      · trivial
  | _, _, _, _, _, .regSchreib r hk e, _, _ => by
      intro σ σ' ρ h
      simp only [execStmt]
      exact ⟨h.lese _ _, rfl⟩
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _, _ => by
      intro σ σ' ρ h
      simp only [execStmt]
      exact ⟨h, rfl⟩
  | _, _, _, Λ₀, _, .publish g e payload hp hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1.schreibGlob _ _ _, rfl⟩
  | _, _, _, _, _, .advances m a h hs, _, _ => by
      intro σ σ' ρ h'
      simp only [execStmt]
      exact ⟨h', rfl⟩
  | _, _, _, _, _, .retires m s h a, _, _ => by
      intro σ σ' ρ h'
      simp only [execStmt]
      exact ⟨h', rfl⟩
  | _, _, _, Λ₀, _, .ite c t e, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [Stmt.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execStmt]
      rw [h1.eval c]
      split
      · exact blockSG t ht ho.1 _ _ _ h1
      · exact blockSG e he ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onOption o p a, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [Stmt.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ o.orte
      simp only [execStmt]
      rw [h1.eval o]
      split
      · exact AusSG.schrumpf (blockSG p hp ho.1 _ _ _ h1)
      · exact blockSG a ha ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onTag w arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onTag_inv
      simp only [Stmt.ohneOrakel] at ho
      have h1 := h.lese Λ₀ w.orte
      simp only [execStmt]
      rw [execArms_wahl, execArms_wahl, h1.eval w]
      exact AusSG.schrumpfArm _ (armsSG arms ha ho _ _ _ _ h1)
  | _, _, _, Λ₀, _, .onGrund r arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onGrund_inv
      simp only [Stmt.ohneOrakel] at ho
      have h1 := h.lese Λ₀ r.orte
      simp only [execStmt]
      rw [execGrund_wahlW O passes keinRuf arms, execGrund_wahlW O passes keinRuf arms,
        h1.eval r]
      exact grundSG arms ha ho _ _ _ _ h1
  | _, _, _, _, _, .call .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .callInd .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .locks L hr body, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [Stmt.ohneOrakel] at ho
      simp only [execStmt]
      exact AusSG.gibt (blockSG body hb ho _ _ _ (h.nimmt L)) L
  | _, _, _, _, _, .breaking i body, hs, ho => by
      intro σ σ' ρ h
      have hb := hs.breaking_inv
      simp only [Stmt.ohneOrakel] at ho
      simp only [execStmt]
      exact blockSG body hb ho _ _ _ h
  | _, _, _, _, _, .traverse .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .retry .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .forever .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .axiomCall .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, Λ₀, _, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, _, _, .retGrund .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .leave .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .next .., hs, _ => absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockG A mr b → b.ohneOrakel = true → SGB O passes b
  | _, _, _, _, _, .nil, _, _ => by
      intro σ σ' ρ h
      exact ⟨h, rfl⟩
  | _, _, _, _, _, .cons s rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr⟩ := hb.cons_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := stmtSG s hs ho.1 _ _ ρ h
      simp only [execBlock]
      generalize execStmt O passes keinRuf s σ ρ = o at h1 ⊢
      generalize execStmt O passes keinRuf s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | (obtain ⟨hs1, rfl⟩ := h1; exact blockSG rest hr ho.2 _ _ _ hs1)
  | _, _, _, Λ₀, _, .bind e rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.bind_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h1)
  | _, _, _, _, _, .bindCall .., hb, _ => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb, _ => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb, _ => by cases hb
  | _, _, _, _, _, .regLies .., _, ho => by simp [Block.ohneOrakel] at ho
  | _, _, _, _, _, .regLiesElse .., _, ho => by simp [Block.ohneOrakel] at ho
  | _, _, _, _, _, .awaits .., _, ho => by simp [Block.ohneOrakel] at ho
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.exchange_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ (.inr g :: neuE.orte)
      simp only [execBlock]
      have hg : (σ.lese Λ₀ (.inr g :: neuE.orte)).globs g =
          (σ'.lese Λ₀ (.inr g :: neuE.orte)).globs g := by rw [h1.2]
      rw [hg, h1.eval neuE]
      exact AusSG.schrumpf (blockSG rest hr ho _ _ _ (h1.schreibGlob _ _ _))
  | _, _, _, Λ₀, _, .narrow e lo' hi' sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      rw [execBlock_narrow, execBlock_narrow, h1.eval e]
      unfold narrowWeiter
      split
      · exact AusSG.schrumpf (blockSG rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSG sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .pruefung c sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execBlock]
      rw [h1.eval c]
      split
      · exact blockSG rest hr ho.2 _ _ _ h1
      · exact EndSG.zuAusgang (endSG sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .gleit op a b lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleit_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ (a.orte ++ b.orte)
      simp only [execBlock]
      rw [h1.eval a, h1.eval b]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, _, _, .gleitLit q lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitLit_inv
      simp only [Block.ohneOrakel] at ho
      simp only [execBlock]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h)
      · trivial
  | _, _, _, Λ₀, _, .gleitVon e lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitVon_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, Λ₀, _, .gleitNarrow e lo hi sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSG sonst hs ho.1 _ _ _ h1)

theorem endSG : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), EndG A e → e.ohneOrakel = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      EndSG (execEnd O passes keinRuf e σ ρ) (execEnd O passes keinRuf e σ' ρ)
  | _, _, Λ₀, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, .retGrund .., he, _ => by cases he
  | _, _, _, .leave .., he, _ => by cases he
  | _, _, _, .next .., he, _ => by cases he
  | _, _, _, .cons s rest, he, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      simp only [Endblock.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := stmtSG s hs ho.1 _ _ ρ h
      simp only [execEnd]
      generalize execStmt O passes keinRuf s σ ρ = o at h1 ⊢
      generalize execStmt O passes keinRuf s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact endSG rest hr ho.2 _ _ _ hs1)
  | _, _, Λ₀, .bind e rest, he, ho => by
      intro σ σ' ρ h
      have hr := he.bind_inv
      simp only [Endblock.ohneOrakel] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      rw [h1.eval e]
      exact EndSG.schrumpf (endSG rest hr ho _ _ _ h1)

theorem armsSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsG A mr arms → arms.ohneOrakel = true → ∀ (v : Wert D (.sum cs)),
    SGB O passes (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨⟨0, _⟩, _⟩ => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at ho
      exact blockSG b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨⟨_ + 1, _⟩, _⟩ => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at ho
      exact armsSG rest ha.cons_inv.2 ho.2 _

theorem grundSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A mr arms → arms.ohneOrakel = true →
    ∀ (r : Fin n), SGB O passes (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨0, _⟩ => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at ho
      exact blockSG b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨_ + 1, _⟩ => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at ho
      exact grundSG rest ha.cons_inv.2 ho.2 _

end

end Spur

/-! ## 15. What a residue still returns: the frame semantics `semR`

    `semR k σ ρ` runs the residue `k` sequentially: an end block by
    `execEnd`, a `dann b k` by `execBlock b` and then `k`, a `schrumpf` by
    dropping the innermost binding, a `frei L` by the `gibt L` of its
    `locks`. Only a return counts (`REnde.zurueck`); every other outcome is
    `sonst`. Loop shims and `wartet` are outside the fragment (`sonst`). -/

inductive REnde (V : Vertrag D) where
  | zurueck (σ : World D) (v : ErgVal D V.erg)
  | sonst

/-- Agreement of frame results up to the trace. -/
def REnde.gleich {V : Vertrag D} : REnde V → REnde V → Prop
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .sonst, .sonst => True
  | _, _ => False

theorem REnde.gleich_refl {V : Vertrag D} (r : REnde V) : r.gleich r := by
  cases r with
  | zurueck σ v => exact ⟨⟨rfl, rfl⟩, rfl⟩
  | sonst => trivial

theorem REnde.gleich_symm {V : Vertrag D} {r r' : REnde V} (h : r.gleich r') : r'.gleich r := by
  cases r <;> cases r' <;> simp_all [REnde.gleich, SG]

theorem REnde.gleich_trans {V : Vertrag D} {r r' r'' : REnde V} (h1 : r.gleich r')
    (h2 : r'.gleich r'') : r.gleich r'' := by
  cases r <;> cases r' <;> cases r'' <;> simp_all [REnde.gleich, SG]

section Sem

variable (O : Orakel D) (passes : Nat) {V : Vertrag D}

def endErg {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → REnde V
  | .zurueck σ v => .zurueck σ v
  | _ => .sonst

def semR : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → World D →
    Env D Γ → REnde V
  | _, _, _, .ende e, σ, ρ => endErg (execEnd O passes keinRuf e σ ρ)
  | _, _, _, .dann b k, σ, ρ =>
      match execBlock O passes keinRuf b σ ρ with
      | .ok σ' ρ' => semR k σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | _ => .sonst
  | _, _, _, .schrumpf k, σ, ρ => semR k σ ρ.tail
  | _, _, _, .frei L k, σ, ρ => semR k (σ.gibt L) ρ
  | _, _, _, .trav .., _, _ => .sonst
  | _, _, _, .travRest .., _, _ => .sonst
  | _, _, _, .wieder .., _, _ => .sonst
  | _, _, _, .wiederRest .., _, _ => .sonst
  | _, _, _, .ewig .., _, _ => .sonst
  | _, _, _, .ewigRest .., _, _ => .sonst
  | _, _, _, .wartet .., _, _ => .sonst
  | _, _, _, .wartetSonst .., _, _ => .sonst

/-- Continue with `k` after an outcome. -/
def nachA {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (o : Ausgang V l Γ)
    (k : GRest D V l Γ Λ) : REnde V :=
  match o with
  | .ok σ ρ => semR O passes k σ ρ
  | .zurueck σ v => .zurueck σ v
  | _ => .sonst

variable {l : Bool} {Γ : Ctx}

theorem semR_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann b k) σ ρ = nachA O passes (execBlock O passes keinRuf b σ ρ) k := by
  simp only [semR, nachA]

theorem nachA_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    nachA O passes (execBlock O passes keinRuf (.cons s rest) σ ρ) k =
      nachA O passes (execStmt O passes keinRuf s σ ρ) (.dann rest k) := by
  simp only [execBlock]
  generalize execStmt O passes keinRuf s σ ρ = o
  cases o <;> simp only [nachA, semR_dann]

theorem nachA_schrumpf {τ : Ty} {Λ : List (Res D)} (o : Ausgang V l (τ :: Γ))
    (k : GRest D V l Γ Λ) :
    nachA O passes o.schrumpf k = nachA O passes o (.schrumpf k) := by
  cases o <;> simp only [Ausgang.schrumpf, nachA, semR]

theorem nachA_schrumpfArm (c : Option (Int × Int)) {Λ : List (Res D)}
    (o : Ausgang V l (ArmCtx Γ c)) (k : GRest D V l Γ Λ) :
    nachA O passes (o.schrumpfArm c) k =
      (match c, o with
       | none, o => nachA O passes o k
       | some (_, _), o => nachA O passes o (.schrumpf k)) := by
  cases c with
  | none => rfl
  | some p => exact nachA_schrumpf O passes o k

theorem nachA_zuAusgang {Λ : List (Res D)} (o : EndAusgang V l Γ) (k : GRest D V l Γ Λ) :
    nachA O passes o.zuAusgang k = endErg o := by
  cases o <;> rfl

theorem endErg_schrumpf {τ : Ty} (o : EndAusgang V l (τ :: Γ)) : endErg o.schrumpf = endErg o := by
  cases o <;> rfl

theorem endErg_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    endErg (execEnd O passes keinRuf (.cons s rest) σ ρ) =
      nachA O passes (execStmt O passes keinRuf s σ ρ) (.dann .nil (.ende rest)) := by
  simp only [execEnd]
  generalize execStmt O passes keinRuf s σ ρ = o
  cases o <;> simp only [endErg, nachA, semR, execBlock]

/-- The `locks` release: a return inside the body loses the final `gibt`
    (the machine pops without it), which only the trace sees. -/
theorem nachA_frei {Λ : List (Res D)} (o : Ausgang V l Γ) (L : D.Lock)
    (k : GRest D V l Γ Λ) :
    (nachA O passes o (.frei L k)).gleich (nachA O passes (o.mapWelt (·.gibt L)) k) := by
  cases o with
  | ok σ ρ => exact REnde.gleich_refl _
  | zurueck σ v => exact ⟨⟨rfl, rfl⟩, rfl⟩
  | _ => trivial

theorem endErg_SG {o o' : EndAusgang V l Γ} (h : EndSG o o') :
    (endErg o).gleich (endErg o') := by
  cases o <;> cases o' <;> simp_all [EndSG, endErg, REnde.gleich]

end Sem

/-- The residues the converse follows: covered, oracle-free blocks in
    `dann` position, covered end blocks, `schrumpf` and `frei` layers. -/
inductive RestG {V : Vertrag D} (A : D.Lock → Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop where
  | ende {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ)
      (he : EndG A e) (ho : e.ohneOrakel = true) : RestG A (.ende e)
  | dann {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
      (k : GRest D V l Γ Λ') (hb : BlockG A mr b) (ho : b.ohneOrakel = true)
      (hk : RestG A k) : RestG A (.dann b k)
  | schrumpf {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ)
      (hk : RestG A k) : RestG A (.schrumpf (τ := τ) k)
  | frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ)
      (hk : RestG A k) : RestG A (.frei L k)

section RestInv

variable {V : Vertrag D} {A : D.Lock → Prop} {l : Bool} {Γ : Ctx}

theorem RestG.ende_inv {Λ : List (Res D)} {e : Endblock D V l Γ Λ}
    (h : RestG A (.ende e)) : EndG A e ∧ e.ohneOrakel = true := by
  cases h with
  | ende _ he ho => exact ⟨he, ho⟩

theorem RestG.dann_inv {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'}
    {k : GRest D V l Γ Λ'} (h : RestG A (.dann b k)) :
    (∃ mr, BlockG A mr b) ∧ b.ohneOrakel = true ∧ RestG A k := by
  cases h with
  | dann _ _ hb ho hk => exact ⟨⟨_, hb⟩, ho, hk⟩

theorem RestG.schrumpf_inv {Λ : List (Res D)} {τ : Ty} {k : GRest D V l Γ Λ}
    (h : RestG A (.schrumpf (τ := τ) k)) : RestG A k := by
  cases h with
  | schrumpf _ hk => exact hk

theorem RestG.frei_inv {Λ : List (Res D)} {L : D.Lock} {k : GRest D V l Γ Λ}
    (h : RestG A (.frei L k)) : RestG A k := by
  cases h with
  | frei _ _ hk => exact hk

/-- The head statement of a covered `dann` block is a covered form. -/
theorem RestG.dann_cons_art {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : RestG A (.dann (.cons s rest) k)) : s.gArt = true := by
  obtain ⟨⟨_, hb⟩, _, _⟩ := h.dann_inv
  exact hb.cons_inv.1.art

theorem RestG.ende_cons_art {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : RestG A (.ende (.cons s rest))) : s.gArt = true := by
  obtain ⟨he, _⟩ := h.ende_inv
  exact he.cons_inv.1.art

end RestInv

/-- Frame results do not see the trace (covered, oracle-free residues). -/
theorem semR_SG (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ), RestG A r →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      (semR O passes r σ ρ).gleich (semR O passes r σ' ρ)
  | _, _, _, .ende e, hr => by
      intro σ σ' ρ h
      obtain ⟨he, ho⟩ := hr.ende_inv
      exact endErg_SG (endSG O passes A e he ho σ σ' ρ h)
  | _, _, _, .dann b k, hr => by
      intro σ σ' ρ h
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hr.dann_inv
      have h1 := blockSG O passes A b hb ho σ σ' ρ h
      rw [semR_dann, semR_dann]
      generalize execBlock O passes keinRuf b σ ρ = o at h1 ⊢
      generalize execBlock O passes keinRuf b σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact semR_SG O passes A k hk _ _ _ hs1)
  | _, _, _, .schrumpf k, hr => by
      intro σ σ' ρ h
      exact semR_SG O passes A k hr.schrumpf_inv σ σ' ρ.tail h
  | _, _, _, .frei L k, hr => by
      intro σ σ' ρ h
      exact semR_SG O passes A k hr.frei_inv (σ.gibt L) (σ'.gibt L) ρ (h.gibt L)
  | _, _, _, .trav .., hr => by cases hr
  | _, _, _, .travRest .., hr => by cases hr
  | _, _, _, .wieder .., hr => by cases hr
  | _, _, _, .wiederRest .., hr => by cases hr
  | _, _, _, .ewig .., hr => by cases hr
  | _, _, _, .ewigRest .., hr => by cases hr
  | _, _, _, .wartet .., hr => by cases hr
  | _, _, _, .wartetSonst .., hr => by cases hr

theorem REnde.gleich_of_eq {V : Vertrag D} {r r' : REnde V} (h : r = r') : r.gleich r' := by
  rw [h]
  exact REnde.gleich_refl r'

/-! ## 16. Each machine step keeps the frame semantics -/

section SemSchritt

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem sem_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') :
    semR O passes (.ende rest) σ' ρ' = semR O passes (.ende (.cons s rest)) σ ρ := by
  simp only [semR, execEnd, h]

theorem sem_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') :
    semR O passes (.dann rest k) σ' ρ' = semR O passes (.dann (.cons s rest) k) σ ρ := by
  rw [semR_dann O passes (.cons s rest), nachA_cons, h]
  rfl

theorem sem_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (.cons s .nil) (.ende rest)) σ ρ =
      semR O passes (.ende (.cons s rest)) σ ρ := by
  rw [semR_dann, nachA_cons]
  exact (endErg_cons O passes s rest σ ρ).symm

theorem sem_iteWahr {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semR O passes (.dann t (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hw, if_true]

theorem sem_iteFalsch {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semR O passes (.dann e (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hw, Bool.false_eq_true, if_false]

theorem sem_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semR O passes (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) =
      semR O passes (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hv]
  rw [nachA_schrumpf]

theorem sem_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semR O passes (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ =
      semR O passes (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hv]

theorem sem_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semR O passes (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semR O passes (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semR_dann O passes b _ _ _).trans (nachA_schrumpf O passes _ _).symm

theorem sem_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semR O passes (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semR O passes (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact semR_dann O passes b _ _ _

theorem sem_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ =
      semR O passes (.dann (.cons (.onGrund r arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt]
  rw [execGrund_wahlW O passes keinRuf arms]

theorem sem_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann body (.dann rest k)) σ ρ =
      semR O passes (.dann (.cons (.breaking i body) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt]

theorem sem_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    (semR O passes (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ).gleich
      (semR O passes (.dann (.cons (.locks L hr body) rest) k) σ ρ) := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt]
  exact nachA_frei O passes _ L _

theorem sem_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semR O passes (.ende (.bind e rest)) σ ρ := by
  simp only [semR, execEnd]
  rw [endErg_schrumpf]

theorem sem_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semR O passes (.dann (.bind e rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock]
  rw [nachA_schrumpf]

theorem sem_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) =
      semR O passes (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semR_dann O passes (.narrow e lo' hi' sonst rest), execBlock_narrow]
  unfold narrowWeiter
  rw [dif_pos h, nachA_schrumpf, semR_dann]

theorem sem_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semR O passes (.ende sonst) (σ.lese Λ e.orte) ρ =
      semR O passes (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semR_dann O passes (.narrow e lo' hi' sonst rest), execBlock_narrow]
  unfold narrowWeiter
  rw [dif_neg h, nachA_zuAusgang]
  rfl

theorem sem_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semR O passes (.dann rest k) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.pruefung c sonst rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hw, if_true]

theorem sem_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semR O passes (.ende sonst) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.pruefung c sonst rest) k) σ ρ := by
  rw [semR_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachA_zuAusgang]
  rfl

theorem sem_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semR O passes (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock]
  rw [nachA_schrumpf]

theorem sem_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semR O passes (.dann (.gleit op a b lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semR O passes (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semR O passes (.dann (.gleitLit q lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (Float.ofInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.dann (.gleitVon e lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semR O passes (.ende sonst) (σ.lese Λ e.orte) ρ =
      semR O passes (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semR_dann]
  simp only [execBlock, hn]
  rw [nachA_zuAusgang]
  rfl

theorem sem_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := rfl

theorem sem_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semR, execEnd, execStmt, endErg]

theorem sem_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semR_dann, nachA_cons]
  rfl

end SemSchritt

theorem faeden_upd (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    (⟨sp, rufUpdateG m f z, la, st⟩ : RufMaschineG D).faeden f = z :=
  rufUpdateG_self m f z

theorem weltVon_upd (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    (⟨sp, rufUpdateG m f z, la, st⟩ : RufMaschineG D).weltVon f = sp.welt z.spur := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]

/-- What one step of thread `f` does to a covered frame: either the frame
    stays on top with a covered residue and the same frame result (up to
    the trace), or it pops, logging a `rueck` whose world and value ARE the
    frame result (up to the trace). -/
def ErhaltG (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (M M' : RufMaschineG D)
    (f : Faden) (z : RufFadenG D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ) : Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (sp : List (Ereignis D)),
      M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, sp, z.log⟩ ∧
      RestG A r' ∧ (semR O passes r' (M'.weltVon f) ρ').gleich (semR O passes r (M.weltVon f) ρ)) ∨
  (∃ (v : ErgVal D (D.erg z.kopf.f)) (s1 : World D),
      (M'.faeden f).log = RufEreignisF.rueck z.kopf.f z.kopf.rho v z.kopf.s0 s1 :: z.log ∧
      (semR O passes r (M.weltVon f) ρ).gleich (.zurueck s1 v))

set_option hygiene false in
/-- Refute a step whose head shape the covered residue cannot have. -/
macro "widerlege" h:ident : tactic => `(tactic| (
  rw [hR] at $h:ident
  cases $h:ident
  first
  | exact absurd hcov.dann_cons_art (by simp [Stmt.gArt, Stmt.blattArt])
  | exact absurd hcov.ende_cons_art (by simp [Stmt.gArt, Stmt.blattArt])
  | (obtain ⟨_, hbo, _⟩ := hcov.dann_inv; simp [Block.ohneOrakel] at hbo; done)
  | (obtain ⟨⟨_, hbw⟩, _, _⟩ := hcov.dann_inv; cases hbw; done)
  | (obtain ⟨hew, _⟩ := hcov.ende_inv; cases hew; done)
  | cases hcov))

theorem armWahlG_G {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    ArmsG A mr arms → BlockG A mr (armWahlG arms v).2.1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => armWahlG_G rest _ h.cons_inv.2

theorem grundWahlG_G {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    GrundArmsG A mr arms → BlockG A mr (grundWahlG arms r)
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => grundWahlG_G rest _ h.cons_inv.2

theorem armWahlG_G' {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : ArmsG A mr arms) :
    BlockG A mr b := by
  have h0 := armWahlG_G arms v h
  rw [hw] at h0
  exact h0

theorem armWahlG_ohne' {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.ohneOrakel = true) :
    b.ohneOrakel = true := by
  have h0 := armWahlG_ohneOrakel arms v h
  rw [hw] at h0
  exact h0

set_option linter.unusedSimpArgs false in
theorem schrittErhalt {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestG A r) :
    ErhaltG O passes A M M' f z ρ r := by
  subst hz
  unfold ErhaltG
  cases hs with
  | blatt l2 Γ2 Λ2 Λ2' s rest ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨_, hr, _⟩ := he.cons_inv
    simp only [Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende rest hr ho.2, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_blatt O passes s rest _ _ _ ρ' hstep)
  | nimmt L _ _ _ =>
    refine Or.inl ⟨l, Γ, Λ, ρ, r, Ereignis.nimmt L (offen (M.faeden f).spur) ::
      (M.faeden f).spur, ?_, hcov, ?_⟩
    · rw [faeden_upd, ← hR]
    · rw [weltVon_upd]
      exact semR_SG O passes A r hcov _ _ ρ ⟨rfl, rfl⟩
  | gibt L _ =>
    refine Or.inl ⟨l, Γ, Λ, ρ, r, Ereignis.gibt L ::
      (M.faeden f).spur, ?_, hcov, ?_⟩
    · rw [faeden_upd, ← hR]
    · rw [weltVon_upd]
      exact semR_SG O passes A r hcov _ _ ρ ⟨rfl, rfl⟩
  | ruf _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rueck caller rst hpop Γ2 Λ2 e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueck O passes e hperm _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | endeEntf l2 Γ2 Λ2 Λ2' s rest ρ2 hent hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨hs, hr, _⟩ := he.cons_inv
    simp only [Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann (.cons s .nil) (.ende rest), _, rufUpdateG_self _ _ _, RestG.dann _ _ (BlockG.cons s .nil hs BlockG.nil) (by simp [Block.ohneOrakel, ho.1]) (RestG.ende rest hr ho.2), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeEntf O passes s rest _ _)
  | dannBlatt l2 Γ2 Λ2 Λ2' Λ2'' s rest k ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_dannBlatt O passes s rest k _ _ _ ρ' hstep)
  | dannLeer l2 Γ2 Λ2 k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | dannIteWahr l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann t (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ ht ho.1.1 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_iteWahr O passes c t e rest k _ _ hw)
  | dannIteFalsch l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann e (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ he ho.1.2 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_iteFalsch O passes c t e rest k _ _ hw)
  | dannOnOptionSome l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann p (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestG.dann _ _ hp ho.1.1 (RestG.schrumpf _ (RestG.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_optSome O passes o p a rest k _ _ v hv)
  | dannOnOptionNone l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann a (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ ha ho.1.2 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_optNone O passes o p a rest k _ _ hv)
  | dannOnTagSome l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ lo hi b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    have hbb := armWahlG_G' arms _ hw ha
    have hbo := armWahlG_ohne' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbb hbo (RestG.schrumpf _ (RestG.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_tagSome O passes v arms rest k _ _ lo hi b nutz hw)
  | dannOnTagNone l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    have hbb := armWahlG_G' arms _ hw ha
    have hbo := armWahlG_ohne' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbb hbo (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_tagNone O passes v arms rest k _ _ b nutz hw)
  | dannOnGrund l2 Γ2 Λ2 Λ2' Λ2'' n rg arms rest k ρ2 hhead σ₁ hs₁ b hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁ hw
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onGrund_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, _, _, rufUpdateG_self _ _ _, RestG.dann _ _ (grundWahlG_G arms _ ha) (grundWahlG_ohneOrakel arms _ ho.1) (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_grund O passes rg arms rest k _ _)
  | endeBind l2 Γ2 Λ2 τ e rest ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨he, ho⟩ := hcov.ende_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende rest he.bind_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeBind O passes e rest (M.weltVon f) ρ)
  | dannBind l2 Γ2 Λ2 Λ2' Λ2'' τ e rest k ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.bind_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_dannBind O passes e rest k (M.weltVon f) ρ)
  | dannNarrowOk l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_narrowOk O passes e lo' hi' sonst rest k _ _ h)
  | dannNarrowElse l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _, RestG.ende sonst hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_narrowElse O passes e lo' hi' sonst rest k _ _ h)
  | dannPruefWahr l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_pruefWahr O passes c sonst rest k _ _ hw)
  | dannPruefFalsch l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _, RestG.ende sonst hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_pruefFalsch O passes c sonst rest k _ _ hw)
  | dannBreaking l2 Γ2 Λ2 Λ2' Λ2'' i body rest k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have hbd := hst.breaking_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbd ho.1 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_breaking O passes i body rest k _ _)
  | dannLocks l2 Γ2 Λ2 Λ2'' L hrg body rest k ρ2 hhead hself hrang hfrei =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨_, hbd⟩ := hst.locks_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.frei L (.dann rest k)), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbd ho.1 (RestG.frei _ _ (RestG.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact sem_locks O passes L hrg body rest k (M.weltVon f) ρ
  | freiGib l2 Γ2 Λ2 L k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hcov.frei_inv, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | schrumpfVergiss l2 Γ2 Λ2 τ k v ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hcov.schrumpf_inv, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | travNext _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | travDone _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederUeber _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rueckBind caller rst hpop l2 Γ2 Λ2 Λ2' τ restb k ρc hcaller Γc Λc e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueck O passes e hperm _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelDannNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRet l2 Γ2 Λ2 Λ2'' e hperm rest k ρ2 hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_dannRet O passes e hperm rest k _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | rueckCons caller rst hpop Γ2 Λ2 e hperm rest ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueckCons O passes e hperm rest _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_dannRet O passes e hperm restk kk _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | rueckConsBind lk Γk Λk e hperm restk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueckCons O passes e hperm restk _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannExchange l2 Γ2 Λ2 Λ2' g neuE hw hL rest k ρ2 hhead σ₁ hs₁ σ₂ hs₂ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    subst hs₂
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.exchange_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_exchange O passes g neuE hw hL rest k (M.weltVon f) ρ)
  | dannGleit l2 Γ2 Λ2 Λ2' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleit_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleit O passes op a b lo hi rest k _ _ v hv)
  | dannGleitLit l2 Γ2 Λ2 Λ2' q lo hi rest k ρ2 hhead v hv =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleitLit_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitLit O passes q lo hi rest k _ _ v hv)
  | dannGleitVon l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleitVon_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitVon O passes e lo hi rest k _ _ v hv)
  | dannGleitNarrowOk l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitNarrowOk O passes e lo hi sonst rest k _ _ v hv)
  | dannGleitNarrowElse l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ hn neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _, RestG.ende sonst hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitNarrowElse O passes e lo hi sonst rest k _ _ hn)
  | dannBindAxiom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rueckGrund _ _ _ hhead => widerlege hhead
  | rueckConsGrund _ _ _ _ hhead => widerlege hhead
  | dannRetGrund _ _ _ _ _ hhead => widerlege hhead

/-- A step of thread `f` keeps its log or prepends one event. -/
theorem rufSchrittG_log {P : Programm D} {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O passes M f M') :
    (M'.faeden f).log = (M.faeden f).log ∨ ∃ e, (M'.faeden f).log = e :: (M.faeden f).log := by
  cases hs <;> rw [faeden_upd] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl⟩

/-! ## 17. TARGET B: the converse for the value -/

/-- The run invariant of the converse: either the frame of `fn` is still on
    top with a covered residue whose frame result agrees (up to the trace)
    with the fixed result `S`, or it has popped, and the log, below any later
    events, holds a `rueck` whose world and value agree with `S`. -/
def InvB (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (f : Faden) (fn : D.Fn)
    (rho : Env D (D.params fn)) (s0 : World D) (stapel : List (RufRahmenG D))
    (log : List (RufEreignisF D)) (S : REnde (vertragVon D fn)) (M : RufMaschineG D) : Prop :=
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D fn) l Γ Λ) (sp : List (Ereignis D)),
      M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩, sp, log⟩ ∧
      RestG A r ∧ (semR O passes r (M.weltVon f) ρ).gleich S) ∨
  (∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)),
      (M.faeden f).log = ext ++ RufEreignisF.rueck fn rho v s0 s1 :: log ∧
      (REnde.zurueck (V := vertragVon D fn) s1 v).gleich S)

theorem invB_schritt {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {f : Faden} {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {stapel : List (RufRahmenG D)} {log : List (RufEreignisF D)} {S : REnde (vertragVon D fn)}
    {M M' : RufMaschineG D} (hs : RufSchrittG P O passes M f M')
    (h : InvB O passes A f fn rho s0 stapel log S M) :
    InvB O passes A f fn rho s0 stapel log S M' := by
  rcases h with ⟨l, Γ, Λ, ρ, r, sp, hM, hc, hg⟩ | ⟨v, s1, ext, hlog, hg⟩
  · rcases schrittErhalt (A := A) hs _ hM ρ r rfl hc with
      ⟨l', Γ', Λ', ρ', r', sp', hM', hc', hg'⟩ | ⟨v, s1, hlog, hg'⟩
    · exact Or.inl ⟨l', Γ', Λ', ρ', r', sp', hM', hc', REnde.gleich_trans hg' hg⟩
    · refine Or.inr ⟨v, s1, [], ?_, REnde.gleich_trans (REnde.gleich_symm hg') hg⟩
      rw [List.nil_append]
      exact hlog
  · rcases rufSchrittG_log hs with he | ⟨e, he⟩
    · exact Or.inr ⟨v, s1, ext, by rw [he]; exact hlog, hg⟩
    · exact Or.inr ⟨v, s1, e :: ext, by rw [he, hlog]; rfl, hg⟩

theorem invB_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {f : Faden} {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {stapel : List (RufRahmenG D)} {log : List (RufEreignisF D)} {S : REnde (vertragVon D fn)}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (h : InvB O passes A f fn rho s0 stapel log S M) :
    InvB O passes A f fn rho s0 stapel log S M' := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (invB_schritt hs h)

/-- **TARGET B -- the converse for the value.** Thread `f` of `M` runs a
    frame of `fn` with residue `.ende b` for a covered, oracle-free end
    block `b`. If ANY run of thread `f` alone reaches a machine whose log is
    the old log with exactly one new event `rueck fn rho' v' s0' s1'` (the
    pop of this frame -- a further call or return would add events), then
    the sequential semantics, started at the thread's world `M.weltVon f`,
    ends normally, returning THE SAME value `v'`, in a world with the same
    shared memory as the logged `s1'`; the logged parameters and entry
    world are the frame's.

    The run may interleave the machine's bare `nimmt`/`gibt` steps (a
    thread may take and release a free lock outside any `locks`
    statement); they change only the trace, so the logged `s1'` agrees with
    `execEnd`'s world in memory, not necessarily in trace. No lock-freedom
    or holdings premise is needed: the statement is about runs that exist.
    `b.ohneOrakel` excludes `regLies`/`regLiesElse`/`awaits`, whose oracle
    sees the whole world, trace included (see the CUTS block). -/
theorem rufG_adaequat_umkehr (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (stapel : List (RufRahmenG D)) (spur : List (Ereignis D))
    (log : List (RufEreignisF D)) {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (b : Endblock D (vertragVon D fn) false Γ Λ) (A : D.Lock → Prop) (hb : EndG A b)
    (ho : b.ohneOrakel = true)
    (hM : M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (M'' : RufMaschineG D) (hl : RufLaufG P O passes f M M'')
    (rho' : Env D (D.params fn)) (v' : ErgVal D (D.erg fn)) (s0' s1' : World D)
    (hlog : (M''.faeden f).log = RufEreignisF.rueck fn rho' v' s0' s1' :: log) :
    ∃ σ', execEnd O passes keinRuf b (M.weltVon f) ρ = .zurueck σ' v' ∧
      σ'.speicher = s1'.speicher ∧ rho' = rho ∧ s0' = s0 := by
  have h0 : InvB O passes A f fn rho s0 stapel log
      (endErg (execEnd O passes keinRuf b (M.weltVon f) ρ)) M :=
    Or.inl ⟨false, Γ, Λ, ρ, .ende b, spur, hM, RestG.ende b hb ho, REnde.gleich_refl _⟩
  rcases invB_lauf hl h0 with ⟨l, Γ', Λ', ρ', r, sp, hM'', _, _⟩ | ⟨v, s1, ext, hlog', hg⟩
  · rw [hM''] at hlog
    have hlen := congrArg List.length hlog
    simp at hlen
  · rw [hlog'] at hlog
    have hext : ext = [] := by
      have hlen := congrArg List.length hlog
      simp at hlen
      exact hlen
    subst hext
    simp only [List.nil_append, List.cons.injEq, RufEreignisF.rueck.injEq] at hlog
    obtain ⟨⟨_, hrho, hv, hs0, hs1⟩, _⟩ := hlog
    have hv' : v = v' := eq_of_heq hv
    have hrho' : rho = rho' := eq_of_heq hrho
    subst hv' hrho' hs0 hs1
    revert hg
    cases hex : execEnd O passes keinRuf b (M.weltVon f) ρ with
    | zurueck σ' w =>
      intro hg
      obtain ⟨hsg, hvw⟩ := hg
      subst hvw
      exact ⟨σ', rfl, hsg.speicher.symm, rfl, rfl⟩
    | _ => intro hg; exact absurd hg id

/-- The witness body never consults the oracle. -/
theorem adRumpf_ohneOrakel : adRumpf.ohneOrakel = true := rfl

/-- **Witness for `rufG_adaequat_umkehr`.** All premises instantiated
    jointly on the `locks`/`if`/write program: the machine `adM`, the
    covered oracle-free body, the run of thread 0 that `rufG_adaequat`
    produces (a real run of the machine, through `endeEntf`, `dannLocks`,
    `dannIteWahr`, the writing `dannBlatt`, `freiGib`, ... and `rueckCons`),
    and its log, which holds exactly the pop. The converse then recovers
    from the MACHINE's log that the sequential semantics returns the logged
    value `7`, with the memory of the logged world (slot 0 moved to 5). -/
theorem rufG_adaequat_umkehr_zeuge :
    ∃ (M'' : RufMaschineG adD) (v : ErgVal adD (adD.erg adFn)) (s1 : World adD),
      RufLaufG adP adO 0 0 adM M'' ∧
      (M''.faeden 0).log = [RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) s1] ∧
      (s1.slots () 0 ()).n = 5 ∧
      ∃ σ', execEnd adO 0 keinRuf adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
        σ'.speicher = s1.speicher ∧ (show Zahl 0 100 from v).n = 7 := by
  obtain ⟨σ', v, _, h5, _, h7, M', hl, hf, _, _, _⟩ := rufG_adaequat_zeuge
  have hlog : (M'.faeden 0).log =
      RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) σ' :: [] := by rw [hf]
  obtain ⟨σ'', hex, hsp, _, _⟩ := rufG_adaequat_umkehr adP adO 0 adM 0 adFn Env.nil
    (adSp0.welt []) [adCaller] [] [] Env.nil adRumpf (fun L : adD.Lock => L = ())
    adRumpf_G adRumpf_ohneOrakel rfl M' hl Env.nil v (adSp0.welt []) σ' hlog
  exact ⟨M', v, σ', hl, hlog, h5, σ'', hex, hsp, h7⟩

/-! ## 18. AGREEMENT (formerly a finding): `traverse` now mirrors `traverseLauf`

    The old rules `dannTravWeiter`/`dannTravFertig` read the invariant at the
    unfold and SKIPPED the loop on a false start invariant (the machine then
    returned where `traverseLauf` ends in `logik .schleife`), `travNext` read
    it a second time before the first iteration, and `travDone` never read it
    after the last. The repaired rules: `dannTrav` unfolds WITHOUT a read,
    `travNext` reads before every iteration, `travDone` reads after the last
    one (both only on `true`), `dannLeaveTrav` reads after a `leave` (only on
    `true`) -- exactly the reads of `traverseLauf`. On a false read NO rule
    for the frame fires (`trav_falsch_steht`): the frame is stuck, and no
    normal return can follow, matching `logik .schleife`. The old
    counterexample now agrees (`trav_einig`). -/

/-- Is the statement a `traverse`? -/
def Stmt.istTraverse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .traverse .. => true
  | _ => false

/-- Does the residue start with a `traverse` statement? (Refutes heads whose
    statement differs where the holdings indices do not unify.) -/
def GRest.kopfTraverse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende (.cons s _) => s.istTraverse
  | .dann (.cons s _) _ => s.istTraverse
  | _ => false

set_option hygiene false in
/-- Close a step case whose head shape cannot be the given one, or whose
    side condition contradicts it. -/
macro "kopfweg" : tactic => `(tactic| (
  first
  | (rw [hR] at hhead; cases hhead; done)
  | (rw [hR] at hhead
     have hk := congrArg (fun x => GRest.kopfTraverse x.2.2.2.2) hhead
     simp [GRest.kopfTraverse, Stmt.istTraverse] at hk; done)
  | (rw [hR] at hhead; cases hhead; simp [Stmt.istBlatt] at hleaf; done)
  | (rw [hR] at hhead; cases hhead; simp [execStmt] at hstep; done)
  | (rw [hS] at hpop; cases hpop; done)))

/-- At a head `ende (traverse …; rest)` every step of `f` is a bare lock step
    (frame, stack and log kept) or the unfold `endeEntf`. -/
theorem trav_ende_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.traverse t inv body) rest)⟩) :
    (∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩) ∨
    (∃ sp, M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
      ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) .nil) (.ende rest)⟩⟩, sp, z.log⟩) := by
  subst hz
  cases hs with
  | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | nimmt => exact Or.inl ⟨_, rufUpdateG_self _ _ _⟩
  | gibt => exact Or.inl ⟨_, rufUpdateG_self _ _ _⟩
  | ruf _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueck _ _ hpop _ _ _ _ _ hhead => kopfweg
  | endeEntf _ _ _ _ _ _ _ _ hhead => (rw [hR] at hhead; cases hhead; exact Or.inr ⟨_, rufUpdateG_self _ _ _⟩)
  | dannBlatt _ _ _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | dannLeer _ _ _ _ _ hhead => kopfweg
  | dannIteWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannIteFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannOnOptionSome _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnOptionNone _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnTagSome _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ _ _ hw => kopfweg
  | dannOnTagNone _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ hw => kopfweg
  | dannOnGrund _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ hw => kopfweg
  | endeBind _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBind _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannPruefWahr _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannPruefFalsch _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannBreaking _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLocks _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | freiGib _ _ _ _ _ _ hhead => kopfweg
  | schrumpfVergiss _ _ _ _ _ _ _ hhead => kopfweg
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travDone _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederUeber _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueckBind _ _ hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep _ _ _ hs₁ hw => kopfweg
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelDannNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRet _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckCons _ _ hpop _ _ _ _ _ _ hhead => kopfweg
  | dannRetBind _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckConsBind _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead _ _ hs₁ => kopfweg
  | dannExchange _ _ _ _ _ _ hw _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitLit _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannGleitVon _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiom _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | rueckGrund _ _ _ hhead => kopfweg
  | rueckConsGrund _ _ _ _ hhead => kopfweg
  | dannRetGrund _ _ _ _ _ hhead => kopfweg

/-- At a head `dann (traverse …; rest) k` every step of `f` is a bare lock
    step or the read-free unfold `dannTrav`. -/
theorem trav_dann_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩) :
    (∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩) ∨
    (∃ sp, M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
      ⟨l, Γ, Λ, ρ, .trav t inv body (alleIndizes (D.count t)) (.dann rest k)⟩⟩, sp, z.log⟩) := by
  subst hz
  cases hs with
  | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | nimmt => exact Or.inl ⟨_, rufUpdateG_self _ _ _⟩
  | gibt => exact Or.inl ⟨_, rufUpdateG_self _ _ _⟩
  | ruf _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueck _ _ hpop _ _ _ _ _ hhead => kopfweg
  | endeEntf _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBlatt _ _ _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | dannLeer _ _ _ _ _ hhead => kopfweg
  | dannIteWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannIteFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannOnOptionSome _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnOptionNone _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnTagSome _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ _ _ hw => kopfweg
  | dannOnTagNone _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ hw => kopfweg
  | dannOnGrund _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ hw => kopfweg
  | endeBind _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBind _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannPruefWahr _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannPruefFalsch _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannBreaking _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLocks _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | freiGib _ _ _ _ _ _ hhead => kopfweg
  | schrumpfVergiss _ _ _ _ _ _ _ hhead => kopfweg
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => (rw [hR] at hhead; cases hhead; exact Or.inr ⟨_, rufUpdateG_self _ _ _⟩)
  | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travDone _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederUeber _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueckBind _ _ hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep _ _ _ hs₁ hw => kopfweg
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelDannNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRet _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckCons _ _ hpop _ _ _ _ _ _ hhead => kopfweg
  | dannRetBind _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckConsBind _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead _ _ hs₁ => kopfweg
  | dannExchange _ _ _ _ _ _ hw _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitLit _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannGleitVon _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiom _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | rueckGrund _ _ _ hhead => kopfweg
  | rueckConsGrund _ _ _ _ hhead => kopfweg
  | dannRetGrund _ _ _ _ _ hhead => kopfweg

/-- **A `traverse` whose invariant reads false is stuck.** At a head
    `trav t inv body (i :: is) k` whose invariant, read at the thread's
    current world, is false, every step of `f` is a bare lock step: frame,
    stack and log stay. The machine never runs the next iteration and never
    returns from the frame -- where `traverseLauf` ends in
    `logik .schleife`. -/
theorem trav_falsch_steht {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .trav t inv body (i :: is) k⟩)
    (hw0 : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = false) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | nimmt => exact ⟨_, rufUpdateG_self _ _ _⟩
  | gibt => exact ⟨_, rufUpdateG_self _ _ _⟩
  | ruf _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueck _ _ hpop _ _ _ _ _ hhead => kopfweg
  | endeEntf _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBlatt _ _ _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | dannLeer _ _ _ _ _ hhead => kopfweg
  | dannIteWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannIteFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannOnOptionSome _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnOptionNone _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnTagSome _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ _ _ hw => kopfweg
  | dannOnTagNone _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ hw => kopfweg
  | dannOnGrund _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ hw => kopfweg
  | endeBind _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBind _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannPruefWahr _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannPruefFalsch _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannBreaking _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLocks _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | freiGib _ _ _ _ _ _ hhead => kopfweg
  | schrumpfVergiss _ _ _ _ _ _ _ hhead => kopfweg
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => (rw [hR] at hhead; cases hhead; subst hs₁; rw [hw0] at hw; cases hw)
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travDone _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederUeber _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueckBind _ _ hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep _ _ _ hs₁ hw => kopfweg
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelDannNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRet _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckCons _ _ hpop _ _ _ _ _ _ hhead => kopfweg
  | dannRetBind _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckConsBind _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead _ _ hs₁ => kopfweg
  | dannExchange _ _ _ _ _ _ hw _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitLit _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannGleitVon _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiom _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | rueckGrund _ _ _ hhead => kopfweg
  | rueckConsGrund _ _ _ _ hhead => kopfweg
  | dannRetGrund _ _ _ _ _ hhead => kopfweg

/-- `traverse konto invariant false { }` in the witness function. -/
def adTrav : Stmt adD (vertragVon adD adFn) false [] [] [] :=
  .traverse () .falsch .nil

/-- The old counterexample body: `traverse konto invariant false { }; return 7`. -/
def adTravRumpf : Endblock adD (vertragVon adD adFn) false [] [] :=
  .cons adTrav (.ret (.wert adSieben) List.Perm.nil)

def adTravFaden : RufFadenG adD :=
  ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adTravRumpf⟩⟩,
    [], []⟩

def adTravM : RufMaschineG adD := ⟨adSp0, fun _ => adTravFaden, [], adSp0.welt []⟩

/-- The three frames the witness thread can be in: at the body, after the
    unfold of the `traverse` statement, at the loop. -/
def adTravK0 : RufRahmenG adD :=
  ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adTravRumpf⟩⟩

def adTravK1 : RufRahmenG adD :=
  ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil,
    .dann (.cons adTrav .nil) (.ende (.ret (.wert adSieben) List.Perm.nil))⟩⟩

def adTravK2 : RufRahmenG adD :=
  ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil,
    .trav () .falsch .nil (alleIndizes (adD.count ()))
      (.dann .nil (.ende (.ret (.wert adSieben) List.Perm.nil)))⟩⟩

/-- The run invariant of the witness thread: one of the three frames, the
    caller below, NOTHING logged. -/
def AdTravZ (M : RufMaschineG adD) : Prop :=
  ∃ sp, M.faeden 0 = ⟨[adCaller], adTravK0, sp, []⟩ ∨
    M.faeden 0 = ⟨[adCaller], adTravK1, sp, []⟩ ∨
    M.faeden 0 = ⟨[adCaller], adTravK2, sp, []⟩

theorem adTravZ_schritt {M M' : RufMaschineG adD} (hs : RufSchrittG adP adO 0 M 0 M')
    (h : AdTravZ M) : AdTravZ M' := by
  obtain ⟨sp, h | h | h⟩ := h
  · rcases trav_ende_schritt hs _ h () .falsch .nil (.ret (.wert adSieben) List.Perm.nil)
      Env.nil rfl with ⟨sp', e⟩ | ⟨sp', e⟩
    · exact ⟨sp', Or.inl e⟩
    · exact ⟨sp', Or.inr (Or.inl e)⟩
  · rcases trav_dann_schritt hs _ h () .falsch .nil .nil
      (.ende (.ret (.wert adSieben) List.Perm.nil)) Env.nil rfl with ⟨sp', e⟩ | ⟨sp', e⟩
    · exact ⟨sp', Or.inr (Or.inl e)⟩
    · exact ⟨sp', Or.inr (Or.inr e)⟩
  · obtain ⟨sp', e⟩ := trav_falsch_steht hs _ h () .falsch .nil
      ⟨0, by decide, by decide⟩ [⟨1, by decide, by decide⟩]
      (.dann .nil (.ende (.ret (.wert adSieben) List.Perm.nil))) Env.nil rfl rfl
    exact ⟨sp', Or.inr (Or.inr e)⟩

theorem adTravZ_lauf {M M' : RufMaschineG adD} (hl : RufLaufG adP adO 0 0 M M')
    (h : AdTravZ M) : AdTravZ M' := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (adTravZ_schritt hs h)

/-- **The old counterexample now AGREES.** The sequential semantics of
    `traverse konto invariant false { }; return 7` ends in `logik .schleife`;
    and NO run of thread 0 of the machine logs anything at all -- in
    particular no return of `7`, which the old rule `dannTravFertig`
    produced. -/
theorem trav_einig :
    execEnd adO 0 keinRuf adTravRumpf (adTravM.weltVon 0) Env.nil =
      .logik .schleife ∧
    ∀ M' : RufMaschineG adD, RufLaufG adP adO 0 0 adTravM M' → (M'.faeden 0).log = [] := by
  refine ⟨rfl, ?_⟩
  intro M' hl
  obtain ⟨sp, h | h | h⟩ := adTravZ_lauf hl ⟨[], Or.inl rfl⟩ <;> rw [h]

/-! ## 19. AGREEMENT (formerly a finding): `ruf` continues after the call

    The old `ruf`/`rufCallInd` pushed the caller frame UNCHANGED, so after
    `rueck` the caller executed the same call again. The repaired rules push
    the caller with its residue advanced to `.ende rest` at holdings
    `nach D g Λ` (resp. `nachSig`), exactly like `rufDann`. In the machine's
    own witness run (`M0G` … `M7G`) the restored caller is now the frame
    after the call, whose residue is the parameter return, and no further
    step of thread 0 logs anything: the callee is entered exactly once, as
    in the sequential semantics. Bodies with calls are adequate in general
    (`RufAdaequatRufG.lean`). -/

/-- At an EMPTY stack a head `ende (ret e)` is final for the log: every step
    of `f` is a bare lock step (no frame to pop to, no call to make). -/
theorem ret_leer_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) (hS : z.stapel = []) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hperm)⟩) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | nimmt => exact ⟨_, rufUpdateG_self _ _ _⟩
  | gibt => exact ⟨_, rufUpdateG_self _ _ _⟩
  | ruf _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueck _ _ hpop _ _ _ _ _ hhead => kopfweg
  | endeEntf _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBlatt _ _ _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | dannLeer _ _ _ _ _ hhead => kopfweg
  | dannIteWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannIteFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannOnOptionSome _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnOptionNone _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnTagSome _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ _ _ hw => kopfweg
  | dannOnTagNone _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ hw => kopfweg
  | dannOnGrund _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ hw => kopfweg
  | endeBind _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBind _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannPruefWahr _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannPruefFalsch _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannBreaking _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLocks _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | freiGib _ _ _ _ _ _ hhead => kopfweg
  | schrumpfVergiss _ _ _ _ _ _ _ hhead => kopfweg
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travDone _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederUeber _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueckBind _ _ hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep _ _ _ hs₁ hw => kopfweg
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelDannNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRet _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckCons _ _ hpop _ _ _ _ _ _ hhead => kopfweg
  | dannRetBind _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckConsBind _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead _ _ hs₁ => kopfweg
  | dannExchange _ _ _ _ _ _ hw _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitLit _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannGleitVon _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiom _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | rueckGrund _ _ _ hhead => kopfweg
  | rueckConsGrund _ _ _ _ hhead => kopfweg
  | dannRetGrund _ _ _ _ _ hhead => kopfweg

theorem ruf_fortsetzung :
    (M7G.faeden 0).kopf = callerFrameG ∧
    callerFrameG.rest = ⟨false, rufDF.params rufCallerF, nach rufDF rufIncF [], rhoCallerF,
      .ende callerRestG⟩ ∧
    (M7G.faeden 0).log = [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G,
      RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0),
      RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] ∧
    ∀ M8 : RufMaschineG rufDF, RufSchrittG gP rufOF 0 M7G 0 M8 →
      (M8.faeden 0).log = (M7G.faeden 0).log := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro M8 hs
  obtain ⟨sp, e⟩ := ret_leer_schritt hs _ rfl rfl _ _ _ rfl
  rw [e]

/-! ## CUTS:
  What is proved: TARGET A (`rufG_adaequat`, and `rufG_adaequat_R` for any
  call handler) and TARGET B (`rufG_adaequat_umkehr`) for the covered
  fragment `EndG`/`StmtG`/`BlockG`/`ArmsG`/`GrundArmsG`, each with a joint
  witness on a `locks { if { write } }; return` body; the two former
  FINDINGS against G's step rules, now repaired, as agreement theorems
  (`trav_falsch_steht`, `trav_einig`, `ruf_fortsetzung`). TARGET A (and
  `rufG_adaequat_R`) carry the premise `hnw : caller.wartend = false`
  since the verbatim pops were repaired (2026-09-13): a premise about the
  concrete caller frame (no waiting residue), true for every caller whose
  frame the machine did not push with a bind-call; the witness's caller
  satisfies it by `rfl`. What is NOT proved here:

  - Calls of every form (`call`, `callInd`, `bindCall`, `bindCallInd`,
    `bindCallElse`): direct calls and bind-calls are covered in
    `RufAdaequatRufG.lean` (TARGET 4, any nesting depth), after the repair
    of `ruf`/`rufCallInd` (they pushed the caller frame with its unchanged
    residue, so after `rueck` the caller repeated the call).
  - `traverse`: after the repair (`dannTrav` reads nothing, `travNext`/
    `travDone`/`dannLeaveTrav` read exactly where `traverseLauf` does, a
    false read fires no rule) the rules agree with `traverseLauf`
    (`trav_falsch_steht`); the loop is simulated in `RufAdaequatRufG.lean`
    (`travOkR`/`travRetR`, with bounded `retry`: `retryOkR`/`retryRetR`),
    not in this file's fragment.
  - `forever`, `leave`, `next`: the peel rules and the abrupt-exit shims
    are not simulated (no RufRest invariant for `ewigRest`, no abrupt-exit
    simulation). Not a finding; not done. (The former gap "a `sonst` ending
    in `ret` inside a loop body stalls" is closed: `rueck` and `rueckCons`
    now accept any loop level.)
  - `retGrund`, `Endblock.retGrund`, `Endblock.leave`/`next`, and every
    `sonst` branch that does not end in `ret` at loop level `false`
    (machine has no grund rule; `leave`/`next` at `ende` are G's CUTS).
  - `axiomCall`, `bindAxiom`: the oracle may answer with any world, the
    machine step demands a trace that extends the old one without `nimmt`
    (`hneu`/`hkein_nimmt`); a premise on the oracle would close it, none
    is taken.
  - A `ret` under a `locks` body (the `mr = false` flag): `dannRet` pops
    without the `gibt` that `execStmt`'s `locks` appends to the return
    world, so the logged world would differ in the trace. Such a `ret` is
    untypable in a function body (`V.ende` names only entry locks, the
    `locks` rank rule excludes them), so nothing real is lost.
  - TARGET B needs `ohneOrakel` (no `regLies`/`regLiesElse`/`awaits`): the
    machine's bare `nimmt`/`gibt` steps let a thread take and release a
    free lock at any time; that changes only its trace, but those three
    forms hand the whole world, trace included, to the oracle, so a
    trace-reading oracle can then answer differently. TARGET A covers
    them (its run has no bare lock steps). B relates the logged world to
    `execEnd`'s world in MEMORY only (`σ'.speicher = s1'.speicher`), since
    bare lock steps add trace events; A states full equality `s1 = σ'`.
  - Only single-thread runs (`RufLaufG` = steps of thread `f`); no
    statement about interleavings with other threads beyond the
    lock-freedom premise of A (`hfrei`, on the locks the body may take).
  - No contract discharge: `requires`/`ensures`/invariants are not checked
    by the machine and not related to `rueck` events here.
-/

#print axioms Gabbro.Grammatik.rufG_adaequat
#print axioms Gabbro.Grammatik.rufG_adaequat_R
#print axioms Gabbro.Grammatik.rufG_adaequat_zeuge
#print axioms Gabbro.Grammatik.rufG_adaequat_umkehr
#print axioms Gabbro.Grammatik.rufG_adaequat_umkehr_zeuge
#print axioms Gabbro.Grammatik.trav_falsch_steht
#print axioms Gabbro.Grammatik.trav_einig
#print axioms Gabbro.Grammatik.ruf_fortsetzung
#print axioms Gabbro.Grammatik.schrittErhalt
#print axioms Gabbro.Grammatik.blockOk
#print axioms Gabbro.Grammatik.endRet

end Gabbro.Grammatik


