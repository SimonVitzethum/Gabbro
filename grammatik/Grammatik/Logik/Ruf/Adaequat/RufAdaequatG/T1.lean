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
import Grammatik.Logik.Ruf.Maschine.RufMaschineG
import Grammatik.Logik.Ruf.Hoare.HoareRegeln

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

/-- An access event (table or global) or a question to the outside -- never a lock event. -/
def Ereignis.istZugriff : Ereignis D → Bool
  | .zugriff .. => true
  | .gzugriff .. => true
  | .fremd .. => true
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
      | fremd => simpa [offen] using ih
      | nimmt => simp only [Ereignis.istZugriff, Bool.false_eq_true] at he
      | gibt => simp only [Ereignis.istZugriff, Bool.false_eq_true] at he

theorem kein_nimmt {neu : List (Ereignis D)} (h : NurZugriff neu) :
    ∀ (L : D.Lock) (hs : List D.Lock), Ereignis.nimmt L hs ∉ neu := by
  intro L hs hm
  have := h _ hm
  simp only [Ereignis.istZugriff, Bool.false_eq_true] at this

/-- `σ'` extends `σ` by access events only. -/
def Erw (σ σ' : World D) : Prop :=
  ∃ neu, σ'.spur = neu ++ σ.spur ∧ NurZugriff neu

theorem Erw.refl (σ : World D) : Erw σ σ :=
  ⟨[], rfl, fun e he => by simp only [List.not_mem_nil] at he⟩

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

theorem Erw.fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : Erw σ (σ.fragt q) :=
  ⟨[.fremd q], rfl, fun e he => by simp only [List.mem_singleton] at he; subst he; rfl⟩

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
  | assignThru (n : Nat) (p : Expr D Γ Λ (.ptr n true)) (t : D.Tab)
      (ht : D.tabNr n = some t) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      BlattG (l := l) (.assignThru p t ht f i e hw hL)
  | assignSlotRef (n : Nat) (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t)
      (ho : D.offen t = true) (f : D.Feld t) (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true)
      (hL : darf D t Λ) :
      BlattG (l := l) (.assignSlotRef r t ht ho f e hw hL)
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) :
      BlattG (l := l) (.assignGlob g e hw hL)
  | putBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true)
      (hL : darf D t Λ) :
      BlattG (l := l) (.putBytes t f hf n i hlo hhi e hw hL)
  | assignVar {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ) :
      BlattG (l := l) (.assignVar (τ := τ) x e)
  | shift (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      BlattG (l := l) (.shift t f hτ i von nach hn he hw hL)
  | regWrite (r : D.Reg) (hk : (D.rklasse r).schreibbar = true)
      (e : Expr D Γ Λ (D.rtyp r)) :
      BlattG (l := l) (.regWrite r hk e)
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
  | .assignSlot .. | .assignThru .. | .assignSlotRef .. | .assignGlob .. | .putBytes .. | .assignVar ..
  | .shift .. | .regWrite .. | .transition .. | .publish .. | .advances ..
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
  | assignThru n p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
  | assignSlotRef n r t ht ho f e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _)
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact (Erw.lese _ _ _).trans (Erw.schreibBytes _ _ _ _ _ _ _)
  | assignVar x e =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.lese _ _ _
  | shift t f hτ i von nach hn he hw hL =>
      simp only [execStmt] at hex
      split at hex
      · simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, -⟩ := hex
        exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
      · cases hex
  | regWrite r hk e =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.lese _ _ _
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, -⟩ := hex
      exact Erw.fragt _ _
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
  | onWhy {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (r : Expr D Γ Λ (.why n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (ha : GrundArmsG A mr arms) : StmtG A mr (.onWhy r arms)
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
  | regRead {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hr : BlockG A mr rest) :
      BlockG A mr (.regRead r hk rest)
  | regReadElse {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (D.rtyp r :: Γ) Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.regReadElse r hk zusage sonst rest)
  | awaits {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (hat : D.atomar g = true) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.awaits g payload hp hL hat rest)
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
  | check {Γ : Ctx} {Λ Λ' : List (Res D)}
      (c : Expr D Γ Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false Γ Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.check c sonst rest)
  | float {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int}
      (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.float op a b lo hi rest)
  | floatLit {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (q lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockG A mr rest) : BlockG A mr (.floatLit q lo hi rest)
  | floatOf {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int}
      (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockG A mr rest) :
      BlockG A mr (.floatOf e lo hi rest)
  | floatNarrow {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
      (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (.fl lo hi :: Γ) Λ Λ')
      (hs : EndG A sonst) (hr : BlockG A true rest) :
      BlockG A true (.floatNarrow e lo hi sonst rest)

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
  | .ite .. | .onOption .. | .onTag .. | .onWhy .. | .breaking .. | .locks ..
  | .ret .. => true
  | s => s.blattArt

theorem StmtG.art {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : StmtG A mr s) : s.gArt = true := by
  cases h with
  | blatt _ hb => cases hb <;> rfl
  | _ => rfl

/-! Inversion lemmas: the simulation recurses on the SYNTAX, so it must not
    `cases` the coverage proof (that would rename the recursive subterms). -/


end Gabbro.Grammatik
