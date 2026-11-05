module
public import Runner.Beweis.Satz
@[expose] public section


/-! # The loader: from the ELF entry to the first dispatch

`loadTree x` is what the loader does, as a request tree from the entry state `x` (Linux's initial stack at
`rsp`): read `argv[1]`; `open` it; `lseek` to its end for the length; `mmap` it at `IMG`; read the image's first
word, the first frame. A negative `open` or `lseek` answer, a zero length or an `mmap` answer other than `IMG`
ends in `ud2` (a fault). Then the IR thread starts at `IMG + 16` with that frame.

`loader_ok`: from the entry, the x86 thread makes exactly these requests and ends at a dispatch copy related to
the first IR state. `runner_entry_tso`: every observation of the process from its first instruction is an
observation of the IR process whose first thread begins with `loadTree`. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog Runner.Mach

set_option linter.unusedSimpArgs false

def TBL : Nat := BASE + tblOff

/-- After `mmap`: read the first frame, start at `IMG + 16`. -/
def t4 : Res IR.T := rd64 (BitVec.ofNat 64 IMG) fun fp => .next ⟨BitVec.ofNat 64 IMG + 16, fp⟩

/-- `mmap(IMG, len, 3, MAP_PRIVATE|MAP_FIXED_NOREPLACE, fd, 0)` must answer `IMG`. -/
def t3 (fd len : W) : Res IR.T :=
  .ask (.sys ⟨9, BitVec.ofNat 64 IMG, len, 3, 0x100002, fd, 0⟩) fun r => opt r fun u =>
  if u.1 = BitVec.ofNat 64 IMG then t4 else .fault

/-- `lseek(fd, 0, SEEK_END)` must answer a positive length. -/
def t2 (r10 r8 r9 fd : W) : Res IR.T :=
  .ask (.sys ⟨8, fd, 0, 2, r10, r8, r9⟩) fun r => opt r fun q =>
  if q.1.msb then .fault else if q.1 = 0 then .fault else t3 fd q.1

/-- From the ELF entry: `argv[1]`, `open` it (a negative answer faults), then the rest. -/
def loadTree (x : X) : Res IR.T :=
  rd64 (x.rsp + 16) fun path =>
  .ask (.sys ⟨2, path, 0, 0, x.r10, x.r8, x.r9⟩) fun r => opt r fun p =>
  if p.1.msb then .fault else t2 x.r10 x.r8 x.r9 p.1

set_option maxRecDepth 100000 in
/-- The loader's code: the loader at its label, checked on the concrete bytes. -/
theorem loader_placed : ((loaderI TBL).all Ins.ok &&
    ((loaderI TBL).flatMap enc).isPrefixOf (image.drop (find tab LOADER))) = true := by
  decide +kernel

theorem addr_eq (a : W) (m n : Nat) (h : n < 2 ^ 31) :
    a + BitVec.ofNat 64 m + sx32 (BitVec.ofNat 32 n) = a + BitVec.ofNat 64 (m + n) := by
  rw [sx32_ofNat h, BitVec.ofNat_add, BitVec.add_assoc]

/-- A jump to the loader's own `ud2` faults. -/
theorem bad_at {z : X} (hc : Code L0.C z.rip [.ud2]) : Match L0 .fault z :=
  .fault ((step_code hc).trans rfl)

macro "rip_simp" : tactic => `(tactic| (
  simp (disch := decide) only [Bool.and_self, BitVec.and_self, sx32_ofNat] at *
  simp [lenOfL, lenOf, ld1, ld2, ld4, ld5, ldj1, ldj2, ldj3, ldj4, dispatch, enc, memEnc, regEnc, le32, mb, ms,
    BitVec.ofNat_add, BitVec.add_assoc, X.nof, X.set, X.cmpf, aluStep] at *))

set_option maxRecDepth 100000 in
theorem tbl_small : BASE + tblOff < 2 ^ 31 := by decide +kernel

/-- The control read is supplied by the loaded readonly file, independently of
    the process's initial MXCSR and of optional DAZ support. -/
private theorem load_control {L : Lay} {r : Res IR.T} {y : X} {is : List Ins}
    (hc : Code L.C y.rip (.ldmxcsr (mb .r14 2048) :: is))
    (ht : y.r14 = L.T)
    (hn : Match L r { y with
      rip := y.rip + BitVec.ofNat 64 (enc (.ldmxcsr (mb .r14 2048))).length
      mxcsr := 0x1F80 }) : Match L r y := by
  have displacement : sx32 (2048#32) =
      (256#64) * BitVec.ofNat 64 (2 ^ 3) + sx32 (0#32) := by decide
  have ha : ea y (mb .r14 2048) = taddr L (BitVec.ofNat 64 256) := by
    change y.r14 + sx32 (2048#32) =
      L.T + (256#64) * BitVec.ofNat 64 (2 ^ 3) + sx32 (0#32)
    calc
      y.r14 + sx32 (2048#32) = L.T + sx32 (2048#32) :=
        congrArg (fun value : W => value + sx32 (2048#32)) ht
      _ = L.T + ((256#64) * BitVec.ofNat 64 (2 ^ 3) + sx32 (0#32)) :=
        congrArg (fun value : W => L.T + value) displacement
      _ = L.T + (256#64) * BitVec.ofNat 64 (2 ^ 3) + sx32 (0#32) :=
        (BitVec.add_assoc _ _ _).symm
  have valid : (0x1F80 : BitVec 32).toNat < 65536 ∧
      ((0x1F80 : BitVec 32).getLsbD 6 = false ∨ y.dazSupported = true) :=
    ⟨by decide, Or.inl (by decide)⟩
  refine .tbl (k := fun a => opt a fun p =>
    if (p.1.setWidth 32).toNat < 65536 ∧
        ((p.1.setWidth 32).getLsbD 6 = false ∨ y.dazSupported = true) then
      .next { y with
        rip := y.rip + BitVec.ofNat 64 (enc (.ldmxcsr (mb .r14 2048))).length
        mxcsr := p.1.setWidth 32 }
    else .fault) 256 (by decide) ?_ fun w => ?_
  · rw [step_code hc]
    simp only [exec, rd32, ha, readOnlyWidth, ite_true]
  · simp only [readOnlyValue, ite_true, opt_some]
    change MatchK L r (if (0x1F80 : BitVec 32).toNat < 65536 ∧
        ((0x1F80 : BitVec 32).getLsbD 6 = false ∨ y.dazSupported = true) then _ else .fault)
    rw [if_pos valid]
    exact .knext hn

/-- Read the first frame and reach dispatch from the actual established mode.
    Keep the layout and starting state abstract while proving the request tree. -/
private theorem initial_dispatch {L : Lay} {y : X}
    (hc : Code L.C y.rip
      ([.ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)] ++ dispatch ++ [.ud2]))
    (hx : y.rcx = BitVec.ofNat 64 IMG) (ht : y.r14 = L.T) (hm : y.fpReady = true) :
    Match L t4 y := by
  let body : List Ins := [.ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)]
  let loaded (fp : W) : X := ({ y with rip := (y.rip +
    BitVec.ofNat 64 (enc (.ld .r13 (mb .rcx))).length) }).set .r13 fp
  let after (fp : W) : X := ({ loaded fp with rip := ((loaded fp).rip +
    BitVec.ofNat 64 (enc (.lea .r12 (mb .rcx 16))).length) }).set .r12
      (ea (loaded fp) (mb .rcx 16))
  have address : ea y (mb .rcx) = BitVec.ofNat 64 IMG := by
    change y.rcx + sx32 (0#32) = _
    rw [sx32_zero, BitVec.add_zero]
    exact hx
  have first : exec (.ld .r13 (mb .rcx)) (enc (.ld .r13 (mb .rcx))).length y =
      rd64 (BitVec.ofNat 64 IMG) (fun fp => .next (loaded fp)) := by
    simp only [exec, address]
    rfl
  have rest (fp : W) : runL [.lea .r12 (mb .rcx 16)] (loaded fp) = .next (after fp) := rfl
  have run : runL body y = rd64 (BitVec.ofNat 64 IMG) (fun fp => .next (after fp)) := by
    change (exec (.ld .r13 (mb .rcx)) (enc (.ld .r13 (mb .rcx))).length y).bind
      (runL [.lea .r12 (mb .rcx 16)]) = _
    rw [first]
    simp only [rd64, bind_ask, bind_opt, bind_next, rest]
  have position (fp : W) : (after fp).rip = y.rip + BitVec.ofNat 64 (lenOfL body) := by
    dsimp only [after, loaded, X.set]
    simp [body, lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have placed : Code L.C (y.rip + BitVec.ofNat 64 (lenOfL body)) dispatch :=
    code_prefix (code_append (is := body) hc)
  have finished (fp : W) : Match L (.next ⟨BitVec.ofNat 64 IMG + 16, fp⟩) (after fp) := by
    refine .disp ⟨?_, ?_, rfl, ht, hm⟩
    · rw [position]
      exact placed
    · change y.rcx + sx32 (16#32) = BitVec.ofNat 64 IMG + (16#64)
      exact congr (congrArg (fun a b : W => a + b) hx) sx32_16
  have continued : CorrM L t4 (runL body y) := by
    rw [run]
    simp only [t4, rd64]
    apply corrM_ask
    intro answer
    apply corrM_opt
    intro result
    exact finished result.1
  exact go body y t4 (by decide) (code_prefix hc) continued

/-- Instantiate the actual MOVI/LDMXCSR pair only after the remaining loader
    continuation has been proved over an abstract table word and state. -/
private theorem initialize_control {L : Lay} {y : X} (tableWord : BitVec 32)
    (hc : Code L.C y.rip (.movi .r14 tableWord :: .ldmxcsr (mb .r14 2048) ::
      [ .ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)] ++ dispatch ++ [.ud2]))
    (ht : sx32 tableWord = L.T) (hx : y.rcx = BitVec.ofNat 64 IMG) : Match L t4 y := by
  let first : Ins := .movi .r14 tableWord
  let y1 : X := ({ y with rip := (y.rip + BitVec.ofNat 64 (enc first).length) }).set
    .r14 (sx32 tableWord)
  have hc1 : Code L.C y1.rip (.ldmxcsr (mb .r14 2048) ::
      [ .ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)] ++ dispatch ++ [.ud2]) := hc.2.2
  have table : y1.r14 = L.T := ht
  have base : y1.rcx = BitVec.ofNat 64 IMG := hx
  refine .priv ((step_code hc).trans (show exec first (enc first).length y = .next y1 from rfl)) ?_
  apply load_control hc1 table
  let y2 : X := { y1 with
    rip := (y1.rip + BitVec.ofNat 64 (enc (.ldmxcsr (mb .r14 2048))).length)
    mxcsr := 0x1F80 }
  have hc2 : Code L.C y2.rip
      ([.ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)] ++ dispatch ++ [.ud2]) := hc1.2.2
  have mode : y2.fpReady = true := by
    change ((0x1F80 : BitVec 32) &&& 0xFFC0 == 0x1F80) = true
    decide
  exact initial_dispatch hc2 base table mode

theorem seg5 {y : X} (hc : Code L0.C y.rip (ld5 TBL ++ [.ud2])) (hx : y.rcx = BitVec.ofNat 64 IMG) :
    Match L0 t4 y := by
  have code : Code L0.C y.rip (.movi .r14 (BitVec.ofNat 32 TBL) ::
      .ldmxcsr (mb .r14 2048) :: [.ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)] ++ dispatch ++ [.ud2]) := by
    simpa only [ld5, List.cons_append, List.nil_append, List.append_assoc] using hc
  have table : sx32 (BitVec.ofNat 32 TBL) = L0.T := sx32_ofNat (n := TBL) tbl_small
  exact initialize_control (BitVec.ofNat 32 TBL) code table hx

theorem seg4 {y : X} (hc : Code L0.C y.rip (ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2])) :
    Match L0 (t3 y.rbx y.rax) y := by
  have hc' : Code L0.C y.rip ((ld4 ++ [ldj4]) ++ (ld5 TBL ++ [.ud2])) := by simpa using hc
  have hrest := code_append hc'
  have hbad := code_append (is := ld4 ++ [ldj4] ++ ld5 TBL) (js := [.ud2]) hc
  apply go (ld4 ++ [ldj4]) y _ (by decide) (code_prefix hc')
  simp [t3, runL, exec, ld4, ldj4, mb, ea, X.get, X.set, X.nof, aluStep, X.cmpf, Cond.eval, eq_flags]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  rename_i _ u
  simp only [CorrM]
  by_cases hu : u.1 = BitVec.ofNat 64 IMG
  · simp only [hu, ↓reduceIte]
    apply seg5
    · rip_simp
      simpa [hu] using hrest
    · simp (disch := decide) only [sx32_ofNat]
  · simp only [hu, ↓reduceIte]
    apply bad_at
    rip_simp
    simpa [hu] using hbad

theorem seg4' {y : X} {fd len : W} (hc : Code L0.C y.rip (ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2]))
    (hb : y.rbx = fd) (ha : y.rax = len) : Match L0 (t3 fd len) y := by
  subst hb; subst ha; exact seg4 hc

theorem seg2 {y : X} (hc : Code L0.C y.rip (ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2])) :
    Match L0 (t2 y.r10 y.r8 y.r9 y.rax) y := by
  have hc' : Code L0.C y.rip ((ld2 ++ [ldj2]) ++ ([ldj3] ++ (ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2]))) := by
    simpa using hc
  have h3 := code_append hc'
  have h4 := code_append (is := ld2 ++ [ldj2, ldj3]) (js := ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2]) (by simpa using hc)
  have hbad := code_append (is := ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 TBL) (js := [.ud2]) hc
  apply go (ld2 ++ [ldj2]) y _ (by decide) (code_prefix hc')
  simp [t2, runL, exec, ld2, ldj2, mb, ea, X.get, X.set, X.nof, aluStep, Cond.eval]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  rename_i _ q
  simp only [CorrM]
  by_cases hs : q.1.msb = true
  · simp only [hs, ↓reduceIte]
    apply bad_at
    rip_simp
    simpa [hs] using hbad
  · simp only [hs, ↓reduceIte, Bool.false_eq_true]
    apply go [ldj3] _ _ (by decide) (by rip_simp; simpa [hs] using code_prefix h3)
    simp [runL, exec, ldj3, Cond.eval]
    by_cases hz : q.1 = 0#64
    · simp only [hz, ↓reduceIte, CorrM]
      apply bad_at
      rip_simp
      simpa [hs, hz] using hbad
    · simp only [hz, ↓reduceIte, CorrM]
      refine seg4' ?_ rfl rfl
      rip_simp
      simpa [hs, hz] using h4

theorem seg2' {y : X} {a b c fd : W}
    (hc : Code L0.C y.rip (ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2]))
    (h10 : y.r10 = a) (h8 : y.r8 = b) (h9 : y.r9 = c) (hfd : y.rax = fd) : Match L0 (t2 a b c fd) y := by
  subst h10; subst h8; subst h9; subst hfd; exact seg2 hc

theorem loader_at {x : X} (hc : Code L0.C x.rip (loaderI TBL)) : Match L0 (loadTree x) x := by
  have hc' : Code L0.C x.rip ((ld1 ++ [ldj1]) ++ (ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 TBL ++ [.ud2])) := by
    simpa [loaderI] using hc
  have h2 := code_append hc'
  have hbad := code_append (is := ld1 ++ [ldj1] ++ ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 TBL)
    (js := [.ud2]) (by simpa [loaderI] using hc)
  apply go (ld1 ++ [ldj1]) x _ (by decide) (code_prefix hc')
  simp [loadTree, runL, exec, ld1, ldj1, mb, ea, X.get, X.set, X.nof, aluStep, Cond.eval, rd64]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  rename_i _ _ _ p
  simp only [CorrM]
  by_cases hs : p.1.msb = true
  · simp only [hs, ↓reduceIte]
    apply bad_at
    rip_simp
    simpa [hs] using hbad
  · simp only [hs, ↓reduceIte, Bool.false_eq_true]
    refine seg2' ?_ rfl rfl rfl rfl
    rip_simp
    simpa [hs] using h2

theorem loader_ok {x : X} (hrip : x.rip = BitVec.ofNat 64 (BASE + find tab LOADER)) :
    Match L0 (loadTree x) x := by
  have hp := loader_placed
  simp only [Bool.and_eq_true] at hp
  exact loader_at (by rw [hrip]; exact code_of_image hp.1 hp.2)

/-- From the process's first instruction: every observation of the runner under x86-TSO, with all the threads
    it starts, is an observation of the IR process whose first thread begins with the loader's requests. -/
theorem runner_entry_tso {s : (TSO L0).St} {x : X} (hrip : x.rip = BitVec.ofNat 64 (BASE + find tab LOADER))
    {l : List Ev} {e : Ende} {n : Nat} (h : Tr (TSO L0) (actX L0) ⟨s, [some x]⟩ l e n) :
    e ≠ .unk ∧ ∃ m, Tr (TSO L0) actI ⟨s, [some (loadTree x)]⟩ l e m := by
  refine runner_mt (tso_fixed L0) cinv_L0 n ⟨rfl, fun j => ?_⟩ h
  match j with
  | 0 => exact loader_ok hrip
  | j + 1 => trivial

theorem runner_entry_sc {s : (SC L0).St} {x : X} (hrip : x.rip = BitVec.ofNat 64 (BASE + find tab LOADER))
    {l : List Ev} {e : Ende} {n : Nat} (h : Tr (SC L0) (actX L0) ⟨s, [some x]⟩ l e n) :
    e ≠ .unk ∧ ∃ m, Tr (SC L0) actI ⟨s, [some (loadTree x)]⟩ l e m := by
  refine runner_mt (sc_fixed L0) cinv_L0 n ⟨rfl, fun j => ?_⟩ h
  match j with
  | 0 => exact loader_ok hrip
  | j + 1 => trivial

set_option maxRecDepth 100000 in
/-- The ELF header's entry point is the loader. -/
theorem entry_is_loader : (ehdr.drop 24).take 8 = leN 8 (BASE + find tab LOADER) := by decide +kernel

end Runner.Beweis
