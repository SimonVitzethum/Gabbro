module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF

@[expose] public section



namespace Gabbro.Grammatik

/-- A run-time library function (PLAN-ERWEITUNG.md section 6, lane E2):
    ordinary parameters, a payload type (a table or tree type on the
    checker side; one more parameter here), an optional result, and
    declared effects. -/
structure BibliotheksFunktion (D : Deklaration) where
  params : List Ty
  nutzlast : Ty
  erg : Option Ty
  schreibt : D.Tab → Bool
  gschreibt : D.Glob → Bool

/-- The axiom serving a library function: its parameter list is the
    ordinary parameters with the payload appended, its result is the
    declared one, and its declared effects agree with the library
    function's. -/
def DientBibliothek (D : Deklaration) (L : BibliotheksFunktion D)
    (a : D.Ax) : Prop :=
  D.aparams a = L.params ++ [L.nutzlast] ∧ D.aerg a = L.erg ∧
  (∀ t, D.aschreibt a t = L.schreibt t) ∧
  ∀ g, D.agschreibt a g = L.gschreibt g

/-! ## 1. Argument lists split at the payload -/

/-- Appending the payload argument to the ordinary arguments gives
    arguments for the axiom's full parameter list. Both append equations
    hold by computation (`rfl`); the `have` names them so the cast reads. -/
def args_snoc (D : Deklaration) {Γ : Ctx} {Λ : List (Res D)}
    {ps : List Ty} {p : Ty} :
    Args D Γ Λ ps → Expr D Γ Λ p → Args D Γ Λ (ps ++ [p])
  | .nil, last =>
    have h : ([] : List Ty) ++ [p] = [p] := rfl
    h ▸ Args.cons last .nil
  | .cons e rest, last =>
    have h : ∀ (τ : Ty) (qs : List Ty) (q : Ty),
        (τ :: qs) ++ [q] = τ :: (qs ++ [q]) := fun _ _ _ => rfl
    h _ _ _ ▸ Args.cons e (args_snoc D rest last)

/-- Splitting arguments for the full list into the ordinary arguments
    and the payload argument. Induction on the ordinary parameters; at
    each step the append equation is named (`rfl`) and the impossible
    `nil` case is closed by the tactic from index unification. -/
theorem args_unsnoc (D : Deklaration) {Γ : Ctx} {Λ : List (Res D)}
    (ps : List Ty) (p : Ty) (args : Args D Γ Λ (ps ++ [p])) :
    ∃ (rest : Args D Γ Λ ps) (last : Expr D Γ Λ p), True := by
  revert args
  induction ps with
  | nil =>
    intro args
    have h : ([] : List Ty) ++ [p] = [p] := rfl
    rw [h] at args
    cases args
    case cons last rest => exact ⟨rest, last, trivial⟩
  | cons t ps ih =>
    intro args
    have h : (t :: ps) ++ [p] = t :: (ps ++ [p]) := rfl
    rw [h] at args
    cases args
    case cons e rest =>
      obtain ⟨r, l, _⟩ := ih rest
      exact ⟨Args.cons e r, l, trivial⟩

/-! ## 2. The call obligations are the `axiomCall` obligations -/

/-- A library call is an `Ax` whose parameter list includes the payload
    (PLAN-ERWEITUNG.md section 6, lane E2): the typing obligation (the
    full argument list) together with the effect obligations (callee
    effects inside the caller's contract, accesses guarded) -- checked
    as ordinary arguments plus the payload argument against the declared
    library function -- are exactly the `Stmt.axiomCall` premises for
    the serving axiom. Both directions use the whole bridge `hDient`:
    `hap` transports the argument list, `herg` the result, `hschw` and
    `hgschw` the four effect premises. -/
theorem bibliotheksruf_ist_ax (D : Deklaration) (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (L : BibliotheksFunktion D) (a : D.Ax)
    (hDient : DientBibliothek D L a) :
    (∃ (args : Args D Γ Λ (D.aparams a)),
      D.aerg a = none ∧
      (∀ t, D.aschreibt a t = true → V.schreibt t = true) ∧
      (∀ g, D.agschreibt a g = true → V.gschreibt g = true) ∧
      (∀ t, D.aschreibt a t = true → darf D t Λ) ∧
      (∀ g, D.agschreibt a g = true → gdarf D g Λ)) ↔
    (∃ (args : Args D Γ Λ L.params) (last : Expr D Γ Λ L.nutzlast),
      L.erg = none ∧
      (∀ t, L.schreibt t = true → V.schreibt t = true) ∧
      (∀ g, L.gschreibt g = true → V.gschreibt g = true) ∧
      (∀ t, L.schreibt t = true → darf D t Λ) ∧
      (∀ g, L.gschreibt g = true → gdarf D g Λ)) := by
  obtain ⟨hap, herg, hschw, hgschw⟩ := hDient
  constructor
  · rintro ⟨args, hno, hw, hg, hd, hgd⟩
    rw [hap] at args
    obtain ⟨rest, last, _⟩ := args_unsnoc D L.params L.nutzlast args
    refine ⟨rest, last, herg ▸ hno, ?_, ?_, ?_, ?_⟩
    · intro t ht
      apply hw t
      rw [hschw t]
      exact ht
    · intro g hg'
      apply hg g
      rw [hgschw g]
      exact hg'
    · intro t ht
      apply hd t
      rw [hschw t]
      exact ht
    · intro g hg'
      apply hgd g
      rw [hgschw g]
      exact hg'
  · rintro ⟨rest, last, hno, hw, hg, hd, hgd⟩
    refine ⟨hap.symm ▸ args_snoc D rest last, ?_, ?_, ?_, ?_, ?_⟩
    · rw [herg]
      exact hno
    · intro t ht
      rw [hschw t] at ht
      exact hw t ht
    · intro g hg'
      rw [hgschw g] at hg'
      exact hg g hg'
    · intro t ht
      rw [hschw t] at ht
      exact hd t ht
    · intro g hg'
      rw [hgschw g] at hg'
      exact hgd g hg'

/-! ## 3. Witness fixture: `refD`'s konto shape with one axiom

    `refD` has `Ax := Empty`, so no axiom-shaped theorem admits a `refD`
    witness. `bibD` copies the reference shape (one two-slot `konto`
    table of `.int 0 100`, one guarding lock, one writer taking `.int
    0 10` and storing the cap `100`) and adds the one axiom the library
    call needs: ordinary parameter `.int 0 10` with payload `.int 0 100`
    appended. The F-machine run below (lock, writing leaf) is the same
    two steps as `refReachBF`'s first half. -/

/-- Signature of the writer: one `.int 0 10` parameter, no result, holds
    the lock, may write the table. -/
def bibSigW : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The witness declaration: `refD`'s table, lock and writer, plus one
    axiom whose parameters are the ordinary parameter with the payload
    (`.int 0 100`) appended. -/
def bibD : Deklaration where
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
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => bibSigW
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => [.int 0 10, .int 0 100]
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => nomatch g
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e


end Gabbro.Grammatik
