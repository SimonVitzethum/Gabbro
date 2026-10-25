import Grammatik.Zielsatz.Einbettung.Uebertragung
import Grammatik.Zielsatz.Projekte.Ohne

/-!
  File:      Grammatik/Zielsatz/Einbettung/Zeuge.lean
  Subject:   **The witness of the embedding theorem**: a library with its own table, linked into a
             program that has a table and a function of its own.

  The library `libD`: one table of four slots (`int 0 10`), one function that writes slot `0`
  and returns. The program `appD`: the library's table and function (the images, `true`) and its
  own table and function (`false`), with the signature numbers of the library at the even
  numbers. The embedding `E` is not onto: the program's own table and function have no
  preimage (`zeuge_fremd`). The library's obligation is decided by the checker
  (`logikPflicht_ohne`, no contracts); `logikPflicht_E` carries it, unchanged, to the program's
  image function (`einbettung_zeuge`).
-/

namespace Gabbro.Grammatik.Einbettung.Zeuge

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Einbettung

/-- The library's signature: no parameters, no result, writes its table. -/
def libSig : Signatur Unit Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

@[reducible] def libD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
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
  sigNr := fun _ => libSig
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
  geteilt_bewacht := fun _ h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The library's signature in the program: it writes the image table. -/
def libSigA : Signatur Bool Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => t
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

/-- The program's own function: writes every table. -/
def appSig : Signatur Bool Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

@[reducible] def appD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
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
  Fn := Bool
  sig := fun b => if b then 0 else 1
  sigNr := fun n => if n % 2 = 0 then libSigA else appSig
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
  geteilt_bewacht := fun _ h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- **The embedding**: the library's table and function to `true`, numbers to the even ones. -/
def E : Einbettung libD appD where
  num := fun n => 2 * n
  num_inj := fun a b h => by omega
  tnum := fun n => 2 * n
  tnum_inj := fun a b h => by omega
  tab := fun _ => true
  tabZ := fun b => if b then some () else none
  tabZ_tab := fun _ => rfl
  tab_tabZ := fun t' _ h => by cases t' <;> simp_all
  feld := fun _ _ => ()
  feldZ := fun _ _ => ()
  feldZ_feld := fun _ _ => rfl
  feld_feldZ := fun _ _ => rfl
  count := fun _ => rfl
  offen := fun _ => rfl
  typ := fun _ _ => rfl
  erlaubt := fun _ _ => rfl
  geteilt := fun _ => rfl
  geist := fun _ => rfl
  glob := fun e => nomatch e
  globZ := fun e => nomatch e
  globZ_glob := fun e => nomatch e
  glob_globZ := fun e => nomatch e
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  ggeist := fun e => nomatch e
  lock := fun e => nomatch e
  lockZ := fun e => nomatch e
  lockZ_lock := fun e => nomatch e
  lock_lockZ := fun e => nomatch e
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  marke := fun e => nomatch e
  markeZ := fun e => nomatch e
  markeZ_marke := fun e => nomatch e
  marke_markeZ := fun e => nomatch e
  stufen := fun e => nomatch e
  braucht := fun _ => rfl
  gbraucht := fun e => nomatch e
  eigner := fun _ => rfl
  fn := fun _ => true
  fnZ := fun b => if b then some () else none
  fnZ_fn := fun _ => rfl
  fn_fnZ := fun f' _ h => by cases f' <;> simp_all
  inv := fun e => nomatch e
  invZ := fun e => nomatch e
  invZ_inv := fun e => nomatch e
  inv_invZ := fun e => nomatch e
  traeger := fun e => nomatch e
  invs := fun e => nomatch e
  ax := fun e => nomatch e
  axZ := fun e => nomatch e
  axZ_ax := fun e => nomatch e
  ax_axZ := fun e => nomatch e
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  agruende := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  anbieter := fun _ => rfl
  reg := fun e => nomatch e
  regZ := fun e => nomatch e
  regZ_reg := fun e => nomatch e
  reg_regZ := fun e => nomatch e
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rtraeger := fun e => nomatch e
  annahme := fun _ => ()
  a10 := rfl
  tabNr := fun _ => rfl
  sig := fun _ => rfl
  passt := fun _ n => by
    show decide ((0 : Nat) = 2 * n) = decide (0 = n)
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

theorem hS : E.SigTreu where
  sigNr := fun n => by
    show (if 2 * n % 2 = 0 then libSigA else appSig) = _
    rw [if_pos (by omega)]
    simp only [libSigA, Einbettung.sigE, libSig]
    congr 1
    · funext t'; cases t' <;> rfl
    · funext g; exact nomatch g
  rzusage := fun r => nomatch r

/-- The library body: write `7` to slot `0`, return. -/
def libBody : Endblock libD (vertragVon libD ()) false (libD.params ()) (Signatur.anfang libD (libD.signatur ())) :=
  .cons (.assignSlot () () (.widen (by decide) (by decide) (.lit 0)) (.widen (by decide) (by decide) (.lit 7))
    rfl (fun _ h => by cases h)) (.ret .empty (List.Perm.refl _))

def libP : Programm libD where
  invariante := fun e => nomatch e
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => libBody

/-- The program's own body. -/
def appBody : Endblock appD (vertragVon appD false) false (appD.params false)
    (Signatur.anfang appD (appD.signatur false)) :=
  .ret .empty (List.Perm.refl _)

/-- **The linking program**: the image of the library at `true`, its own body at `false`. -/
def appP : Programm appD where
  invariante := fun e => nomatch e
  requires := fun b => match b with
    | true => Einbettung.requiresE hS libP ()
    | false => .tru
  ensures := fun b => match b with
    | true => Einbettung.ensuresE hS libP ()
    | false => .tru
  rumpf := fun b => match b with
    | true => Einbettung.rumpfE hS libP ()
    | false => appBody

theorem hZ : ZeigerfreiD libD where
  typ := fun _ _ => rfl
  gtyp := fun g => nomatch g
  erg := fun _ _ h => by cases h
  aerg := fun a => nomatch a
  rtyp := fun r => nomatch r
  params := fun _ _ h => by cases h

theorem hU : E.Uebernahme hZ hS libP (SperrInv.leer libD) (axWahr libD) (fun _ => False)
    appP (SperrInv.leer appD) (axWahr appD) (fun _ => False) where
  fort := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, (fun i => nomatch i), fun _ => rfl⟩
  orte := fun L => nomatch L
  inv := fun L => nomatch L
  atom := fun _ h => h
  ax := fun a => nomatch a
  invBild := fun i => nomatch i

theorem hL : LogikPflichtA libP (SperrInv.leer libD) (axWahr libD) (fun _ => False) :=
  logikPflichtA_of_frei (fun _ _ _ h => h)
    (logikPflicht_ohne (fs := [()]) (fun _ => List.mem_singleton.mpr rfl) (fun _ => rfl) (fun _ => rfl)
      rfl (by decide))

/-- The program's own table and function have no preimage: the embedding is not onto. -/
theorem zeuge_fremd : E.tabZ false = none ∧ E.fnZ false = none ∧ libD.schreibt () () = true :=
  ⟨rfl, rfl, rfl⟩

/-- **The witness**: the library's decided obligation holds at the program's image function,
    for every budget, with nothing proved anew. -/
theorem einbettung_zeuge (passes : Nat) :
    KoerperGutSA appP passes (axWahr appD) (SperrInv.leer appD) (fun _ => False) true ∧
      InvGutSA appP passes (axWahr appD) (SperrInv.leer appD) (fun _ => False) true ∧
      InvGutGrundA appP passes (axWahr appD) (SperrInv.leer appD) (fun _ => False) true :=
  E.logikPflicht_E hZ hS hU (Einbettung.padOk_tab (D := libD) ()) hL passes ()

#print axioms einbettung_zeuge

end Gabbro.Grammatik.Einbettung.Zeuge
