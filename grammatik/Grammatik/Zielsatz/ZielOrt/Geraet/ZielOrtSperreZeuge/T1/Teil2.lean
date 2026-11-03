module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- The declaration of the two-writer witness. -/
def sD : Deklaration where
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
  Fn := SFn
  sig := fun | .setze => 0 | .haupt => 1
  sigNr := fun | 0 => sSigSetze | _ => sSigHaupt
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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

def sSetze : sD.Fn := SFn.setze
def sHaupt : sD.Fn := SFn.haupt

abbrev sL : List (Res sD) := [Res.held (D := sD) ()]

theorem sDarf : darf sD () sL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

def sIdx0 {Γ : Ctx} {Λ : List (Res sD)} : Expr sD Γ Λ (.index (sD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

def sIdx1 {Γ : Ctx} {Λ : List (Res sD)} : Expr sD Γ Λ (.index (sD.count ())) :=
  .widen (by decide) (by decide) (.lit 1)

/-- `konto[0] == konto[1]`, at the holdings `sL`. -/
def sGleich {Γ : Ctx} : Expr sD Γ sL .bool :=
  .eq (.slot () () sIdx0 sDarf) (.slot () () sIdx1 sDarf)

/-- `setze` requires `konto[0] == konto[1]`. -/
def sReqSetze : Expr sD (sD.params sSetze) (Signatur.anfang sD (sD.signatur sSetze)) .bool :=
  sGleich

/-- `setze` ensures `konto[0] == konto[1] && konto[0] == x`. -/
def sEnsSetze : Expr sD (ErgCtx (sD.params sSetze) (sD.erg sSetze)) (vertragVon sD sSetze).ende .bool :=
  .and sGleich (.eq (.slot () () sIdx0 sDarf) (.var .here))

/-- `setze(x)`: `konto[0] = x; konto[1] = x; return`. -/
def sRumpfSetze : Endblock sD (vertragVon sD sSetze) false [.int 0 100] sL :=
  .cons (.assignSlot () () sIdx0 (.var .here) rfl sDarf)
    (.cons (.assignSlot () () sIdx1 (.var .here) rfl sDarf) (.ret .empty (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig]))))


end Gabbro.Grammatik
