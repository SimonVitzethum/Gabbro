module

public import Grammatik.Zielsatz.Atomar.AtomarInvarianten
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Logik.Terminierung.Mass
public import Grammatik.Logik.Terminierung.LaufGX
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Logik.Terminierung.Rekursion.Teil1
public import Grammatik.Logik.Terminierung.Rekursion.Teil1a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Lauf
variable {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (m : Mass D)
  (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

/-- **T4 from the goal's premises**: `rekursion_endlich` with the replay supplied by `zielInvSA_erreichbarGX`, the
    user's measure duty `MassPflicht` for every function in place of the empty one the goal uses. -/
theorem rekursion_endlich_aus (Q : AxEns D) (S : SperrInv D) (K : Faden → D.Fn → Bool)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P pa Q S Tg f) (hM : ∀ f, MassPflicht P pa Q S Tg m zyk f)
    (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hR : ∀ f, rufeE (tor zyk rk f) (torS zyk rk fs f) true (P.rumpf f) = true)
    (hL : ∀ f g, zyk f g = true → (m f).length = (m g).length)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    ∃ N, ∀ j, N ≤ j → R.akt j ≠ some t :=
  rekursion_endlich m zyk rk fs Q S lok hvoll hTA hR hL sp init
    (fun M hr => (zielInvSA_erreichbarGX P O pa Q S K Tg lok sp init hO hRL hQ hlok hS hvoll hAbg hWurzel
      hTA hTV hTS hTO hFragS hFS hlokK hK hM hStart hsp hex M hr).1) R h0 t

end Lauf

end Gabbro.Grammatik
