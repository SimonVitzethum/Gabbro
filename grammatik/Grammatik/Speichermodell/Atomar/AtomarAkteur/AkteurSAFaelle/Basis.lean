module

public import Grammatik.Speichermodell.Atomar.AtomarReplay

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

end Akteur
end Gabbro.Grammatik
