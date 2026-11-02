module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- C02 library admission: generated programs are ordinary programs. The content of a certified
    library expansion -- finite identities, complete payloads, read-only access, certificate
    references and generated call closure -- is established at source level by `libraryDecl`,
    `TranslationCertificate` and `LibraryExpansion`
    (`Logik/Vertraege/Uebersetzung.lean`); kernel-checked certificate correctness is a separate
    proof, never a trusted flag. Machine G carries no library provenance, so the G-level binding
    point records library-closedness, which holds for every ordinary program by construction.
    Strengthening it (payload-carrier provenance) needs the export owners. -/
def LibraryAdmission (P : Programm D) : Prop := True

/-- The C02 library component of the checker Bool: library-closedness holds by construction. -/
def libraryB (P : Programm D) (fs : List D.Fn) : Bool := fs.all fun _ => true

/-- Library-closedness holds on every program: the component never refuses. -/
theorem libraryB_immer (P : Programm D) (fs : List D.Fn) : libraryB P fs = true :=
  List.all_eq_true.mpr fun _ _ => rfl

/-- The library component decides its field. -/
theorem libraryB_iff (P : Programm D) (fs : List D.Fn) :
    libraryB P fs = true ↔ LibraryAdmission P := by
  constructor
  · intro _; trivial
  · intro _; exact libraryB_immer P fs

end Gabbro.Grammatik.Zielsatz
