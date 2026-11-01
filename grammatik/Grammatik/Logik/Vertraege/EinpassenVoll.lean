/-
  File:      Grammatik/EinpassenVoll.lean
  Subject:   EVERY VALUE IS AN ANSWER -- the decoding `einpassen` (Semantik.lean) accepts, for
             every type, exactly the values of that type (floats: the well-formed ones), so
             the answer class of an axiom or a register is empty only when its declared type
             is (round-5 finding G1, 2026-09-15).

  THE FINDING. Until 2026-09-15 `einpassen` answered `none` for EVERY raw word of a `tagged`
  sum (`.sum`), a float (`.fl`) and a function pointer (`.fnptr`). Every call of an axiom with
  such a result ended in `hardware (annahme a)`, every read of such a register in
  `hardware (register r)`, for EVERY oracle -- a stop the MODEL decided, filed as hardware.
  `KoerperGutS` does not constrain hardware outcomes, so probe A (`ensures false`) behind one
  such call met (b) and was certified. `AxVertragO` was vacuous for such axioms.

  THE DECODINGS (Semantik.lean, `einpassen`):
  * `.sum cs`  -- `summePasst`: the raw word packs the emitter's C value
                  `struct { marke; union last; }` mixed-radix, `roh = marke + |cs| * last`
                  (Euclidean `%`, `/`); a bare case carries `0`, a payload case a number in
                  its range. Inverse: `summeRoh`, `summePasst_voll`.
  * `.fl lo hi`-- `gleitWortPasst`: the word is the IEEE-754 binary64 bit pattern
                  (`0 <= roh < 2^64`, `Gleitkomma.ausBits`), held against the range like a
                  computed float (`gleitPasst`). Inverse on well-formed values: `zuBits`,
                  `gleitWortPasst_voll`; every decoded value is well-formed
                  (`gleitWortPasst_wf`).
  * `.fnptr m` -- `zeigerPasst`: the word is a code address, the loaded image
                  `Orakel.zeiger` names the function there, and its signature number is held
                  against `m`. Every function of signature `m` is the answer of some image
                  (`zeigerPasst_voll`).
  * `.never` and every other EMPTY type have no value, hence no answer: `AntwortLeer`.

  WHAT IS PROVED HERE.
  * `einpassen_voll` -- every value of every type (floats: well-formed) is the decoding of
                        some raw word under some image;
  * `einpassen_wertOk` -- every decoded value is such a value;
  * `antwortLeer_iff` -- the answer class of `τ` is empty EXACTLY when `τ` has no such value:
                        the model decides no stop beyond the declared type;
  * `antwortLeer_never`, `antwortLeer_grund0`, `antwortLeer_int_leer` -- the named empties;
    `antwortLeer_keinErg` -- an axiom without a result always answers;
  * `antwortB_iff` (round-6 finding W1) -- emptiness DECIDED from the declaration and the
    program's function list, exactly; the float case by three candidate witnesses, complete
    because the kernel IEEE order is transitive on finite values (`flt_trans_endlich`). The
    checker uses it to refuse every answer site at an empty type except an axiom `-> never`
    (`antwortenB`, Zielsatz/Akzeptiert.lean).
-/
module

public import Grammatik.Logik.Vertraege.EinpassenVoll.Teil1
public import Grammatik.Logik.Vertraege.EinpassenVoll.Teil2
