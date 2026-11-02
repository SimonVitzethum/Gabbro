module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil9

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The context of the last conjunct of `floatFiniteAddL_read_fields_align`: the facts its proof uses. -/
abbrev floatFiniteAddL_read_fields_align_boundsCase {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : ℕ) (a b : ℕ → Option (List II × ℕ)) (wa wb : Runner.W) {top K reserved : ℕ} {fp pc : Runner.W} {m : Runner.Mem} (width : F.fracBits + F.ebits < 64) (lower : FB ≤ dst + 1) (frac : F.fracBits < 64) (mask : 2 ^ F.ebits - 1 < 2 ^ 64) (fracMask : 2 ^ F.fracBits - 1 < 2 ^ 64) (hiddenBound : 2 ^ F.fracBits < 2 ^ 64) (room : top ≤ K) (sortRoom : dst + 11 < K) (alignRoom : dst + 17 ≤ K) (executed : List II) (before : Runner.Mem) (it : ℕ) (hi : floatStateSlotsL (dst + 1)
        ([a, b, fun j =>
            floatFieldL (F.fracBits + F.ebits) 1 j fun k => some ([ci 2 (↑k : ℤ) ((↑dst : ℤ) + 1) 0], k + 1), fun j =>
            floatFieldL (F.fracBits + F.ebits) 1 j fun k => some ([ci 2 (↑k : ℤ) ((↑dst : ℤ) + 2) 0], k + 1)] ++
          finiteAddRemaining F dst) =
      some (executed, it)) : Prop :=
  let values := fun i => (before.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0;
  ∀ (out : Runner.Mem),
    (∀ i < dst + 9,
        out.rd64 (slot fp (BitVec.ofNat 64 i)) =
          some
            (if
                (BitVec.slt (values (dst + 5)) (values (dst + 6)) ||
                    values (dst + 5) == values (dst + 6) && BitVec.slt (values (dst + 7)) (values (dst + 8))) =
                  true then
              if i = dst + 3 then values (dst + 4)
              else
                if i = dst + 4 then values (dst + 3)
                else
                  if i = dst + 5 then values (dst + 6)
                  else
                    if i = dst + 6 then values (dst + 5)
                    else if i = dst + 7 then values (dst + 8) else if i = dst + 8 then values (dst + 7) else values i
            else values i)) →
      (∀ i < 8,
          values (dst + 1 + i) =
            match i with
            | 0 => wa
            | 1 => wb
            | 2 => floatFieldWord wa (F.fracBits + F.ebits) 1
            | 3 => floatFieldWord wb (F.fracBits + F.ebits) 1
            | x => finiteAddRemainingValue F wa wb (i - 4)) →
        ∀ (aligned shift : List II × ℕ),
          (floatShiftJamL (dst + 16) (fun j => some ([ci 2 (↑j : ℤ) ((dst + 7 : ℕ) : ℤ) 0], j + 1)) fun j =>
                some ([ci 1 (↑j : ℤ) 1 0], j + 1)) =
              some shift →
            ∀ (rounded : List II × ℕ),
              (floatGuardRoundL (dst + 16) (fun j => wordK 6 j (some ([ci 2 (↑j : ℤ) ((dst + 7 : ℕ) : ℤ) 0], j + 1)) 8)
                    (fun j => wordK 8 j (some ([ci 2 (↑j : ℤ) ((dst + 7 : ℕ) : ℤ) 0], j + 1)) 7) fun j =>
                    some ([ci 1 (↑j : ℤ) 0 0], j + 1)) =
                  some rounded →
                ∀ (continuation : List II) (ex ey q r : Runner.W),
                  out.rd64 (slot fp (BitVec.ofNat 64 (dst + 5))) = some ex →
                    out.rd64 (slot fp (BitVec.ofNat 64 (dst + 6))) = some ey →
                      out.rd64 (slot fp (BitVec.ofNat 64 (dst + 7))) = some q →
                        out.rd64 (slot fp (BitVec.ofNat 64 (dst + 8))) = some r →
                          BitVec.toInt ey ≤ BitVec.toInt ex ∧ (ey = ex → BitVec.toInt r ≤ BitVec.toInt q) →
                            ∀ (final : Runner.Mem),
                              final.rd64 (slot fp (BitVec.ofNat 64 (dst + 16))) = some (floatShiftJamWord r (ex - ey)) →
                                Pre L final
                                    (pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                      BitVec.ofNat 64 (16 * aligned.1.length))
                                    fp K (dst + 17) continuation ρ W reserved →
                                  (∀ i < dst + 9,
                                      final.rd64 (slot fp (BitVec.ofNat 64 i)) =
                                        out.rd64 (slot fp (BitVec.ofNat 64 i))) →
                                    let vs := fun i => (final.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0;
                                    (∀ i < K, final.rd64 (slot fp (BitVec.ofNat 64 i)) = some (vs i)) →
                                      ∀ (signedOut : Runner.Mem),
                                        Runner.IR.Star
                                            {
                                              pc :=
                                                pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                  BitVec.ofNat 64 (16 * aligned.1.length),
                                              fp := fp }
                                            final
                                            {
                                              pc :=
                                                pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                    BitVec.ofNat 64 (16 * aligned.1.length) +
                                                  96,
                                              fp := fp }
                                            signedOut →
                                          Agree fp (dst + 7) K final signedOut →
                                            Runner.IR.Star { pc := pc, fp := fp } m
                                                {
                                                  pc :=
                                                    pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                      BitVec.ofNat 64 (16 * aligned.1.length),
                                                  fp := fp }
                                                final →
                                              Agree fp (dst + 1) K m final →
                                                ∀ (normalization : List II) (zeroMem : Runner.Mem),
                                                  Runner.IR.Star
                                                      {
                                                        pc :=
                                                          pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                              BitVec.ofNat 64 (16 * aligned.1.length) +
                                                            96,
                                                        fp := fp }
                                                      signedOut
                                                      {
                                                        pc :=
                                                          pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                                BitVec.ofNat 64 (16 * aligned.1.length) +
                                                              96 +
                                                            BitVec.ofNat 64 (16 * [ci 1 ((dst + 10 : ℕ) : ℤ) 0 0].length),
                                                        fp := fp }
                                                      zeroMem →
                                                    Agree fp (dst + 10) K signedOut zeroMem →
                                                      Pre L zeroMem
                                                          (pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                                BitVec.ofNat 64 (16 * aligned.1.length) +
                                                              96 +
                                                            BitVec.ofNat 64 (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length))
                                                          fp K (dst + 7)
                                                          ([ci 14 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 7)
                                                                ((↑dst : ℤ) + 10)] ++
                                                            normalization)
                                                          ρ W reserved →
                                                        zeroMem.rd64 (slot fp (BitVec.ofNat 64 (dst + 7))) =
                                                            some
                                                              (if (vs (dst + 3) == vs (dst + 4)) = true then
                                                                vs (dst + 7) + vs (dst + 16)
                                                              else vs (dst + 7) - vs (dst + 16)) →
                                                          ∀ (tested : Runner.Mem),
                                                            Runner.IR.Star
                                                                {
                                                                  pc :=
                                                                    pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                                          BitVec.ofNat 64 (16 * aligned.1.length) +
                                                                        96 +
                                                                      BitVec.ofNat 64
                                                                        (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length),
                                                                  fp := fp }
                                                                zeroMem
                                                                {
                                                                  pc :=
                                                                    pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                                            BitVec.ofNat 64 (16 * aligned.1.length) +
                                                                          96 +
                                                                        BitVec.ofNat 64
                                                                          (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length) +
                                                                      BitVec.ofNat 64
                                                                        (16 *
                                                                          [ci 14 ((dst + 9 : ℕ) : ℤ) ((dst + 7 : ℕ) : ℤ)
                                                                                ((dst + 10 : ℕ) : ℤ)].length),
                                                                  fp := fp }
                                                                tested →
                                                              Agree fp (dst + 9) K zeroMem tested →
                                                                Pre L tested
                                                                    (pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                                                            BitVec.ofNat 64 (16 * aligned.1.length) +
                                                                          96 +
                                                                        BitVec.ofNat 64
                                                                          (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length) +
                                                                      BitVec.ofNat 64
                                                                        (16 *
                                                                          [ci 14 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 7)
                                                                                ((↑dst : ℤ) + 10)].length))
                                                                    fp K (dst + 7) normalization ρ W reserved →
                                                                  (∀ i < 4,
                                                                      if i < 2 then
                                                                        1 ≤
                                                                            BitVec.toNat
                                                                              (finiteAddRemainingValue F wa wb i) ∧
                                                                          BitVec.toNat
                                                                              (finiteAddRemainingValue F wa wb i) <
                                                                            F.bexpMax
                                                                      else
                                                                        BitVec.toNat
                                                                            (finiteAddRemainingValue F wa wb i) <
                                                                          2 ^ 56) →
                                                                    ∃ ex ey,
                                                                      signedOut.rd64
                                                                            (slot fp (BitVec.ofNat 64 (dst + 5))) =
                                                                          some ex ∧
                                                                        signedOut.rd64
                                                                              (slot fp (BitVec.ofNat 64 (dst + 6))) =
                                                                            some ey ∧
                                                                          1 ≤ BitVec.toNat ex ∧
                                                                            BitVec.toNat ex < F.bexpMax ∧
                                                                              1 ≤ BitVec.toNat ey ∧
                                                                                BitVec.toNat ey < F.bexpMax ∧
                                                                                  BitVec.toNat (vs (dst + 7)) < 2 ^ 56 ∧
                                                                                    BitVec.toNat (vs (dst + 16)) <
                                                                                        2 ^ 56 ∧
                                                                                      -2 ^ 57 <
                                                                                          BitVec.toInt
                                                                                            (if
                                                                                                (vs (dst + 3) ==
                                                                                                    vs (dst + 4)) =
                                                                                                  true then
                                                                                              vs (dst + 7) +
                                                                                                vs (dst + 16)
                                                                                            else
                                                                                              vs (dst + 7) -
                                                                                                vs (dst + 16)) ∧
                                                                                        BitVec.toInt
                                                                                              (if
                                                                                                  (vs (dst + 3) ==
                                                                                                      vs (dst + 4)) =
                                                                                                    true then
                                                                                                vs (dst + 7) +
                                                                                                  vs (dst + 16)
                                                                                              else
                                                                                                vs (dst + 7) -
                                                                                                  vs (dst + 16)) <
                                                                                            2 ^ 57 ∧
                                                                                          (vs (dst + 3) = vs (dst + 4) ∨
                                                                                                ex = ey →
                                                                                              (if
                                                                                                      (vs (dst + 3) ==
                                                                                                          vs
                                                                                                            (dst + 4)) =
                                                                                                        true then
                                                                                                    vs (dst + 7) +
                                                                                                      vs (dst + 16)
                                                                                                  else
                                                                                                    vs (dst + 7) -
                                                                                                      vs (dst + 16)) ≠
                                                                                                  0 →
                                                                                                0 <
                                                                                                  BitVec.toInt
                                                                                                    (if
                                                                                                        (vs (dst + 3) ==
                                                                                                            vs
                                                                                                              (dst +
                                                                                                                4)) =
                                                                                                          true then
                                                                                                      vs (dst + 7) +
                                                                                                        vs (dst + 16)
                                                                                                    else
                                                                                                      vs (dst + 7) -
                                                                                                        vs
                                                                                                          (dst + 16))) ∧
                                                                                            (∀
                                                                                                (x y :
                                                                                                  Gleitkomma.GBits F),
                                                                                                F.dicht →
                                                                                                  F.ebits + F.fracBits +
                                                                                                        1 ≤
                                                                                                      64 →
                                                                                                    F.fracBits ≤ 52 →
                                                                                                      1 < F.bexpMax →
                                                                                                        Gleitkomma.wf F
                                                                                                            x →
                                                                                                          Gleitkomma.wf
                                                                                                              F y →
                                                                                                            x.bexp ≠
                                                                                                                F.bexpMax →
                                                                                                              y.bexp ≠
                                                                                                                  F.bexpMax →
                                                                                                                wa =
                                                                                                                    BitVec.ofNat
                                                                                                                      64
                                                                                                                      (Gleitkomma.zuBits
                                                                                                                        F
                                                                                                                        x) →
                                                                                                                  wb =
                                                                                                                      BitVec.ofNat
                                                                                                                        64
                                                                                                                        (Gleitkomma.zuBits
                                                                                                                          F
                                                                                                                          y) →
                                                                                                                    (if
                                                                                                                            (vs
                                                                                                                                  (dst +
                                                                                                                                    3) ==
                                                                                                                                vs
                                                                                                                                  (dst +
                                                                                                                                    4)) =
                                                                                                                              true then
                                                                                                                          vs
                                                                                                                              (dst +
                                                                                                                                7) +
                                                                                                                            vs
                                                                                                                              (dst +
                                                                                                                                16)
                                                                                                                        else
                                                                                                                          vs
                                                                                                                              (dst +
                                                                                                                                7) -
                                                                                                                            vs
                                                                                                                              (dst +
                                                                                                                                16)) ≠
                                                                                                                        0 →
                                                                                                                      0 <
                                                                                                                        BitVec.toInt
                                                                                                                          (if
                                                                                                                              (vs
                                                                                                                                    (dst +
                                                                                                                                      3) ==
                                                                                                                                  vs
                                                                                                                                    (dst +
                                                                                                                                      4)) =
                                                                                                                                true then
                                                                                                                            vs
                                                                                                                                (dst +
                                                                                                                                  7) +
                                                                                                                              vs
                                                                                                                                (dst +
                                                                                                                                  16)
                                                                                                                          else
                                                                                                                            vs
                                                                                                                                (dst +
                                                                                                                                  7) -
                                                                                                                              vs
                                                                                                                                (dst +
                                                                                                                                  16))) ∧
                                                                                              ∃ source,
                                                                                                final.rd64
                                                                                                      (slot fp
                                                                                                        (BitVec.ofNat 64
                                                                                                          (dst + 8))) =
                                                                                                    some source ∧
                                                                                                  let den :=
                                                                                                    ((2 ^
                                                                                                          BitVec.toNat
                                                                                                            (ex - ey) : ℕ) : ℤ);
                                                                                                  let numerator :=
                                                                                                    if
                                                                                                        (vs (dst + 3) ==
                                                                                                            vs
                                                                                                              (dst +
                                                                                                                4)) =
                                                                                                          true then
                                                                                                      ((BitVec.toNat
                                                                                                                (vs
                                                                                                                  (dst +
                                                                                                                    7)) : ℕ) : ℤ) *
                                                                                                          den +
                                                                                                        ((BitVec.toNat
                                                                                                              source : ℕ) : ℤ)
                                                                                                    else
                                                                                                      ((BitVec.toNat
                                                                                                                (vs
                                                                                                                  (dst +
                                                                                                                    7)) : ℕ) : ℤ) *
                                                                                                          den -
                                                                                                        ((BitVec.toNat
                                                                                                              source : ℕ) : ℤ);
                                                                                                  let correction :=
                                                                                                    if
                                                                                                        (vs (dst + 3) ==
                                                                                                            vs
                                                                                                              (dst +
                                                                                                                4)) =
                                                                                                          true then
                                                                                                      ((BitVec.toNat
                                                                                                              source : ℕ) : ℤ) -
                                                                                                        ((BitVec.toNat
                                                                                                                (vs
                                                                                                                  (dst +
                                                                                                                    16)) : ℕ) : ℤ) *
                                                                                                          den
                                                                                                    else
                                                                                                      ((BitVec.toNat
                                                                                                                (vs
                                                                                                                  (dst +
                                                                                                                    16)) : ℕ) : ℤ) *
                                                                                                          den -
                                                                                                        ((BitVec.toNat
                                                                                                              source : ℕ) : ℤ);
                                                                                                  numerator =
                                                                                                      BitVec.toInt
                                                                                                            (if
                                                                                                                (vs
                                                                                                                      (dst +
                                                                                                                        3) ==
                                                                                                                    vs
                                                                                                                      (dst +
                                                                                                                        4)) =
                                                                                                                  true then
                                                                                                              vs
                                                                                                                  (dst +
                                                                                                                    7) +
                                                                                                                vs
                                                                                                                  (dst +
                                                                                                                    16)
                                                                                                            else
                                                                                                              vs
                                                                                                                  (dst +
                                                                                                                    7) -
                                                                                                                vs
                                                                                                                  (dst +
                                                                                                                    16)) *
                                                                                                          den +
                                                                                                        correction ∧
                                                                                                    ((↑numerator.natAbs :
                                                                                                          ℤ) =
                                                                                                        floatSumMagnitude
                                                                                                              (numerator /
                                                                                                                den)
                                                                                                              (numerator %
                                                                                                                den) *
                                                                                                            den +
                                                                                                          if
                                                                                                              numerator /
                                                                                                                  den <
                                                                                                                0 then
                                                                                                            if
                                                                                                                numerator %
                                                                                                                    den =
                                                                                                                  0 then
                                                                                                              0
                                                                                                            else
                                                                                                              den -
                                                                                                                numerator %
                                                                                                                  den
                                                                                                          else
                                                                                                            numerator %
                                                                                                              den) ∧
                                                                                                      (numerator < 0 ↔
                                                                                                          numerator /
                                                                                                              den <
                                                                                                            0) ∧
                                                                                                        (numerator = 0 ↔
                                                                                                          numerator /
                                                                                                                den =
                                                                                                              0 ∧
                                                                                                            numerator %
                                                                                                                den =
                                                                                                              0)

end Gabbro.Stage0.Senke
