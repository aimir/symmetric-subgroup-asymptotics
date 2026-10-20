import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! The zero-twisted quotient branch: two actual binary coordinates and
one actual ternary coordinate. The published KP input is the existing
abelianization theorem, exposed explicitly; no project source bound is an
input. Binary and ternary labels are counted jointly before the square. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace BinaryTwoTernaryAbelianB6Envelope

variable {Q : Type} [Group Q] [Finite Q]
  (binary : Fin 2 → (Q →* Multiplicative (ZMod 2)))
  (ternary : Q →* Multiplicative (ZMod 3))
  (joint : Function.Injective (fun q => ((binary 0 q, ternary q), binary 1 q)))

include binary ternary joint in
omit [Finite Q] in
theorem epi_card_le_abelianization_square {J : Type} [Group J] [Finite J] :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (Abelianization J) * Nat.card (Abelianization J) := by
  let label : GroupEpimorphism J Q →
      (PrimeCharacters 2 J × PrimeCharacters 3 J) × PrimeCharacters 2 J :=
    fun f => ((AddMonoidHom.toMultiplicativeRight.symm ((binary 0).comp f.1),
      AddMonoidHom.toMultiplicativeRight.symm (ternary.comp f.1)),
      AddMonoidHom.toMultiplicativeRight.symm ((binary 1).comp f.1))
  have hinj : Function.Injective label := by
    intro f g he
    apply Subtype.ext
    ext x
    apply joint
    have h20 := DFunLike.congr_fun (congrArg (fun z => z.1.1) he) (Additive.ofMul x)
    have h3 := DFunLike.congr_fun (congrArg (fun z => z.1.2) he) (Additive.ofMul x)
    have h21 := DFunLike.congr_fun (congrArg (fun z => z.2) he) (Additive.ofMul x)
    exact Prod.ext
      (Prod.ext (Multiplicative.toAdd.injective h20) (Multiplicative.toAdd.injective h3))
      (Multiplicative.toAdd.injective h21)
  have h2 : Nat.card (PrimeCharacters 2 J) ≤ Nat.card (Abelianization J) :=
    addMonoidHom_zmod_card_le_abelianization J 2
  calc Nat.card (GroupEpimorphism J Q) ≤
        Nat.card ((PrimeCharacters 2 J × PrimeCharacters 3 J) × PrimeCharacters 2 J) :=
      Nat.card_le_card_of_injective label hinj
    _ = (Nat.card (PrimeCharacters 2 J) * Nat.card (PrimeCharacters 3 J)) *
        Nat.card (PrimeCharacters 2 J) := by rw [Nat.card_prod, Nat.card_prod]
    _ ≤ Nat.card (Abelianization J) * Nat.card (Abelianization J) :=
      Nat.mul_le_mul (primeCharacters_two_mul_three_le_abelianization J) h2

include binary ternary joint in
omit [Finite Q] in
theorem permutation_envelope (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ (2 : ℝ) ^ ((4 / 3 : ℝ) * b) := by
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hbase : (3 : ℝ) ^ ((b : ℝ) / 3) ≤ (2 : ℝ) ^ (2 * ((b : ℝ) / 3)) := by
    calc (3 : ℝ) ^ ((b : ℝ) / 3) ≤ (4 : ℝ) ^ ((b : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ (2 * ((b : ℝ) / 3)) := by
        rw [Real.rpow_mul (by norm_num)]
        norm_num
  have hA := (hKP b J).trans hbase
  have hn := epi_card_le_abelianization_square binary ternary joint (J := J)
  have hc : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Abelianization J) : ℝ) * Nat.card (Abelianization J) := by
    exact_mod_cast hn
  calc (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (Abelianization J) : ℝ) * Nat.card (Abelianization J) := hc
    _ ≤ (2 : ℝ) ^ (2 * ((b : ℝ) / 3)) * (2 : ℝ) ^ (2 * ((b : ℝ) / 3)) :=
      mul_le_mul hA hA (Nat.cast_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ ((4 / 3 : ℝ) * b) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring

def b6Certificate (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6QuotientCertificate Q :=
  .fullSource 1 (4 / 3) (by norm_num) le_rfl (by
    intro b J
    simpa only [one_mul] using
      (permutation_envelope binary ternary joint hKP b J).trans
        (le_mul_of_one_le_left (by positivity : 0 ≤ (2 : ℝ) ^ ((4 / 3 : ℝ) * b))
          (by exact le_add_of_nonneg_right (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ)) :
            (1 : ℝ) ≤ 1 + b)))

end BinaryTwoTernaryAbelianB6Envelope
end SymmetricSubgroupAsymptotics
end
