import SymmetricSubgroupAsymptotics.ScalarFourDoubleHeadJointCount
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! The two invariant/twisted coordinate budget gives a full-source B6
envelope of slope one on every actual permutation source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace ScalarFourDoubleHeadJointData
variable {Q : Type} [Group Q] [Finite Q] (D : ScalarFourDoubleHeadJointData Q)

include D in
theorem permutation_epi_card_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J Q) ≤ (1 + b) * Nat.card Q * 2 ^ b := by
  let E := GroupEpimorphism J Q
  let R := Set.range (fun phi : E => D.headed.top.comp phi.1)
  letI : Finite E := Finite.of_injective
    (fun phi : E => (phi.1 : J → Q))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  letI : Finite R := Set.finite_range _ |>.to_subtype
  let pi : E → R := fun phi => ⟨D.headed.top.comp phi.1, phi, rfl⟩
  have hfibre : ∀ theta : R, Nat.card {phi : E // pi phi = theta} ≤
      Nat.card Q * 2 ^ b := by
    intro theta
    obtain ⟨phi0, hphi0⟩ := theta.2
    have htheta : Function.Surjective theta.1 := by
      rw [← hphi0]
      exact D.headed.top_surjective.comp phi0.2
    have hsmall : 2 * binaryCharacterRank theta.1.ker ≤ b := by
      have hr := permutation_binaryCharacterRank_le_half theta.1.ker (Fin b)
      rw [Nat.card_fin] at hr
      change binaryCharacterRank theta.1.ker ≤ b / 2 at hr
      omega
    have hinj : Function.Injective
        (fun phi : {phi : E // pi phi = theta} =>
          (⟨phi.1, congrArg Subtype.val phi.2⟩ :
            {phi : E // D.headed.top.comp phi.1 = theta.1})) := by
      intro phi psi he
      apply Subtype.ext
      exact congrArg
        (fun z : {phi : E // D.headed.top.comp phi.1 = theta.1} => z.1) he
    exact (Nat.card_le_card_of_injective _ hinj).trans
      ((D.fibre_card_le theta.1 htheta).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hsmall)))
  have hcount := natCard_le_mul_of_fibre pi (Nat.card Q * 2 ^ b) hfibre
  have hR : Nat.card R ≤ binaryCharacterRank (commutator J) :=
    D.headed.realisedTops_card_le
  have hr : binaryCharacterRank (commutator J) ≤ b := by
    have hh := permutation_binaryCharacterRank_le_half (commutator J) (Fin b)
    rw [Nat.card_fin] at hh
    change binaryCharacterRank (commutator J) ≤ b / 2 at hh
    omega
  calc Nat.card E ≤ Nat.card R * (Nat.card Q * 2 ^ b) := hcount
    _ ≤ (1 + b) * (Nat.card Q * 2 ^ b) :=
      Nat.mul_le_mul_right _ (hR.trans (hr.trans (by omega)))
    _ = (1 + b) * Nat.card Q * 2 ^ b := by ring

/-- A literal actual-target structure supplies the B6 full-source branch;
no owner table, final-bound input, or extra published theorem is assumed. -/
def b6Certificate : PreE7B6QuotientCertificate Q :=
  .fullSource (Nat.card Q) 1 (Nat.cast_nonneg _) (by norm_num) (by
    intro b J
    have hn := D.permutation_epi_card_le J
    have hc : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        ((1 + b) * Nat.card Q * 2 ^ b : ℕ) := by exact_mod_cast hn
    calc (Nat.card (GroupEpimorphism J Q) : ℝ)
        ≤ ((1 + b) * Nat.card Q * 2 ^ b : ℕ) := hc
      _ = (Nat.card Q : ℝ) * (1 + b) * (2 : ℝ) ^ ((1 : ℝ) * b) := by
        push_cast
        rw [one_mul, Real.rpow_natCast]
        ring)

end ScalarFourDoubleHeadJointData
end SymmetricSubgroupAsymptotics
end
