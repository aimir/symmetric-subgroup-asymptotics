import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPenultimateWeyl
import SymmetricSubgroupAsymptotics.CyclicFourInvolutionIntersection

/-! The SAME actual inner length-seven element normalizes the ambient
middle C4, hence fixes y². This identifies the actual opposed square.
No arbitrary automorphism of Tits is applied to y or the ambient C4. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareOpposition
open CFSGReeFFourBinaryPenultimateWeyl CFSGReeFFourPenultimateMiddleIntersection
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourReducedPositiveIntersection
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourBinaryMiddleGenerators
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedAmbientHom

private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private theorem opposed_conjugate {G : Type*} [Group G] (a b x : G)
    (ha : a^2=1) (he : (a*b)*x*(a*b)⁻¹=x) :
    a*x*a⁻¹=b*x*b⁻¹ := by
  have hi : a⁻¹=a := inv_eq_of_mul_eq_one_right ((pow_two a).symm.trans ha)
  have hh := congrArg (fun z : G => a⁻¹*z*a) he
  have hh' : b*x*b⁻¹=a⁻¹*x*a := by
    simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,inv_mul_cancel_left,mul_one,one_mul] using hh
  simpa only [hi] using hh'.symm

theorem binary_penultimate_normalizes_middle :
    shortModelWord 0 (13 : Fin 16)∈
      Subgroup.normalizer (middleFixedSubgroup 0 : Set (originalModelFixed 0)) := by
  have h := CyclicFourInvolutionIntersection.normalizes_intersection
    (fixedPositive 0) (shortModelWord 0 (13 : Fin 16)) binary_short_thirteen_square
  have hi : fixedPositive 0⊓(fixedPositive 0).comap
      (MulAut.conj (shortModelWord 0 (13 : Fin 16))).toMonoidHom=middleFixedSubgroup 0 :=
    penultimate_intersection_eq_middle 0
  change shortModelWord 0 (13 : Fin 16)∈Subgroup.normalizer
    ((fixedPositive 0⊓(fixedPositive 0).comap
      (MulAut.conj (shortModelWord 0 (13 : Fin 16))).toMonoidHom :
        Subgroup (originalModelFixed 0)) : Set (originalModelFixed 0)) at h
  have hN := congrArg (fun S : Subgroup (originalModelFixed 0) =>
    Subgroup.normalizer (S : Set (originalModelFixed 0))) hi
  exact Eq.mp (congrArg (fun Q : Subgroup (originalModelFixed 0) =>
    shortModelWord 0 (13 : Fin 16)∈Q) hN) h

theorem binary_penultimate_fixes_middle_square :
    shortModelWord 0 (13 : Fin 16)*(fourCycle 0)^2*
      (shortModelWord 0 (13 : Fin 16))⁻¹=(fourCycle 0)^2 := by
  have hn : shortModelWord 0 (13 : Fin 16)∈
      Subgroup.normalizer (Subgroup.zpowers (fourCycle 0) : Set (originalModelFixed 0)) := by
    rw [←middleFixed_zero_eq_zpowers]
    exact binary_penultimate_normalizes_middle
  exact CyclicFourInvolutionIntersection.square_fixed_of_normalizes
    (fourCycle 0) (shortModelWord 0 (13 : Fin 16)) (fourCycle_order_four 0) hn

theorem binary_opposition_middle_square :
    oppositionFixed 0*(fourCycle 0)^2*(oppositionFixed 0)⁻¹=
      middleFixedWeyl 0*(fourCycle 0)^2*(middleFixedWeyl 0)⁻¹ := by
  have he := binary_penultimate_fixes_middle_square
  rw [binary_short_thirteen_eq] at he
  exact opposed_conjugate (oppositionFixed 0) (middleFixedWeyl 0) ((fourCycle 0)^2)
    binary_opposition_square he

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareOpposition
