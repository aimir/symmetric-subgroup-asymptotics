import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusFirstLayer
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralCommutators
import SymmetricSubgroupAsymptotics.CFSGCentralExtensionScalarRigidity
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoNormOneWeight

/-! The intrinsic first-layer action is faithful on the ACTUAL rank-two
torus normalizer in Aut(R). Its kernel fixes the centre by commutators,
centralizes the torus, and is killed by one norm-one scalar different
from one. No unital automorphism theorem or full-SU premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGTwistedA2DiagonalTorus
open CFSGFiniteFieldScalarNormalizer

private theorem representation_conjugate_eq_of_kernel {A B : Type*} [Group A] [Group B]
    (rho : A →* B) (f t : A) (hf : rho f = 1) : rho (f * t * f⁻¹) = rho t := by
  simp only [map_mul, map_inv, hf, one_mul, inv_one, mul_one]

theorem rankTwoRadicalTorusAut_eq_one_of_first (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ)
    (hz : rankTwoFirstLayerAutHom q (rankTwoRadicalTorusAutHom q z) = 1) :
    rankTwoRadicalTorusAutHom q z = 1 := by
  rw [rankTwoFirstLayer_torus] at hz
  have hunit : rankTwoFirstWeightHom q (rankTwoSigmaUnits q z) = 1 :=
    scalarHom_injective (q.Extension 2) (hz.trans (scalarHom (q.Extension 2)).map_one.symm)
  have hs : definingFieldAutomorphism q 2
      (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2)) = 1 := by
    rw [← rankTwoFirstWeight_sigma]
    exact congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hunit
  have hw : firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2) = 1 :=
    (definingFieldAutomorphism q 2).injective (hs.trans (map_one _).symm)
  have hpow : (z : q.Extension 2) ^ 2 = definingFieldAutomorphism q 2 z :=
    (div_eq_one_iff_eq ((map_ne_zero _).mpr (Units.ne_zero z))).mp hw
  have hzk : z ∈ (rankTwoFirstWeightHom q).ker := by
    apply Units.ext
    exact (rankTwoFirstWeightHom_val q z).trans hw
  have hcube : z ^ 3 = 1 := CFSGInvolutiveScalarWeights.kernel_cube
    (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x) z hzk
  have hnorm : (z : q.Extension 2) * definingFieldAutomorphism q 2 z = 1 := by
    rw [← hpow]
    have hc := congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hcube
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, mul_comm] using hc
  have hmid : definingFieldAutomorphism q 2 (z : q.Extension 2) / (z : q.Extension 2) = z := by
    rw [← hpow]
    field_simp [Units.ne_zero z]
  have hlast : (definingFieldAutomorphism q 2 (z : q.Extension 2))⁻¹ = z := by
    have hsz : definingFieldAutomorphism q 2 (z : q.Extension 2) ≠ 0 :=
      (map_ne_zero (definingFieldAutomorphism q 2)).mpr (Units.ne_zero z)
    apply mul_left_cancel₀ hsz
    calc
      _ = 1 := mul_inv_cancel₀ hsz
      _ = (z : q.Extension 2) * definingFieldAutomorphism q 2 z := hnorm.symm
      _ = _ := mul_comm _ _
  have hscalar : ((rankTwoNaturalTorus q z).val.val : Mat (q.Extension 2) 2) =
      (z : q.Extension 2) • (1 : Mat (q.Extension 2) 2) := by
    have hweights : torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2) =
        fun _ => (z : q.Extension 2) := by
      funext i
      fin_cases i
      · rfl
      · exact hmid
      · exact hlast
    rw [rankTwoNaturalTorus_matrix, hweights]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp only [mul_one, mul_zero]
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change ((rankTwoNaturalTorus q z).val.val : Mat (q.Extension 2) 2) *
      (g.val.val.val : Mat (q.Extension 2) 2) *
      (((rankTwoNaturalTorus q z).val.val⁻¹ : (Mat (q.Extension 2) 2)ˣ) : Mat (q.Extension 2) 2) =
      (g.val.val.val : Mat (q.Extension 2) 2)
  have hcomm : ((rankTwoNaturalTorus q z).val.val : Mat (q.Extension 2) 2) *
      (g.val.val.val : Mat (q.Extension 2) 2) =
      (g.val.val.val : Mat (q.Extension 2) 2) *
        ((rankTwoNaturalTorus q z).val.val : Mat (q.Extension 2) 2) := by
    rw [hscalar, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hcomm, mul_assoc, Units.mul_inv, mul_one]

theorem rankTwoFirstLayer_injective_on_torus (q : CFSG.PrimePower)
    {f g : MulAut (fixedRadical q 0)}
    (hf : f ∈ (rankTwoRadicalTorusAutHom q).range)
    (hg : g ∈ (rankTwoRadicalTorusAutHom q).range)
    (he : rankTwoFirstLayerAutHom q f = rankTwoFirstLayerAutHom q g) : f = g := by
  obtain ⟨z, hz⟩ := (rankTwoRadicalTorusAutHom q).range.mul_mem hf
    ((rankTwoRadicalTorusAutHom q).range.inv_mem hg)
  have hzfirst : rankTwoFirstLayerAutHom q (rankTwoRadicalTorusAutHom q z) = 1 := by
    rw [hz, map_mul, map_inv, he, mul_inv_cancel]
  have hz0 := rankTwoRadicalTorusAut_eq_one_of_first q z hzfirst
  exact mul_inv_eq_one.mp (hz.symm.trans hz0)

theorem rankTwo_normalizer_first_kernel (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (fixedRadical q 0))
    (hf : f ∈ Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0))))
    (hfirst : rankTwoFirstLayerAutHom q f = 1) : f = 1 := by
  have hcentral (z : (q.Extension 2)ˣ) :
      f * rankTwoRadicalTorusAutHom q z * f⁻¹ = rankTwoRadicalTorusAutHom q z := by
    have hz : f * rankTwoRadicalTorusAutHom q z * f⁻¹ ∈ (rankTwoRadicalTorusAutHom q).range :=
      (Subgroup.mem_normalizer_iff.mp hf _).mp ⟨z, rfl⟩
    apply rankTwoFirstLayer_injective_on_torus q hz ⟨z, rfl⟩
    exact representation_conjugate_eq_of_kernel (rankTwoFirstLayerAutHom q) f
      (rankTwoRadicalTorusAutHom q z) hfirst
  have hcomm (z : (q.Extension 2)ˣ) (g : fixedRadical q 0) :
      f (rankTwoRadicalTorusAut q z g) = rankTwoRadicalTorusAut q z (f g) := by
    have he := congrArg (fun A : MulAut (fixedRadical q 0) => A (f g)) (hcentral z)
    change f (rankTwoRadicalTorusAut q z (f.symm (f g))) = rankTwoRadicalTorusAut q z (f g) at he
    rw [f.symm_apply_apply] at he
    exact he
  have hfix (g : fixedRadical q 0) : rankTwoParameterHom q (f g) = rankTwoParameterHom q g := by
    exact congrArg (fun a : Multiplicative (Fin 1 → q.Extension 2) =>
      Multiplicative.ofAdd (a.toAdd 0)) (rankTwo_vector_fixed_of_firstLayer_eq_one q f hfirst g)
  have hfixC (c : fixedRadical q 0) (hc : c ∈ (rankTwoParameterHom q).ker) : f c = c := by
    rw [rankTwoParameterHom_ker] at hc
    obtain ⟨a, rfl⟩ := exists_centralRadical_of_parameter_one q 0 c hc
    exact rankTwo_firstLayer_kernel_fixes_centre q f hfirst a
  obtain ⟨z, hz, hweight⟩ := exists_norm_one_nontrivial_first_weight q hq
  have htC (c : fixedRadical q 0) (hc : c ∈ (rankTwoParameterHom q).ker) :
      rankTwoRadicalTorusAut q z c = c := by
    rw [rankTwoParameterHom_ker] at hc
    obtain ⟨a, rfl⟩ := exists_centralRadical_of_parameter_one q 0 c hc
    exact rankTwoRadicalTorusAut_centre_of_norm_one q z hz a
  have hk : definingFieldAutomorphism q 2
      (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z) ≠ 1 := by
    intro he
    exact hweight ((definingFieldAutomorphism q 2).injective (he.trans (map_one _).symm))
  have hend := CFSGCentralExtensionScalarRigidity.endomorphism_eq_id
    (rankTwoParameterHom q) (rankTwoParameterHom_surjective q)
    (le_of_eq (rankTwoParameterHom_ker_eq_center q)) f.toMonoidHom hfix hfixC
    (rankTwoRadicalTorusAut q z) htC (hcomm z)
    (definingFieldAutomorphism q 2 (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z))
    hk (rankTwoRadicalTorusAut_first q z)
  apply MulEquiv.ext
  intro g
  exact congrArg (fun a : fixedRadical q 0 →* fixedRadical q 0 => a g) hend

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
