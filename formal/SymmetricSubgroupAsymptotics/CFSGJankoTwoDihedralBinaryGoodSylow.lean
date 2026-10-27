import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryMatrixEquality
import SymmetricSubgroupAsymptotics.CFSGJankoTwoActualHeisenbergFrame
import SymmetricSubgroupAsymptotics.InvertingBinaryCyclicJoin
import Mathlib.Tactic.FinCases

/-! Original ATLAS-five-relator J2, with inherited simplicity only. The
new finite matrix equality recovers the ORIGINAL second generator in the
join of two explicitly binary dihedral subgroups. No model identification,
whole-group order, ordinary-generation label or extra public premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoDihedralBinaryGoodSylow
open CFSGReduction CFSGJankoTwoBinaryRecoveryWords
open CFSGJankoTwoSelectedMatrixIdentities
open CFSGJankoTwoActualHeisenbergFrame
abbrev G := CFSG.Models.Presentations.J2.Model
private def a : G := PresentedGroup.of (0 : Fin 2)
private def b : G := PresentedGroup.of (1 : Fin 2)
private theorem image_a : rho a=unitA := rho_first
private theorem image_b : rho b=unitB := rho_second

theorem goodSylowPrime (hCFSG : CFSG.CFSGClassification)
    [Finite G] [IsSimpleGroup G] : GoodSylowPrime G 2 := by
  have ha : a^2=1 := by
    apply rho_injective
    rw [map_pow,map_one,image_a]
    exact unitA_square
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hAi : unitA⁻¹=unitA := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using unitA_square)
  have hb : b^3=1 := by
    apply rho_injective
    rw [map_pow,map_one,image_b]
    exact unitB_cube
  have hbi : b⁻¹=b*b := inv_eq_of_mul_eq_one_right (by
    calc
      b*(b*b)=b^3 := by simp only [pow_succ,pow_zero]; group
      _=1 := hb)
  let t : G := b⁻¹*a*b
  let r : G := a*t
  let z : G := r^3
  let v : G := b⁻¹*z*b
  have ht : t^2=1 := by
    calc
      t^2=b⁻¹*a^2*b := by dsimp [t]; simp only [pow_two]; group
      _=1 := by rw [ha,mul_one,inv_mul_cancel]
  have hr : r^12=1 := by
    apply rho_injective
    dsimp [r,t]
    simp only [map_pow,map_mul,map_inv,map_one,image_a,image_b]
    simpa only [CFSG.Models.commWord,hAi,mul_assoc] using commutator_twelfth
  let U : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers z
  let V : Subgroup G := U.map (MulAut.conj b⁻¹).toMonoidHom
  have hU : IsPGroup 2 U := InvertingBinaryCyclicJoin.involution_rotation_binary a t ha ht hr
  have hV : IsPGroup 2 V := hU.map (MulAut.conj b⁻¹).toMonoidHom
  let J : Subgroup G := U ⊔ V
  have hma : a∈J := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hmz : z∈J := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hmt : t∈J := by
    apply Subgroup.mem_sup_right
    refine ⟨a,Subgroup.mem_sup_left (Subgroup.mem_zpowers a),?_⟩
    change b⁻¹*a*(b⁻¹)⁻¹=t
    rw [inv_inv]
  have hmv : v∈J := by
    apply Subgroup.mem_sup_right
    refine ⟨z,Subgroup.mem_sup_right (Subgroup.mem_zpowers z),?_⟩
    change b⁻¹*z*(b⁻¹)⁻¹=v
    rw [inv_inv]
  have hn5 : node005 a b=t := by
    change (b*b*a)*b=b⁻¹*a*b
    rw [hbi]
  have hn8 : node008 a b=z := by
    change (a*(b*b*a*b))*(a*(b*b*a*b))*(a*(b*b*a*b))=r^3
    simp only [r,t,hbi,pow_succ,pow_zero,one_mul]
  have hn10 : node010 a b=z^3 := by
    change (node008 a b*node008 a b)*node008 a b=z^3
    rw [hn8]
    simp only [pow_succ,pow_zero,one_mul]
  have hn12 : node012 a b=v := by
    change (b*b*node008 a b)*b=v
    rw [hn8]
    simp only [v,hbi]
  have hn14 : node014 a b=v^3 := by
    change (node012 a b*node012 a b)*node012 a b=v^3
    rw [hn12]
    simp only [pow_succ,pow_zero,one_mul]
  have hm5 : node005 a b∈J := hn5.symm ▸ hmt
  have hm8 : node008 a b∈J := hn8.symm ▸ hmz
  have hm10 : node010 a b∈J := hn10.symm ▸ J.pow_mem hmz 3
  have hm12 : node012 a b∈J := hn12.symm ▸ hmv
  have hm14 : node014 a b∈J := hn14.symm ▸ J.pow_mem hmv 3
  have hrecovery : node034 a b=b := by
    apply rho_injective
    rw [map_node034,image_a,image_b]
    apply Units.ext
    exact (map_node034 (Units.coeHom M) unitA unitB).trans
      CFSGJankoTwoBinaryRecoveryMatrixEquality.recovery_matrix
  have hm15 : node015 a b∈J := J.mul_mem J.one_mem hm5
  have hm16 : node016 a b∈J := J.mul_mem hm15 hm12
  have hm17 : node017 a b∈J := J.mul_mem hm16 hm12
  have hm18 : node018 a b∈J := J.mul_mem hm17 hm12
  have hm19 : node019 a b∈J := J.mul_mem hm18 hma
  have hm20 : node020 a b∈J := J.mul_mem hm19 hm8
  have hm21 : node021 a b∈J := J.mul_mem hm20 hm5
  have hm22 : node022 a b∈J := J.mul_mem hm21 hm12
  have hm23 : node023 a b∈J := J.mul_mem hm22 hma
  have hm24 : node024 a b∈J := J.mul_mem hm23 hm8
  have hm25 : node025 a b∈J := J.mul_mem hm24 hm8
  have hm26 : node026 a b∈J := J.mul_mem hm25 hm8
  have hm27 : node027 a b∈J := J.mul_mem hm26 hm14
  have hm28 : node028 a b∈J := J.mul_mem hm27 hm14
  have hm29 : node029 a b∈J := J.mul_mem hm28 hm14
  have hm30 : node030 a b∈J := J.mul_mem hm29 hm10
  have hm31 : node031 a b∈J := J.mul_mem hm30 hma
  have hm32 : node032 a b∈J := J.mul_mem hm31 hm14
  have hm33 : node033 a b∈J := J.mul_mem hm32 hm5
  have hm34 : node034 a b∈J := J.mul_mem hm33 hm10
  have hmb : b∈J := hrecovery ▸ hm34
  have hjoin : U⊔V=⊤ := by
    apply top_unique
    intro g _
    exact PresentedGroup.generated_by _ J (by
      intro i
      fin_cases i
      · exact hma
      · exact hmb) g
  exact goodSylowTwo_of_two_binary_subgroups hCFSG U V hU hV hjoin

end SymmetricSubgroupAsymptotics.CFSGJankoTwoDihedralBinaryGoodSylow
