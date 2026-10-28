import SymmetricSubgroupAsymptotics.OddOrderSolvabilityBinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGJankoOneBinaryFrameGoodSylow
import SymmetricSubgroupAsymptotics.CFSGJankoTwoDihedralBinaryGoodSylow
import SymmetricSubgroupAsymptotics.CFSGRuBinaryMatrixPowerIdentities
import SymmetricSubgroupAsymptotics.CFSGONBinaryMatrixPowerIdentities
import SymmetricSubgroupAsymptotics.CFSGSuzOddRotationBrayMatrixIdentities
import SymmetricSubgroupAsymptotics.CFSGYBinaryDerivedFrames

/-! Original-model closed binary leaves with classification removed from
normalizer solubility. The actual checked whole-matrix identities, literal
source word recovery and genuine source units remain unchanged. Only the
odd-order-solvability argument replaces the old classification parameter.
The final extended-classifier AG consumer supplies it internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddOrderSolvabilityClosedBinaryModels
open CFSGReduction
open SylowTwoNormalizerOfOddOrderSolvability (OddOrderSolvability)

namespace JankoOne
open CFSGJankoOnePresentationGenerators CFSGJankoOneLiteralRepresentation
open CFSGCommutingBinaryFrameGeneration CFSGJankoOneBinaryFrameGoodSylow

theorem goodSylowPrime_of_literal_guide {G : Type} [Group G]
    (hodd : OddOrderSolvability) {x y : G}
    (hpacket : RelatorPacket x y) (hx : x≠1)
    (hrotation : (rotation x y)^10=1)
    (hrecovery : (recoveryIndices.map (seeds x y)).prod=y)
    [Finite CFSG.Models.Presentations.J1.Model]
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model] :
    CFSGReduction.GoodSylowPrime CFSG.Models.Presentations.J1.Model 2 := by
  let a := pinnedX
  let b := pinnedY
  let t := secondInvolution a b
  let z := (rotation a b)^5
  have ha : a^2=1 := pinnedX_square
  have hb : b^3=1 := pinnedY_cube
  have hrot : (rotation a b)^10=1 := by
    apply representation_injective hpacket hx
    simpa only [a,b,map_pow,map_one,map_rotation,representation_pinnedX,representation_pinnedY]
      using hrotation
  have hrec : (recoveryIndices.map (seeds a b)).prod=b := by
    apply representation_injective hpacket hx
    simpa only [a,b,map_list_prod,List.map_map,Function.comp_def,map_seed,
      representation_pinnedX,representation_pinnedY] using hrecovery
  have ht : t^2=1 := by
    have haa : a*a=1 := by simpa only [pow_two] using ha
    change ((conjugator a b)⁻¹*a*(conjugator a b))^2=1
    rw [pow_two]
    calc
      _=(conjugator a b)⁻¹*(a*a)*(conjugator a b) := by group
      _=1 := by rw [haa]; simp only [mul_one,inv_mul_cancel]
  have Fu : Frame (pair a z) := halfProductFrame a t ha ht 5
    (by simpa only [show (2:ℕ)*5=10 by decide] using hrot)
  let v : Bool → CFSG.Models.Presentations.J1.Model := fun j => b⁻¹*pair a z j*b
  have Fv : Frame v := by
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
      Fu.map (MulAut.conj b⁻¹).toMonoidHom
  let P := Subgroup.closure (Set.range (pair a z))
  let Q := Subgroup.closure (Set.range v)
  have hbinv : b^2=b⁻¹ := eq_inv_of_mul_eq_one_left
    (by simpa only [pow_succ,pow_two] using hb)
  have hseed : ∀ i : Fin 4,seeds a b i∈P⊔Q := by
    intro i
    fin_cases i
    · change a∈P⊔Q
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨false,rfl⟩)
    · change z∈P⊔Q
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨true,rfl⟩)
    · change b^2*a*b∈P⊔Q
      rw [hbinv]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨false,rfl⟩)
    · change b^2*z*b∈P⊔Q
      rw [hbinv]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨true,rfl⟩)
  have hbjoin : b∈P⊔Q := by
    rw [←hrec]
    apply (P⊔Q).list_prod_mem
    intro g hg
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hg
    exact hseed i
  have hjoin : P⊔Q=⊤ := by
    apply top_unique
    rw [←presentation_pair_closure]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hga|hg
    · subst g
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨false,rfl⟩)
    · have hgb : g=b := Set.mem_singleton_iff.mp hg
      subst g
      exact hbjoin
  exact SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups hodd P Q Fu.isPGroup Fv.isPGroup hjoin

theorem goodSylowPrime (hodd : OddOrderSolvability)
    [Finite CFSG.Models.Presentations.J1.Model]
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model] :
    CFSGReduction.GoodSylowPrime CFSG.Models.Presentations.J1.Model 2 := by
  apply goodSylowPrime_of_literal_guide hodd CFSGJankoOneSevenMatrices.relatorPacket
    CFSGJankoOneSevenMatrices.unitA_ne_one
  · simpa only [rotation,secondInvolution,conjugator,
      CFSGJankoOneSevenMatrices.rotation,CFSGJankoOneSevenMatrices.conjugator] using
      CFSGJankoOneSevenMatrices.rotation_tenth
  · have hs : seeds CFSGJankoOneSevenMatrices.unitA CFSGJankoOneSevenMatrices.unitB=
        CFSGJankoOneSevenMatrices.seeds := by
      funext i
      fin_cases i <;> simp [seeds,CFSGJankoOneSevenMatrices.seeds,rotation,
        secondInvolution,conjugator,CFSGJankoOneSevenMatrices.rotation,
        CFSGJankoOneSevenMatrices.conjugator]
    simpa only [hs,recoveryIndices,CFSGJankoOneSevenMatrices.recoveryIndices] using
      CFSGJankoOneSevenMatrices.recovery_product

end JankoOne

namespace JankoTwo
open CFSGJankoTwoBinaryRecoveryWords CFSGJankoTwoSelectedMatrixIdentities
open CFSGJankoTwoActualHeisenbergFrame

abbrev G := CFSG.Models.Presentations.J2.Model
private def a : G := PresentedGroup.of (0 : Fin 2)
private def b : G := PresentedGroup.of (1 : Fin 2)
private theorem image_a : rho a=unitA := rho_first
private theorem image_b : rho b=unitB := rho_second

theorem goodSylowPrime (hodd : OddOrderSolvability)
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
  exact SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups hodd U V hU hV hjoin

end JankoTwo

namespace Y
open CFSG.Models.YGroups

theorem goodSylowPrime (arms : Arms) [Finite (SimpleSection arms)]
    (hodd : OddOrderSolvability) : GoodSylowPrime (SimpleSection arms) 2 := by
  obtain ⟨U,V,hU,hV,hgen⟩ := CFSGYBinaryDerivedFrames.exists_binary_generating_subgroups arms
  let q : commutator (CFSG.Models.YGroups.Group arms) →* SimpleSection arms :=
    QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms)))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  apply SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups
    hodd (U.map q) (V.map q) (hU.map q) (hV.map q)
  rw [←Subgroup.map_sup,hgen,Subgroup.map_top_of_surjective q hq]

end Y

namespace Ru
open CFSG.Models.MatrixGroups.Ru

theorem goodSylowPrime (hodd : OddOrderSolvability)
    [Finite Model] (hn : ¬IsMulCommutative Model) : GoodSylowPrime Model 2 := by
  exact OddOrderSolvabilityBinaryGenerators.matrix_model_goodSylowTwo_of_binary_powers
    hodd 2 28 rows1 rows2 hn 1 2
    (by simpa only [show (2 : ℕ)^1=2 by decide] using CFSGRuBinaryMatrixPowerIdentities.first_square)
    (by simpa only [show (2 : ℕ)^2=4 by decide] using CFSGRuBinaryMatrixPowerIdentities.second_fourth)

end Ru

namespace ON
open CFSG.Models.MatrixGroups.ON

theorem goodSylowPrime (hodd : OddOrderSolvability)
    [Finite Model] (hn : ¬IsMulCommutative Model) : GoodSylowPrime Model 2 := by
  exact OddOrderSolvabilityBinaryGenerators.matrix_model_goodSylowTwo_of_binary_powers
    hodd 3 154 rows1 rows2 hn 1 2
    (by simpa only [show (2 : ℕ)^1=2 by decide] using CFSGONBinaryMatrixPowerIdentities.first_square)
    (by simpa only [show (2 : ℕ)^2=4 by decide] using CFSGONBinaryMatrixPowerIdentities.second_fourth)

end ON

namespace Suz
open CFSG.Models.MatrixGroups.Suz

theorem goodSylowPrime (hodd : OddOrderSolvability)
    [Finite Model] (hn : ¬IsMulCommutative Model) : GoodSylowPrime Model 2 := by
  exact OddOrderSolvabilityBinaryGenerators.matrix_model_goodSylowTwo_of_odd_rotation
    hodd 3 64 rows1 rows2 hn 7 8
    CFSGSuzOddRotationBrayMatrixIdentities.first_square
    CFSGSuzOddRotationBrayMatrixIdentities.second_cube
    (by simpa only [show 2*7+1=(15 : ℕ) by decide] using CFSGSuzOddRotationBrayMatrixIdentities.rotation_fifteenth)
    (by simpa only [show 7+1=(8 : ℕ) by decide,show 2^8=(256 : ℕ) by decide] using CFSGSuzOddRotationBrayMatrixIdentities.bray_binary_power)

end Suz
end SymmetricSubgroupAsymptotics.OddOrderSolvabilityClosedBinaryModels
