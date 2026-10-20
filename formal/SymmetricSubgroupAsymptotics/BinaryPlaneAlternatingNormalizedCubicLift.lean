import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCubicCentralizingLift
import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator

/-! The local factor of an actual centralizing base-block stabilizer is
removed by an actual power of the retained cubic generator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalizedCubicLift
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (label)

private theorem cubic_correction : ∀ p q : Equiv.Perm (Fin 3),
    q^3=1 → q≠1 → p*q=q*p → ∃ n : Fin 3, q^n.val*p=1 := by decide +kernel

/-- An actual odd-kernel power cancels the local cubic holonomy. This
normalizes only a base-fixing centralizing lift, not an entire S4 action. -/
theorem normalize (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (g : C) (hb : (g : Frame).right (label 1)=label 1)
    (hcentral : ∀ o : oddKernel C, Commute g (o : C)) :
    ∃ z : C, (z : Frame).right=(g : Frame).right ∧
      (z : Frame).left (label 1)=1 ∧
      ∀ o : oddKernel C, Commute z (o : C) := by
  let k := BinaryPlaneRankOneOddGenerator.generator C e
  let K : Linear := localLinear C (label 1) k
  let M : Linear := (g : Frame).left (label 1)
  have hin : (g : Frame).right⁻¹ (label 1)=label 1 := by
    have he := congrArg (g : Frame).right.symm hb
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hcomm : M*K=K*M := by
    have hh := congrArg (fun z : C => (z : Frame).left (label 1)) (hcentral k).eq
    simp only [Subgroup.coe_mul,PermutationalWreathProduct.mul_left,
      Pi.mul_apply,top_one C k,inv_one,one_smul] at hh
    change (g : Frame).left (label 1)*((k : C) : Frame).left
      ((g : Frame).right⁻¹ (label 1))=
      ((k : C) : Frame).left (label 1)*(g : Frame).left (label 1) at hh
    rw [hin] at hh
    exact hh
  have hk : K^3=1 := local_cubic C (label 1) k
  have hn : K≠1 := BinaryPlaneRankOneOddGenerator.local_nontrivial C e
    (BinaryPlaneAlternatingKernelPartition.transitive C heven) (label 1)
  obtain ⟨n,hcorr⟩ := cubic_correction (toThree M) (toThree K)
    (by rw [← map_pow,hk,map_one])
    (fun h => hn (toThree_injective (h.trans (map_one _).symm)))
    (by simpa only [map_mul] using congrArg toThree hcomm)
  have hKM : K^n.val*M=1 := by
    apply toThree_injective
    simpa only [map_mul,map_pow,map_one] using hcorr
  let u : oddKernel C := k^n.val
  let z : C := (u : C)*g
  have ht : (z : Frame).right=(g : Frame).right := by
    change (((u : C) : Frame)* (g : Frame)).right=(g : Frame).right
    rw [PermutationalWreathProduct.mul_right,top_one C u,one_mul]
  have hl : (z : Frame).left (label 1)=1 := by
    change ((((u : C) : Frame)* (g : Frame)).left (label 1))=1
    rw [PermutationalWreathProduct.mul_left]
    change localLinear C (label 1) u *
      (g : Frame).left ((((u : C) : Frame).right)⁻¹ • label 1)=1
    rw [top_one C u,inv_one,one_smul]
    change localLinear C (label 1) (k^n.val)*M=1
    rw [map_pow]
    exact hKM
  refine ⟨z,ht,hl,?_⟩
  intro o
  have hu : Commute (u : C) (o : C) := by
    change (u : C)*(o : C)=(o : C)*(u : C)
    exact congrArg (fun v : oddKernel C => (v : C))
      (isMulCommutative_iff.mp (commutative C) u o)
  exact hu.mul_left (hcentral o)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalizedCubicLift
