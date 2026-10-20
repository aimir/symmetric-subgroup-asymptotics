import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerKleinLift
import SymmetricSubgroupAsymptotics.BinaryPlaneTopTrivialCubicKernel
import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator
import SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators

/-! In the rank-one case the actual TOP kernel embeds in one local S3.
The local projection is proved injective using the actual odd line and
actual centralizer, not a presumed diagonal model. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneTopKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (top regular)
open BinaryPlaneAlternatingCentralizerKleinLift (alpha centralRegular beta)

variable (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)

include e heven in
theorem local_injective (i : Fin 4) : Function.Injective (localLinear C i) := by
  have hcard : Nat.card (oddKernel C)=3 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  letI : Fact (Nat.card (oddKernel C)).Prime := ⟨by rw [hcard]; decide⟩
  rcases (localLinear C i).ker.eq_bot_or_eq_top_of_prime_card with hb | ht
  · exact (localLinear C i).ker_eq_bot_iff.mp hb
  · exfalso
    have hm : BinaryPlaneRankOneOddGenerator.generator C e∈(localLinear C i).ker := by
      rw [ht]; trivial
    exact BinaryPlaneRankOneOddGenerator.local_nontrivial C e
      (BinaryPlaneAlternatingKernelPartition.transitive C heven) i hm

/-- Literal local homomorphism on the actual top kernel. -/
def localTopKernel : (top C).ker →* Linear where
  toFun g := ((g : C) : Frame).left 0
  map_one' := rfl
  map_mul' g h := by
    have ht : ((g : C) : Frame).right=1 := g.property
    change ((((g : C) : Frame)*((h : C) : Frame)).left 0)=_
    rw [PermutationalWreathProduct.mul_left]
    simp only [Pi.mul_apply,ht,inv_one,one_smul]

include e heven in
theorem localTopKernel_injective : Function.Injective (localTopKernel C) := by
  apply (localTopKernel C).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx0 : ((x : C) : Frame).left 0=1 := hx
  have hxt : ((x : C) : Frame).right=1 := x.property
  have ha : alpha C (x : C)=1 := by
    apply MulEquiv.ext
    intro o
    apply local_injective C e heven 0
    have hh := localLinear_conjugate C (x : C) o 0
    simpa only [hxt,one_smul,hx0,one_mul,inv_one,mul_one] using hh
  let d : centralRegular C := ⟨(x : C),ha,⟨1,by simpa only [map_one] using hxt.symm⟩⟩
  have hd : d∈(beta C).ker := by
    apply Subtype.ext
    exact hxt
  let z : (beta C).ker := ⟨d,hd⟩
  have hc : (x : C)^3=1 := congrArg
    (fun y : (beta C).ker => ((y : centralRegular C) : C))
    (BinaryPlaneAlternatingCentralizerKleinLift.beta_kernel_cubic C e heven z)
  let o : oddKernel C := ⟨(x : C),BinaryPlaneTopTrivialCubicKernel.mem_oddKernel C (x : C) hxt hc⟩
  have ho : o=1 := local_injective C e heven 0 (by
    change ((x : C) : Frame).left 0=localLinear C 0 1
    rw [hx0,map_one])
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact congrArg (fun t : oddKernel C => (t : C)) ho

include e heven in
/-- The actual top kernel is an actual subgroup of one local S3, so its
normal subgroups admit singleton tuples internally. -/
theorem normal_generating_singletons :
    ∀ N : Subgroup (top C).ker, N.Normal →
      ∃ x : Fin 1 → (top C).ker, Subgroup.normalClosure (Set.range x)=N := by
  let f := BinaryPlaneWreathNormalGenerators.toThree.comp (localTopKernel C)
  have hf : Function.Injective f := BinaryPlaneWreathNormalGenerators.toThree_injective.comp
    (localTopKernel_injective C e heven)
  let E : (top C).ker ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  exact normal_generating_tuples_of_surjective E.symm.toMonoidHom E.symm.surjective
    (SymmetricThreeSubgroupNormalGenerators.normal_generating_singletons f.range)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneTopKernel
