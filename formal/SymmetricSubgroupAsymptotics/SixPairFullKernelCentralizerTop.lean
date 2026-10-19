import SymmetricSubgroupAsymptotics.SixPairFullKernelHeadSurjective
import SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathCentralizer
import Mathlib.GroupTheory.Commutator.Basic

/-! An element centralizing the actual full kernel modulo its original
center has trivial retained physical top. This is proved using the actual
head surjection, rather than a quotient type or normal-census annotation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelCentralizerTop
open SixPairFullKernelCenter SixPairCoarseWreathHead SixPairCoarseWreathHeadKernel
open SixPairFullKernelHeadSurjective

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

theorem mem_kernel_of_commutators_mem_center
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (g : U)
    (hcomm : ∀ k : (SixPairNestedTopFrames.nestedFrame F E).top.ker,
      g*k.val*g⁻¹*k.val⁻¹∈centerImage F E) :
    g∈(SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  have ht : (headHom F E g).right=1 := by
    apply TwoBinaryThreeWreathKernel.right_eq_one_of_centralizes_kernel C.top.range
    intro w
    obtain ⟨k,hk⟩ := head_base_surjective F E hfull
      (TwoBinaryThreeWreathKernel.base C.top.range w)
    have he : headKernel F E k=w :=
      TwoBinaryThreeWreathKernel.base_injective C.top.range hk
    rw [←he]
    change headHom F E g*headHom F E k.val=headHom F E k.val*headHom F E g
    have hc : g*k.val*g⁻¹*k.val⁻¹∈(headHom F E).ker := by
      rw [ker_head F E hfull]
      exact hcomm k
    have hm := MonoidHom.mem_ker.mp hc
    rw [map_mul,map_mul,map_mul,map_inv,map_inv] at hm
    exact commutatorElement_eq_one_iff_mul_comm.mp hm
  change C.top g=1
  exact congrArg (fun t : C.top.range => (t : Equiv.Perm (Fin 3))) ht

end SymmetricSubgroupAsymptotics.SixPairFullKernelCentralizerTop
