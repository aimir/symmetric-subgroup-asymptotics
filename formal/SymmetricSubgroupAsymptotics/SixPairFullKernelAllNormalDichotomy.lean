import SymmetricSubgroupAsymptotics.SixPairFullKernelCentralizerTop

/-! Every original normal denominator is either contained in the actual
coarse center or contains that center. Physical top faithfulness removes
the earlier restriction that the denominator lie in the coarse kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelAllNormalDichotomy
open SixPairFullKernelCenter

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

/-- No original normal axis, including axes meeting the top, is omitted. -/
theorem normal_dichotomy [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (N : Subgroup U) [N.Normal] : N≤centerImage F E ∨ centerImage F E≤N := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let L := N ⊓ C.top.ker
  rcases SixPairFullKernelCenter.normal_dichotomy F E hfull L inf_le_right with hL | hZ
  · left
    intro g hg
    have hcomm (k : C.top.ker) : g*k.val*g⁻¹*k.val⁻¹∈L := by
      constructor
      · have hn : k.val*g⁻¹*k.val⁻¹∈N :=
          Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hg) k.val
        simpa only [mul_assoc] using N.mul_mem hg hn
      · change C.top (g*k.val*g⁻¹*k.val⁻¹)=1
        rw [map_mul,map_mul,map_mul,map_inv,map_inv,
          MonoidHom.mem_ker.mp k.property]
        simp
    have hgK : g∈C.top.ker :=
      SixPairFullKernelCentralizerTop.mem_kernel_of_commutators_mem_center F E hfull g
        (fun k => hL (hcomm k))
    exact hL ⟨hg,hgK⟩
  · right
    exact hZ.trans inf_le_left

end SymmetricSubgroupAsymptotics.SixPairFullKernelAllNormalDichotomy
