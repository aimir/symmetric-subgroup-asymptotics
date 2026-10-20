import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.BinaryPairNormalHead
import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead

/-! Any actual normal subgroup of a physical six-pair kernel has one
relative binary head position from the actual pair-top permutation-module uniform-one bound. Correlated flip subspaces are retained separately. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairUniformOriginalKernelHead

theorem normal_kernel_head_le_one {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6))
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)≤1 := by
  letI : MulAction U (Fin 6) := MulAction.compHom (Fin 6) F.top
  have hact : ∀ (u : U) (i : Fin 6), u • i=F.top u i := fun _ _ => rfl
  have hu := UniformSubrepresentationGeneratorBound.comp_of_surjective
    (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6))
    F.top.rangeRestrict F.top.rangeRestrict_surjective
    hpair
  have he : (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)).comp
      F.top.rangeRestrict = permutationFunctionRepresentation (ZMod 2) U (Fin 6) := by
    apply MonoidHom.ext
    intro u
    apply LinearMap.ext
    intro v
    funext i
    change v ((F.top u)⁻¹ i)=v (F.top (u⁻¹) i)
    rw [map_inv]
  rw [he] at hu
  let W := F.normalKernelOriginalSubrepresentation hact N hN
  obtain ⟨v,hv⟩ := hu W
  rw [← (F.normalKernelOriginalCharactersEquiv hact N hN).finrank_eq]
  exact representationCharacterHead_le_generators W.toRepresentation v hv

end SymmetricSubgroupAsymptotics.BinaryPairUniformOriginalKernelHead
