import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex

/-! The centre of the ACTUAL fixed radical is exactly its actual
central parameter kernel, all prime powers. Nondegeneracy follows from
the proved onto centre-valued commutator, also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUnitaryNaturalRadical

theorem centralPair_separates (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2)
    (hv : ∀ w, centralPair q s v w = 0) : v = 0 := by
  by_contra hv0
  obtain ⟨c, hc0, hc⟩ := exists_nonzero_central_parameter q s
  let z : centralParameters q s := ⟨c, (centralCondition_iff q s c).mp hc⟩
  have hz : z ≠ 0 := fun he => hc0 (congrArg Subtype.val he)
  obtain ⟨w, hw⟩ := centralPair_surjective q s v hv0 z
  exact hz (hw.symm.trans (hv w))

theorem fixedRadical_center_eq_kernel (q : CFSG.PrimePower) (s : ℕ) :
    Subgroup.center (fixedRadical q s) = (fixedRadicalParameterHom q s).ker := by
  apply le_antisymm
  · intro g hg
    change fixedRadicalParameterHom q s g = 1
    apply Multiplicative.toAdd.injective
    apply centralPair_separates q s
    intro w
    obtain ⟨h, hh⟩ := fixedRadicalParameterHom_surjective q s (Multiplicative.ofAdd w)
    have hp : (fixedRadicalParameterHom q s h).toAdd = w := congrArg Multiplicative.toAdd hh
    have hcomm : ⁅g, h⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact (Subgroup.mem_center_iff.mp hg h).symm
    have hxy := fixedRadical_commutator q s g h
    rw [hp, hcomm] at hxy
    have he : centralRadicalHom q s (Multiplicative.ofAdd
        (centralPair q s (fixedRadicalParameterHom q s g).toAdd w)) = 1 := hxy.symm
    have hz := centralRadicalHom_injective q s
      (he.trans (map_one (centralRadicalHom q s)).symm)
    exact congrArg Multiplicative.toAdd hz
  · rw [← centralRadicalHom_range_eq_kernel]
    rintro g ⟨c, rfl⟩
    exact centralRadicalHom_mem_center q s c

theorem fixedRadical_center_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (Subgroup.center (fixedRadical q s)) = q.order := by
  rw [fixedRadical_center_eq_kernel, fixedRadicalParameterHom_kernel_card]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
