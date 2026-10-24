import SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterHom

/-! The explicit finite commuting-parameter word parametrizes exactly the
join of its actual factor ranges. This supports radical normalization by
its displayed root generators, without a root census or new recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterRange
open CFSGFiniteCommutingParameterHom
variable {K G : Type*} [AddCommGroup K] [Group G] {m : ℕ}

theorem parameterHom_range (f : Fin m → Multiplicative K →* G)
    (hcomm : Pairwise (fun i j => ∀ a b,Commute (f i a) (f j b))) :
    (parameterHom f hcomm).range = ⨆ i, (f i).range := by
  apply le_antisymm
  · rintro g ⟨v,rfl⟩
    change Finset.univ.noncommProd (fun i => f i (Multiplicative.ofAdd (v.toAdd i)))
      (fun i _ j _ hij => hcomm hij (Multiplicative.ofAdd (v.toAdd i))
        (Multiplicative.ofAdd (v.toAdd j))) ∈ _
    apply Subgroup.noncommProd_mem
    intro i _
    exact (show (f i).range ≤ ⨆ j, (f j).range from le_iSup (fun j => (f j).range) i) ⟨_,rfl⟩
  · refine iSup_le fun i => ?_
    rintro g ⟨a,rfl⟩
    refine ⟨Multiplicative.ofAdd (Pi.single i a.toAdd),?_⟩
    exact parameterHom_single f hcomm i a.toAdd

end SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterRange
