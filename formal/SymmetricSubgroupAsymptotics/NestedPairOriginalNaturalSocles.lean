import SymmetricSubgroupAsymptotics.ThreePairNormalGenerators

/-! Generator-facing form of the actual nested-pair theorem. The natural
bound belongs to the unchanged original point action. The two literal
physical pair charts and one original inner rotation generator suffice;
no six-cycle, top group identification, or normal-lattice certificate is
required. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.NestedPairOriginalNaturalSocles

variable {X : Type} [Finite X]

theorem quotientSocle_of_generators {ι : Type*}
    (outerFrame : Fin 6 × ZMod 2 ≃ X) (innerFrame : Fin 3 × ZMod 2 ≃ Fin 6)
    (generators : ι → Equiv.Perm X) (tops : ι → Equiv.Perm (Fin 6))
    (blocks : ι → Equiv.Perm (Fin 3))
    (hp : ∀ i, BinaryPairFrame.Preserves outerFrame (generators i) (tops i))
    (hq : ∀ i, BinaryPairFrame.Preserves innerFrame (tops i) (blocks i))
    (ri : ι) (hr : blocks ri = NestedBinaryPairSocles.rotation)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range generators)) X) 1)
    (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range generators)) ⧸ N) 3 := by
  let F := BinaryPairFrame.ofGenerators outerFrame generators tops hp
  let E := BinaryPairFrame.ofGenerators innerFrame tops blocks hq
  apply ThreePairNormalGenerators.quotientSocle_of_original_natural E F
    (BinaryPairFrame.ofGenerators_top_range _ _ _ hp)
    (closureGenerators tops ri) ?_ huniform N
  exact (BinaryPairFrame.ofGenerators_top_generator _ _ _ hq ri).trans hr

end SymmetricSubgroupAsymptotics.NestedPairOriginalNaturalSocles

end
