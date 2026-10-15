import SymmetricSubgroupAsymptotics.OriginalTwoBlockFrameBound
import SymmetricSubgroupAsymptotics.PrimitiveEightLiteralNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitivePGroupDegree

/-! Bind the seven literal local normal chains to an actual two-block
action. The chart is used only on the actual local component; the original
ambient group, normal subgroup, point stabilizer, and local epimorphism
remain unchanged. A three-plus-four estimate leaves room in the ten-slot
degree-four frame budget. The exact primitive-catalogue match is still
supplied separately. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G X] [Finite X]
    {x₀ : X} (D : OriginalMinimalBlock (A := G) x₀)

theorem eightPoint_component_not_binary (hr : Nat.card D.Fibre = 8) :
    ¬ IsPGroup 2 D.Component := by
  letI := D.component_preprimitive
  exact primitive_eight_not_binary hr

theorem component_normal_singletons_of_literal (j : Fin 24) (hj : 17 ≤ j.val)
    (e : D.Component ≃* (DegreeTwoPairedEightSharedTops.interface j).top) :
    ∀ N : Subgroup D.Component, N.Normal →
      ∃ z : Fin 1 → D.Component, Subgroup.normalClosure (Set.range z) = N :=
  normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (PrimitiveEightLiteralNormalGenerators.normal_generating_singletons j hj)

theorem twoBlock_literalPrimitive_frame_sum_le_seven (hs : Nat.card D.Points = 2)
    (hX : Nat.card X = 16) (j : Fin 24) (hj : 17 ≤ j.val)
    (e : D.Component ≃* (DegreeTwoPairedEightSharedTops.interface j).top)
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : X) (f : MulAction.stabilizer G x →* C) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) C V)
    (hC : Nat.card C = 3 ∨ Nat.card C = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (N : Subgroup G) [N.Normal]
    (B : Subrepresentation (Representation.coind (MulAction.stabilizer G x).subtype
      (rho.comp f))) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))
        ≤ 7 := by
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  have hn := D.twoBlock_relativeHead_le hs
    (D.component_normal_singletons_of_literal j hj e) N
  have hb := BinaryTopNormalizerOrbitHead.head_le_four_on_points x hX
    D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective (D.twoBlock_top_isPGroup hs)
    (fun _ _ => rfl) D.map D.map_equivariant f hf rho hC hdim hrho B
  omega

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock

end
