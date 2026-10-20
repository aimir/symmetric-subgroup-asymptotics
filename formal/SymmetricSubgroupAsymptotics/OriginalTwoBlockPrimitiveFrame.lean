import SymmetricSubgroupAsymptotics.PrimitiveEightCanonicalMatch
import SymmetricSubgroupAsymptotics.OriginalTwoBlockLiteralPrimitiveFrame

/-! The actual two-block, eight-point-component branch. Canonical
completeness is used only to identify the component; every exclusion,
normal-generator bound and frame estimate is proved. The ambient normal
subgroup and the given stabilizer epimorphism are unchanged. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G X] [Finite X]
    {x₀ : X} (D : OriginalMinimalBlock (A := G) x₀)

theorem eightPoint_component_normal_singletons
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card D.Fibre = 8) :
    ∀ N : Subgroup D.Component, N.Normal →
      ∃ z : Fin 1 → D.Component, Subgroup.normalClosure (Set.range z) = N := by
  letI := D.component_preprimitive
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch published D.Component hr
  exact D.component_normal_singletons_of_literal M.index M.primitive_index M.groupEquiv

theorem twoBlock_primitive_frame_sum_le_seven
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hX : Nat.card X = 16) (hr : Nat.card D.Fibre = 8)
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
  have hs : Nat.card D.Points = 2 := by
    have h := D.degree_product
    rw [hr, hX] at h
    omega
  letI := D.component_preprimitive
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch published D.Component hr
  exact D.twoBlock_literalPrimitive_frame_sum_le_seven hs hX M.index M.primitive_index
    M.groupEquiv x f hf rho hC hdim hrho N B

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock

end
