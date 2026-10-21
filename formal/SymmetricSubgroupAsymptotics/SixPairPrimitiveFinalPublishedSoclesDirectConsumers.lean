import SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGeneratorsDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles

namespace DirectConsumers

open BinarySixPointFiveCyclePolynomial

open Non2UnipotentPrefixFiniteMenu

variable (socle : PublishedPrimitiveSocleDichotomyInput)
  (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
  {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 6))

include socle catalogue in

theorem quotientSocle (a b : U) (q : Equiv.Perm (Fin 6))
    (ha : F.top a = SixPointFiveCyclePrimitive.cycle) (hb : F.top b = q)
    (hmoves : q 5 ≠ 5)
    (hmatrix : ∀ i x : Fin 6,
      actualOperator representation SixPointFiveCyclePrimitive.cycle q (Pi.single i 1) x =
        operator 0 (Pi.single i 1) x)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  have haction (g : U) (p : Equiv.Perm (Fin 6)) (hg : F.top g = p) :
      permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)
        (F.top.rangeRestrict g) = representation p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((F.top g)⁻¹ x) = v (p⁻¹ x)
    rw [hg]
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1 :=
    uniform_of_actions 0 _ (F.top.rangeRestrict a) (F.top.rangeRestrict b)
      SixPointFiveCyclePrimitive.cycle q (haction a _ ha) (haction b _ hb) hmatrix
  letI : MulAction.IsPreprimitive F.top.range (Fin 6) :=
    SixPointFiveCyclePrimitive.preprimitive F.top.range
      (F.top.rangeRestrict a) (F.top.rangeRestrict b) ha (by change F.top b 5 ≠ 5; rwa [hb])
  apply F.quotientSocle_of_uniform_pair_action 1 1 hu ?_ N
  intro L hL
  letI := hL
  exact _root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.DirectConsumers.normalGen_le_one
    socle catalogue F.top.range L

include socle catalogue in

theorem quotientSocle_of_generators {ι : Type*}
    (frame : Fin 6 × ZMod 2 ≃ X) (gs : ι → Equiv.Perm X)
    (tops : ι → Equiv.Perm (Fin 6)) (ai bi : ι)
    (hp : ∀ i, BinaryPairFrame.Preserves frame (gs i) (tops i))
    (ha : tops ai = SixPointFiveCyclePrimitive.cycle) (hmoves : tops bi 5 ≠ 5)
    (hmatrix : ∀ i x : Fin 6,
      actualOperator representation SixPointFiveCyclePrimitive.cycle (tops bi) (Pi.single i 1) x =
        operator 0 (Pi.single i 1) x)
    (N : Subgroup (Subgroup.closure (Set.range gs))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range gs)) ⧸ N) 2 := by
  let F := BinaryPairFrame.ofGenerators frame gs tops hp
  exact _root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles.DirectConsumers.quotientSocle socle catalogue F (closureGenerators gs ai) (closureGenerators gs bi) (tops bi)
    ((BinaryPairFrame.ofGenerators_top_generator _ _ _ hp ai).trans ha)
    (BinaryPairFrame.ofGenerators_top_generator _ _ _ hp bi) hmoves hmatrix N

end DirectConsumers

end SymmetricSubgroupAsymptotics.SixPairPrimitiveFinalPublishedSocles

end

