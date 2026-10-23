import SymmetricSubgroupAsymptotics.CFSGTwistedA2RadicalTorusAction
import SymmetricSubgroupAsymptotics.CFSGGeneratedScalarNormalizer

/-! Actual rank-two torus-normalizing radical automorphisms induce
field-semilinear maps on the SAME intrinsic quotient. The field-generation
input is discharged by the literal first-weight subgroup, every q >= 3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedA2DiagonalTorus
open CFSGFiniteFieldScalarNormalizer

def rankTwoSigmaUnits (q : CFSG.PrimePower) : (q.Extension 2)ˣ ≃* (q.Extension 2)ˣ :=
  Units.mapEquiv (definingFieldAutomorphism q 2).toMulEquiv

theorem rankTwoFirstWeight_sigma (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    (rankTwoFirstWeightHom q (rankTwoSigmaUnits q z) : q.Extension 2) =
      definingFieldAutomorphism q 2
        (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) (z : q.Extension 2)) := by
  rw [rankTwoFirstWeightHom_val]
  change (definingFieldAutomorphism q 2 z) ^ 2 /
    definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 z) =
      definingFieldAutomorphism q 2 ((z : q.Extension 2) ^ 2 / definingFieldAutomorphism q 2 z)
  rw [map_div₀, map_pow]

theorem rankTwoFirstLayer_torus (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    rankTwoFirstLayerAutHom q (rankTwoRadicalTorusAutHom q z) =
      scalarHom (q.Extension 2) (rankTwoFirstWeightHom q (rankTwoSigmaUnits q z)) := by
  apply AddEquiv.ext
  intro x
  obtain ⟨g, hg⟩ := rankTwoParameterHom_surjective q (Multiplicative.ofAdd x)
  have hx : (rankTwoParameterHom q g).toAdd = x := congrArg Multiplicative.toAdd hg
  have he := rankTwoFirstLayerAutHom_first q (rankTwoRadicalTorusAut q z) g
  rw [rankTwoRadicalTorusAut_first] at he
  change rankTwoFirstLayerAutHom q (rankTwoRadicalTorusAutHom q z) x =
    (rankTwoFirstWeightHom q (rankTwoSigmaUnits q z) : q.Extension 2) * x
  simpa only [hx, rankTwoFirstWeight_sigma] using he

theorem rankTwoFirstLayer_map_torus (q : CFSG.PrimePower) :
    (rankTwoRadicalTorusAutHom q).range.map (rankTwoFirstLayerAutHom q) =
      scalarSubgroupOf (rankTwoFirstWeightHom q).range := by
  ext A
  constructor
  · rintro ⟨f, ⟨z, rfl⟩, rfl⟩
    exact ⟨rankTwoFirstWeightHom q (rankTwoSigmaUnits q z),
      ⟨rankTwoSigmaUnits q z, rfl⟩, (rankTwoFirstLayer_torus q z).symm⟩
  · rintro ⟨u, ⟨z, rfl⟩, rfl⟩
    refine ⟨rankTwoRadicalTorusAutHom q ((rankTwoSigmaUnits q).symm z),
      ⟨(rankTwoSigmaUnits q).symm z, rfl⟩, ?_⟩
    rw [rankTwoFirstLayer_torus, MulEquiv.apply_symm_apply]

theorem rankTwoFirstLayer_mem_scalar_normalizer (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (fixedRadical q 0))
    (hf : f ∈ Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0)))) :
    rankTwoFirstLayerAutHom q f ∈
      Subgroup.normalizer (scalarSubgroup (q.Extension 2) : Set (AddAut (q.Extension 2))) := by
  have he := Subgroup.le_normalizer_map (H := (rankTwoRadicalTorusAutHom q).range)
    (rankTwoFirstLayerAutHom q)
    (show rankTwoFirstLayerAutHom q f ∈
      (Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0)))).map
        (rankTwoFirstLayerAutHom q) from ⟨f, hf, rfl⟩)
  rw [rankTwoFirstLayer_map_torus] at he
  exact generating_scalar_normalizer_le (rankTwoFirstWeightHom q).range
    (rankTwoFirstWeight_generates_field q hq) he

theorem rankTwoFirstLayer_scalar_ringAut (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (fixedRadical q 0))
    (hf : f ∈ Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0)))) :
    ∃! p : (q.Extension 2)ˣ × (q.Extension 2 ≃+* q.Extension 2),
      ∀ g : fixedRadical q 0, (rankTwoParameterHom q (f g)).toAdd =
        (p.1 : q.Extension 2) * p.2 (rankTwoParameterHom q g).toAdd := by
  obtain ⟨p, hp, hunique⟩ := exists_unique_scalar_ringAut (rankTwoFirstLayerAutHom q f)
    (rankTwoFirstLayer_mem_scalar_normalizer q hq f hf)
  refine ⟨p, ?_, ?_⟩
  · intro g
    rw [← rankTwoFirstLayerAutHom_first q f g]
    exact hp _
  · intro a ha
    apply hunique a
    intro x
    obtain ⟨g, hg⟩ := rankTwoParameterHom_surjective q (Multiplicative.ofAdd x)
    have hx : (rankTwoParameterHom q g).toAdd = x := congrArg Multiplicative.toAdd hg
    have he := ha g
    rw [← rankTwoFirstLayerAutHom_first q f g, hx] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
