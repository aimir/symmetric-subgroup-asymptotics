import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusIndex

/-! The paired-torus image on the norm-one residual plane has index at
most two. This is the actual fibre of the original norm/quotient map,
with its norm component equal to one, rather than a cardinal heuristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneTorusIndex
open CFSGTwistedDRelativeTorusParameters CFSGTwistedDNormOneUnits CFSGTwistedA2FixedField

def residualInclusion (q : CFSG.PrimePower) :
    normOneUnits q →* (fixedField q)ˣ × normOneUnits q where
  toFun z := (1, z)
  map_one' := rfl
  map_mul' z w := by simp only [Prod.mk_mul_mk, one_mul]

def retainedResidual (q : CFSG.PrimePower) : Subgroup (normOneUnits q) :=
  (torusParameterHom q).range.comap (residualInclusion q)

theorem mem_retainedResidual_iff (q : CFSG.PrimePower) (z : normOneUnits q) :
    z ∈ retainedResidual q ↔ ∃ c : (q.Extension 2)ˣ,
      normHom q c = 1 ∧ quotientHom q c = z := by
  change (∃ c : (q.Extension 2)ˣ, torusParameterHom q c = (1, z)) ↔ _
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  · rintro ⟨c, hn, hz⟩
    exact ⟨c, Prod.ext hn hz⟩

theorem retainedResidual_index_le_two (q : CFSG.PrimePower) :
    (retainedResidual q).index ≤ 2 := by
  change ((torusParameterHom q).range.comap (residualInclusion q)).index ≤ 2
  rw [Subgroup.index_comap]
  have hn : (torusParameterHom q).range.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  calc
    (torusParameterHom q).range.relIndex (residualInclusion q).range ≤
        (torusParameterHom q).range.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right le_top hn
    _ = (torusParameterHom q).range.index := by rw [Subgroup.relIndex_top_right]
    _ ≤ 2 := CFSGTwistedDRelativeTorusIndex.torus_parameter_index_le_two q

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneTorusIndex
