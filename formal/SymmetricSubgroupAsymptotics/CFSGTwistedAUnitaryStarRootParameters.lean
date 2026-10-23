import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveStarParameters
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRootLines

/-! Exact original root-line membership in the intrinsic Hermitian star
coordinates. Membership is EQUIVALENT to lying on the literal fixed-
scalar rank-one coefficient line, not merely implied by a determinant
or counted by its cardinality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical

theorem exists_conjugateCentralFixed_starRankOne (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (v : Fin 2 → q.Extension 2) (g : naturalFixed (s + 3) q) (c : q.Extension 2)
    (hgv : unitaryCentralVector q s g = c • starVector q s v)
    (b : q.Extension 2) (hb : Condition q (s + 1) 0 b) :
    ∃ (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a),
      g * centralFixed q (s + 1) b hb * g⁻¹ =
        starFixed q s (starRankOneParameters q s t htc a ha v) := by
  have hbf : b ∈ centralParameters q (s + 1) := (centralCondition_iff q (s + 1) b).mp hb
  have hcc : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 c) = c :=
    extension_two_pow_twice q c
  have hnf : definingFieldAutomorphism q 2 (c * definingFieldAutomorphism q 2 c) =
      c * definingFieldAutomorphism q 2 c := by
    rw [map_mul, hcc]
    exact mul_comm _ _
  have hbn : b * (c * definingFieldAutomorphism q 2 c) ∈ centralParameters q (s + 1) :=
    star_central_mul_fixed q s b hbf _ hnf
  let a : q.Extension 2 := (b * (c * definingFieldAutomorphism q 2 c)) / t
  have haf : definingFieldAutomorphism q 2 a = a :=
    star_central_div_fixed q s t ht htc ⟨_, hbn⟩
  refine ⟨a, haf, (starRankOne_eq_conjugate_of_scale q s t htc a haf v g c b hb hgv ?_).symm⟩
  dsimp only [a]
  field_simp [ht]

theorem projectiveHermitian_mem_pointRoot_iff (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0)
    (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) :
    projectiveHermitianStarHom q s t ht htc (Multiplicative.ofAdd A) ∈
      unitaryPointRoot q s (starPoint q s v hv) ↔
        A ∈ CFSGHermitianTwoByTwoRankOne.rankOneLine (definingFieldAutomorphism q 2)
          (fun z => extension_two_pow_twice q z) v := by
  obtain ⟨g, c, hc, hgv⟩ := exists_starVector_representative q s v hv
  rw [unitaryPointRoot_starPoint_representative q s v hv g c hc hgv,
    conjugateProjectiveCentralRootLine_cover]
  constructor
  · rintro ⟨z, ⟨u, hu, rfl⟩, he⟩
    obtain ⟨b, hb, rfl⟩ := (mem_naturalCentralRootLine_iff q (s + 1) u).mp hu
    obtain ⟨a, ha, hconj⟩ := exists_conjugateCentralFixed_starRankOne q s t ht htc v g c hgv b hb
    have hp : projectiveHermitianStarHom q s t ht htc
        (Multiplicative.ofAdd (CFSGHermitianTwoByTwoRankOne.rankOneParameter
          (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z) a ha v)) =
        projectiveHermitianStarHom q s t ht htc (Multiplicative.ofAdd A) := by
      change unitaryProjectiveCover q s (starFixed q s (starRankOneParameters q s t htc a ha v)) = _
      rw [← hconj]
      exact he
    have hA := congrArg Multiplicative.toAdd (projectiveHermitianStarHom_injective q s t ht htc hp)
    exact ⟨a, ha, hA.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, starRankOne_mem_conjugateRootLine q s t htc a ha v g c hc hgv, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
