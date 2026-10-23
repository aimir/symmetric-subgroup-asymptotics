import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoProjectiveNormalizer

/-! The full normalizer of the literal rank-two upper Sylow is its
actual triangular flag subgroup. The reverse inclusion uses only the
fact that every defining-prime subgroup of triangular matrices has
diagonal one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwo_pGroup_flag_le_upper (q : CFSG.PrimePower)
    (R : Subgroup (naturalFixed 2 q)) (hR : IsPGroup q.prime R)
    (hRB : R ≤ rankTwoUpperFlag q) : R ≤ rankTwoUpperSubgroup q := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  let rho : R →* Mat (q.Extension 2) 2 :=
    (Units.coeHom _).comp ((fixedMatrixHom q 2).comp R.subtype)
  have hu (x : R) : (rho x).BlockTriangular id :=
    (rankTwoUpperFlag_mem_iff q x.val).mp (hRB x.property)
  intro x hx
  have hd (i : Fin 3) : (x.val.val : Mat (q.Extension 2) 2) i i = 1 :=
    CFSGTwistedA2UnipotentArrays.pGroup_upper_diagonal_one q.prime hR rho hu ⟨x, hx⟩ i
  exact ⟨⟨hu ⟨x, hx⟩, hd⟩, x.property⟩

theorem rankTwo_flag_conjugate_upper_le (q : CFSG.PrimePower)
    (b : naturalFixed 2 q) (hb : b ∈ rankTwoUpperFlag q) :
    (rankTwoUpperSubgroup q).map (MulAut.conj b).toMonoidHom ≤ rankTwoUpperSubgroup q := by
  apply rankTwo_pGroup_flag_le_upper q _ ((rankTwoUpperSubgroup_isPGroup q).map _)
  rintro _ ⟨u, hu, rfl⟩
  exact (rankTwoUpperFlag q).mul_mem
    ((rankTwoUpperFlag q).mul_mem hb (rankTwoUpperSubgroup_le_flag q hu))
    ((rankTwoUpperFlag q).inv_mem hb)

theorem rankTwo_natural_normalizer_eq_flag (q : CFSG.PrimePower) :
    Subgroup.normalizer (rankTwoUpperSubgroup q : Set _) = rankTwoUpperFlag q := by
  apply le_antisymm
  · intro g hg
    exact (rankTwoUpperFlag_mem_iff q g).mpr (rankTwo_natural_normalizer_upper q g hg)
  · intro b hb
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    change (((rankTwoUpperSubgroup q).map (MulAut.conj b).toMonoidHom :
      Subgroup (naturalFixed 2 q)) : Set (naturalFixed 2 q)) = (rankTwoUpperSubgroup q : Set _)
    apply congrArg (fun R : Subgroup (naturalFixed 2 q) => (R : Set (naturalFixed 2 q)))
    apply le_antisymm (rankTwo_flag_conjugate_upper_le q b hb)
    intro x hx
    have hy : b⁻¹ * x * b ∈ rankTwoUpperSubgroup q :=
      rankTwo_flag_conjugate_upper_le q b⁻¹ ((rankTwoUpperFlag q).inv_mem hb)
        ⟨x, hx, rfl⟩
    refine ⟨b⁻¹ * x * b, hy, ?_⟩
    change b * (b⁻¹ * x * b) * b⁻¹ = x
    group

theorem rankTwo_projective_normalizer_eq_flag (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Subgroup.normalizer ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) : Set _) =
      (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq) := by
  rw [← rankTwo_projective_normalizer_map, rankTwo_natural_normalizer_eq_flag]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
