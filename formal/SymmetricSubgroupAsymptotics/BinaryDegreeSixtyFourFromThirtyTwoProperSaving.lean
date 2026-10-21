import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineUniformSeven
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankTenUniformSix
import SymmetricSubgroupAsymptotics.BinaryNormalDegreeRecurrence
import SymmetricSubgroupAsymptotics.SurjectiveRepresentationGeneratorTransport

/-! The exact degree-sixty-four step reduces to proper-normal saving at
its actual thirty-two-point top. The original normal intersection and
image remain unchanged. This is an internal reduction, not a new input
for the published boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 32))

private theorem normalGen_le_uniform_original_top
    (c : ℕ)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 32)) c)
    (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ c + MarkedC4.normalGen (N.map F.top.rangeRestrict) := by
  letI : MulAction U (Fin 32) := MulAction.compHom (Fin 32) F.top
  have hact : ∀ (u : U) (i : Fin 32), u • i = F.top u i := fun _ _ => rfl
  have hpull := UniformSubrepresentationGeneratorBound.comp_of_surjective
    (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 32))
    F.top.rangeRestrict F.top.rangeRestrict_surjective hu
  have he : (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 32)).comp
      F.top.rangeRestrict = permutationFunctionRepresentation (ZMod 2) U (Fin 32) := by
    apply MonoidHom.ext
    intro u
    apply LinearMap.ext
    intro v
    funext i
    change v ((F.top u)⁻¹ i) = v (F.top (u⁻¹) i)
    rw [map_inv]
  rw [he] at hpull
  exact F.normalGen_le_uniform_add_actual_top hact c hpull N

/-- Only the actual top's proper-normal rank-nine saving is needed here.
It will be supplied by the unconditional degree-thirty-two proof. -/
theorem normalGen_le_sixteen_of_actual_top_proper_saving
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hsaving : ∀ D : Subgroup F.top.range, D.Normal → D ≠ ⊤ →
      9 ≤ MarkedC4.normalGen D → 10 ≤ MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal] : MarkedC4.normalGen N ≤ 16 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive F.top.range (Fin 32) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  let D := N.map F.top.rangeRestrict
  letI : D.Normal := Subgroup.Normal.map inferInstance F.top.rangeRestrict F.top.rangeRestrict_surjective
  have hDbound : MarkedC4.normalGen D ≤ 10 := by
    simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two
      F.top.range hTop D
  by_cases hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 32)
  · letI : MulAction U (Fin 32) := MulAction.compHom (Fin 32) F.top
    have hact : ∀ (u : U) (i : Fin 32), u • i = F.top u i := fun _ _ => rfl
    letI : MulAction.IsPretransitive U (Fin 32) := ⟨fun i j => by
      obtain ⟨t,ht⟩ := MulAction.exists_smul_eq F.top.range i j
      obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
      exact ⟨u,ht⟩⟩
    have hel' : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 32) := by
      intro u i
      have ht := hel (F.top.rangeRestrict u) i
      change F.top (u ^ 2) i = i
      rw [map_pow]
      exact ht
    have hb := F.normalGen_le_middle_add_exponent_of_elementary_top hact hU hel'
      (0 : Fin 32) 5 (by norm_num only [Nat.card_fin]) N
    norm_num [Nat.choose] at hb
    omega
  · obtain ⟨E⟩ := transitiveBinaryPairFrame_nonempty 4 F.top.range hTop
      (by norm_num only [Nat.card_fin])
    by_cases hten : 10 ≤ MarkedC4.genRank F.top.range
    · have hu := E.uniform_generatedBy_six_of_rank_ten hTop hten
      have hb := F.normalGen_le_uniform_original_top 6 hu N
      change MarkedC4.normalGen N ≤ 6 + MarkedC4.normalGen D at hb
      omega
    by_cases hnine : 9 ≤ MarkedC4.genRank F.top.range
    · have hu := E.uniform_generatedBy_seven_of_rank_nine hTop hnine
      have hD : MarkedC4.normalGen D ≤ 9 := by
        by_cases he : D = ⊤
        · rw [he,MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank]
          omega
        · by_contra h
          exact hten (hsaving D inferInstance he (by omega))
      have hb := F.normalGen_le_uniform_original_top 7 hu N
      change MarkedC4.normalGen N ≤ 7 + MarkedC4.normalGen D at hb
      omega
    · have hu := twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary hTop hel
      have hD : MarkedC4.normalGen D ≤ 8 := by
        by_cases he : D = ⊤
        · rw [he,MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank]
          omega
        · by_contra h
          exact hten (hsaving D inferInstance he (by omega))
      have hb := F.normalGen_le_uniform_original_top 8
        (by simpa only [Nat.card_fin] using hu) N
      change MarkedC4.normalGen N ≤ 8 + MarkedC4.normalGen D at hb
      omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
