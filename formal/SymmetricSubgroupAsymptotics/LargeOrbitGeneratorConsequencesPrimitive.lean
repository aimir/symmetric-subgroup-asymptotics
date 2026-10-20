import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesShapes
import SymmetricSubgroupAsymptotics.C1PrimitiveTail
import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthTransport
import SymmetricSubgroupAsymptotics.PermutationSectionNormalGenerators

/-! Ordinary generator bounds for the actual kernel supported on a primitive
head orbit.  Its image is normal in the actual primitive permutation image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
open MarkedC4

variable {X : Type} [Fintype X]

theorem genRank_le_groupRank (G : Type) [Group G] [Finite G] :
    genRank G ≤ Group.rank G := by
  obtain ⟨S, hcard, hgen⟩ := Group.rank_spec G
  exact (genRank_le hgen).trans_eq hcard

/-- Relabel the original primitive point action, and transport its actual
normal subgroup rather than introducing a new action on a quotient. -/
theorem primitiveNormal_genRank_bound
    (hgen : PrimitiveNormalGeneratorInput)
    (U : Subgroup (Equiv.Perm X))
    (hprimitive : MulAction.IsPreprimitive U X)
    (N : Subgroup U) [N.Normal]
    (hr : 4 ≤ Fintype.card X) : genRank N ≤ Nat.log2 (Fintype.card X) := by
  let r := Fintype.card X
  let e := Fintype.equivFin X
  let V := PrimitiveCompositionLengthInput.relabelGroup r e U
  let g : U ≃* V := PrimitiveCompositionLengthInput.relabelGroupEquiv r e U
  let f : X →ₑ[g] Fin r :=
    { toFun := e
      map_smul' := by
        intro u x
        change e (u.1 x) = e (u.1 (e.symm (e x)))
        rw [e.symm_apply_apply] }
  have hV : MulAction.IsPreprimitive V (Fin r) :=
    (MulAction.isPreprimitive_congr g.surjective
      (show Function.Bijective f from e.bijective)).mp hprimitive
  let M := N.map g.toMonoidHom
  letI : M.Normal := (inferInstance : N.Normal).map g.toMonoidHom g.surjective
  have hbound := hgen r hr V hV M inferInstance
  have hcongr : Group.rank N = Group.rank M :=
    Group.rank_congr (g.subgroupMap N)
  have hrank : Group.rank N ≤ Nat.log2 r := by
    rw [hcongr]
    exact hbound
  exact (genRank_le_groupRank N).trans hrank

/-- The two small primitive degrees need no published input. -/
theorem smallPermutationNormal_genRank_bound
    (U : Subgroup (Equiv.Perm X)) (N : Subgroup U)
    (hr : Fintype.card X ≤ 3) : genRank N ≤ 3 := by
  have hinj : Function.Injective (fun n : N => ((n : U) : Equiv.Perm X)) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hc : Nat.card N ≤ 2 ^ 3 := by
    calc
      Nat.card N ≤ Nat.card (Equiv.Perm X) :=
        Nat.card_le_card_of_injective _ hinj
      _ = (Fintype.card X).factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card]
      _ ≤ (3 : ℕ).factorial := Nat.factorial_le hr
      _ ≤ 2 ^ 3 := by norm_num
  obtain ⟨S, hS, hpow⟩ := exists_generating_finset_two_pow_le N
  have hs : S.card ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hpow.trans hc)
  exact (genRank_le hS).trans hs

/-- A uniform loose primitive-head cost accommodates degrees two and three. -/
theorem primitiveNormal_genRank_bound_all
    (hgen : PrimitiveNormalGeneratorInput)
    (U : Subgroup (Equiv.Perm X))
    (hprimitive : MulAction.IsPreprimitive U X)
    (N : Subgroup U) [N.Normal]
    (hr : 2 ≤ Fintype.card X) :
    genRank N ≤ Nat.log2 (Fintype.card X) + 2 := by
  by_cases hlarge : 4 ≤ Fintype.card X
  · exact (primitiveNormal_genRank_bound hgen U hprimitive N hlarge).trans (by omega)
  · have hlog : 1 ≤ Nat.log2 (Fintype.card X) := by
      rw [Nat.log2_eq_log_two]
      exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega)).mpr (by simpa using hr)
    exact (smallPermutationNormal_genRank_bound U N (by omega)).trans (by omega)

/-- The ordinary kernel rank adds to that of the actual image. -/
theorem genRank_le_kernel_add_range
    {G R : Type} [Group G] [Finite G] [Group R]
    (f : G →* R) : genRank G ≤ genRank f.ker + genRank f.range := by
  letI : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let e := QuotientGroup.quotientKerEquivRange f
  have hq : genRank (G ⧸ f.ker) ≤ genRank f.range :=
    genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact (genRank_le_of_normal f.ker).trans (Nat.add_le_add_left hq _)

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
