import SymmetricSubgroupAsymptotics.CFSGOddRotationBinaryFrames
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerGeneration

/-! Odd rotation gives an actual abelian subgroup whose two conjugates
generate the original group. No power of the Bray element, finiteness,
classification, intravariance or self-normalization is assumed or claimed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOddRotationAbelianPairs

open CFSGCommutingBinaryFrameGeneration CFSGOddRotationBinaryFrames

variable {G : Type*} [Group G]

def subgroup (a b : G) (m : ℕ) : Subgroup G :=
  Subgroup.closure (Set.range (pair a (brayElement a b m)))

theorem subgroup_abelian (a b : G) (m : ℕ) (ha : a ^ 2 = 1)
    (hr : (a * (b⁻¹ * a * b)) ^ (2 * m + 1) = 1) :
    IsMulCommutative (subgroup a b m) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  cases i <;> cases j
  · exact rfl
  · exact (bray_commute a b m ha hr).eq
  · exact (bray_commute a b m ha hr).symm.eq
  · exact rfl

theorem subgroup_soluble (a b : G) (m : ℕ) (ha : a ^ 2 = 1)
    (hr : (a * (b⁻¹ * a * b)) ^ (2 * m + 1) = 1) :
    IsSolvable (subgroup a b m) :=
  isSolvable_of_comm (subgroup_abelian a b m ha hr).is_comm.comm

theorem conjugates_generate (a b : G) (m : ℕ)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Subgroup.closure ((subgroup a b m : Set G) ∪
      (subgroup a b m).map (MulAut.conj b⁻¹).toMonoidHom) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  exact join_eq_top a b m hgen

theorem soluble_pair (a b : G) (m : ℕ) (ha : a ^ 2 = 1)
    (hr : (a * (b⁻¹ * a * b)) ^ (2 * m + 1) = 1)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    ∃ (U : Subgroup G) (g : G), IsSolvable U ∧
      Subgroup.closure ((U : Set G) ∪ U.map (MulAut.conj g).toMonoidHom) = ⊤ :=
  ⟨subgroup a b m, b⁻¹, subgroup_soluble a b m ha hr,
    conjugates_generate a b m hgen⟩

theorem soluble_one_extra (a b : G) (m : ℕ) (ha : a ^ 2 = 1)
    (hr : (a * (b⁻¹ * a * b)) ^ (2 * m + 1) = 1)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    ∃ (U : Subgroup G) (g : G), IsSolvable U ∧
      Subgroup.closure (({g} : Set G) ∪ U) = ⊤ := by
  refine ⟨subgroup a b m, b⁻¹, subgroup_soluble a b m ha hr, ?_⟩
  exact CFSGReduction.one_extra_generator_of_two_conjugates _ _
    (conjugates_generate a b m hgen)

end SymmetricSubgroupAsymptotics.CFSGOddRotationAbelianPairs
