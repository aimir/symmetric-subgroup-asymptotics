import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors

/-! A genuine smaller D root word normalizes the singular tail while
fixing the same first positive vector. Rank-three tails use their literal
root definitions, without identifying them with another model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexFlagVectors
variable (K : Type) [Field K]

theorem exists_tail_normalize_singular (s : ℕ)
    (v : Index (s + 4) → K) (hn : v (Sum.inr 0) = 0)
    (ht : tailRestriction K (s + 3) v ≠ 0) (hs : splitQ K v = 0) :
    ∃ g : elementaryRootGroup K (s + 4),
      (g.val : Mat K (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      (g.val : Mat K (s + 4)) *ᵥ v = v (Sum.inl 0) • Pi.single (Sum.inl 0) 1 +
        Pi.single (Sum.inl (secondIndex s)) 1 := by
  have hs' : splitQ K (tailRestriction K (s + 3) v) = 0 :=
    (splitQ_tail_of_negative_head_zero K (s + 3) v hn).symm.trans hs
  obtain ⟨h, hh⟩ := exists_normalize_singular K (s + 1)
    (tailRestriction K (s + 3) v) ht hs'
  let g := tailElementaryHom K (s + 3) (by omega) h
  let w := (g.val : Mat K (s + 4)) *ᵥ v
  have hw : tailRestriction K (s + 3) w = Pi.single (Sum.inl 0) 1 :=
    (tailElementaryHom_tail_action K (s + 3) (by omega) h v).trans hh
  have hwn : w (Sum.inr 0) = 0 :=
    (tailElementaryHom_head_negative K (s + 3) (by omega) h v).trans hn
  have hwp : w (Sum.inl 0) = v (Sum.inl 0) :=
    tailElementaryHom_head_positive K (s + 3) (by omega) h v
  refine ⟨g, tailElementaryHom_fixes_first_positive K (s + 3) (by omega) h, ?_⟩
  have he := vector_eq_first_add_tail_basis K (s + 2) w hw hwn
  rw [hwp] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
