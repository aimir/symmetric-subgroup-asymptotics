import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingPlane

/-! Nondegenerate alternating spaces have even dimension in every
characteristic, by repeatedly splitting off the actual two-plane of a
nonzero pairing. This is a proved linear-algebra prerequisite, not an
assumed component invariant for the D model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u v
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingEvenDimension
open CFSGOrthogonalDIndexAlternatingPlane
variable (K : Type u) [Field K]

private theorem even_finrank_aux (n : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      Module.finrank K V = n → ∀ B : LinearMap.BilinForm K V,
        B.IsAlt → B.Nondegenerate → Even n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ hn B hAlt hB
    by_cases hz : n = 0
    · exact ⟨0, by omega⟩
    · letI : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have hy : ¬ ∀ y : V, B x y = 0 := fun h => hx (hB.1 x h)
      obtain ⟨y, hxy⟩ := not_forall.mp hy
      let P := (planeMap (K := K) x y).range
      let W := B.orthogonal P
      have hP : (B.restrict P).Nondegenerate := plane_restrict_nondegenerate B hAlt x y hxy
      have hPdim : Module.finrank K P = 2 := plane_range_finrank B hAlt x y hxy
      have hcomp : IsCompl P W := B.isCompl_orthogonal_of_restrict_nondegenerate hAlt.isRefl hP
      have hdouble : B.orthogonal W = P := B.orthogonal_orthogonal hB hAlt.isRefl P
      have hWcomp : IsCompl W (B.orthogonal W) := by
        rw [hdouble]
        exact hcomp.symm
      have hW : (B.restrict W).Nondegenerate :=
        (B.restrict_nondegenerate_iff_isCompl_orthogonal hAlt.isRefl).mpr hWcomp
      have hWalt : (B.restrict W).IsAlt := fun w => hAlt w.val
      have hdim := Submodule.finrank_add_eq_of_isCompl hcomp
      rw [hPdim, hn] at hdim
      have hlt : Module.finrank K W < n := by omega
      obtain ⟨a, ha⟩ := ih (Module.finrank K W) hlt W rfl (B.restrict W) hWalt hW
      exact ⟨a + 1, by omega⟩

theorem even_finrank_of_nondegenerate {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    (hB : B.Nondegenerate) : Even (Module.finrank K V) :=
  even_finrank_aux K (Module.finrank K V) V rfl B hAlt hB

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingEvenDimension
