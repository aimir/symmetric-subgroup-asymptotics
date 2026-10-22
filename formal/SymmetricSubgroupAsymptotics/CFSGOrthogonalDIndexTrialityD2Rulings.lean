import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingExhaustion
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingIntersection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingParameters
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! Complete original residual D2 ruling coordinates: the ACTUAL
quadratic singular planes are exactly two disjoint copies of PG(1,K),
each with q+1 members over a finite field. This is the explicit local
quadratic input needed for D4 triality, not an assumed building. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

abbrev ResidualSingularPlanes := {P : Submodule K (Index 2 → K) //
  Module.finrank K P = 2 ∧ ∀ x ∈ P, splitQuadraticForm K 2 x = 0}
abbrev RulingParameters := ℙ K (Fin 2 → K)

def columnRuling (p : RulingParameters K) : ResidualSingularPlanes K :=
  ⟨originalColumnPlane K p.rep, originalColumnPlane_finrank K p.rep p.rep_nonzero,
    originalColumnPlane_singular K p.rep⟩

def rowRuling (p : RulingParameters K) : ResidualSingularPlanes K :=
  ⟨originalRowPlane K p.rep, originalRowPlane_finrank K p.rep p.rep_nonzero,
    originalRowPlane_singular K p.rep⟩

theorem columnRuling_injective : Function.Injective (columnRuling K) := by
  intro p q he
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_eq, Projectivization.submodule_eq]
  exact (originalColumnPlane_eq_iff_factor_line_eq K p.rep q.rep).mp (congrArg Subtype.val he)

theorem rowRuling_injective : Function.Injective (rowRuling K) := by
  intro p q he
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_eq, Projectivization.submodule_eq]
  exact (originalRowPlane_eq_iff_factor_line_eq K p.rep q.rep).mp (congrArg Subtype.val he)

theorem columnRuling_ne_rowRuling (p q : RulingParameters K) : columnRuling K p ≠ rowRuling K q := by
  intro he
  exact originalColumnPlane_ne_originalRowPlane K p.rep q.rep p.rep_nonzero q.rep_nonzero
    (congrArg Subtype.val he)

def rulingPlane : RulingParameters K ⊕ RulingParameters K → ResidualSingularPlanes K :=
  Sum.elim (columnRuling K) (rowRuling K)

theorem rulingPlane_injective : Function.Injective (rulingPlane K) := by
  intro p q he
  rcases p with p | p <;> rcases q with q | q
  · exact congrArg Sum.inl (columnRuling_injective K he)
  · exact False.elim (columnRuling_ne_rowRuling K p q he)
  · exact False.elim (columnRuling_ne_rowRuling K q p he.symm)
  · exact congrArg Sum.inr (rowRuling_injective K he)

theorem rulingPlane_surjective : Function.Surjective (rulingPlane K) := by
  intro P
  rcases original_singular_plane_ruling K P.val P.property.1 P.property.2 with
    ⟨u, hu, hP⟩ | ⟨v, hv, hP⟩
  · let p : RulingParameters K := Projectivization.mk K u hu
    refine ⟨Sum.inl p, ?_⟩
    apply Subtype.ext
    change originalColumnPlane K p.rep = P.val
    apply Eq.trans _ hP.symm
    apply (originalColumnPlane_eq_iff_factor_line_eq K p.rep u).mpr
    exact (Projectivization.submodule_eq p).symm.trans (Projectivization.submodule_mk (K := K) u hu)
  · let p : RulingParameters K := Projectivization.mk K v hv
    refine ⟨Sum.inr p, ?_⟩
    apply Subtype.ext
    change originalRowPlane K p.rep = P.val
    apply Eq.trans _ hP.symm
    apply (originalRowPlane_eq_iff_factor_line_eq K p.rep v).mpr
    exact (Projectivization.submodule_eq p).symm.trans (Projectivization.submodule_mk (K := K) v hv)

def rulingEquiv : RulingParameters K ⊕ RulingParameters K ≃ ResidualSingularPlanes K :=
  Equiv.ofBijective (rulingPlane K) ⟨rulingPlane_injective K, rulingPlane_surjective K⟩

theorem rulingParameter_card [Finite K] : Nat.card (RulingParameters K) = Nat.card K + 1 :=
  Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)

theorem columnRuling_range_card [Finite K] :
    Nat.card (Set.range (columnRuling K)) = Nat.card K + 1 :=
  (Nat.card_range_of_injective (columnRuling_injective K)).trans (rulingParameter_card K)

theorem rowRuling_range_card [Finite K] :
    Nat.card (Set.range (rowRuling K)) = Nat.card K + 1 :=
  (Nat.card_range_of_injective (rowRuling_injective K)).trans (rulingParameter_card K)

theorem residualSingularPlane_card [Finite K] :
    Nat.card (ResidualSingularPlanes K) = 2 * (Nat.card K + 1) := by
  rw [Nat.card_congr (rulingEquiv K).symm, Nat.card_sum, rulingParameter_card]
  ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
