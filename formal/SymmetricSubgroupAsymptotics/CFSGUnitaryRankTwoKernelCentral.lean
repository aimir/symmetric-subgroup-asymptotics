import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCentralUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalGeneration
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-! The kernel of the same natural cover of the original unitary
central quotient is central in the actual natural fixed group. Literal
upper and opposite generation, with unipotent scalar rigidity, proves
this rather than assuming a named-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwo_kernel_commutes_upper (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (g : naturalFixed 2 q) (hg : g ∈ (rankTwoProjectiveCover q hq).ker)
    (u : naturalUnipotent 2 q) : g.val * u.val = u.val * g.val := by
  have hz : rankTwoDerivedCover q hq g ∈ Subgroup.center (commutator (Fixed 2 q)) :=
    (QuotientGroup.eq_one_iff _).mp hg
  have hh := rankTwo_central_cover_conjugates_upper q hq g hz u
  exact (mul_inv_eq_iff_eq_mul).mp hh

theorem rankTwoProjectiveCover_kernel_central (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoProjectiveCover q hq).ker ≤ Subgroup.center (naturalFixed 2 q) := by
  intro g hg
  let C := Subgroup.centralizer ({g.val} : Set (NaturalElementary (q.Extension 2) 2))
  have hU : naturalUnipotent 2 q ≤ C := by
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (rankTwo_kernel_commutes_upper q hq g hg ⟨u, hu⟩).symm
  have hV : oppositeNaturalUnipotent q 2 ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    let w := reversalFixed q 2
    let k : naturalFixed 2 q := w⁻¹ * g * w
    have hk : k ∈ (rankTwoProjectiveCover q hq).ker := by
      change rankTwoProjectiveCover q hq (w⁻¹ * g * w) = 1
      simp only [map_mul, map_inv, show rankTwoProjectiveCover q hq g = 1 from hg,
        mul_one, inv_mul_cancel]
    have hc := rankTwo_kernel_commutes_upper q hq k hk ⟨u, hu⟩
    change (w.val⁻¹ * g.val * w.val) * u = u * (w.val⁻¹ * g.val * w.val) at hc
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change (w.val * u * w.val⁻¹) * g.val = g.val * (w.val * u * w.val⁻¹)
    calc
      _ = w.val * (u * (w.val⁻¹ * g.val * w.val)) * w.val⁻¹ := by group
      _ = w.val * ((w.val⁻¹ * g.val * w.val) * u) * w.val⁻¹ := by rw [hc]
      _ = _ := by group
  have hle : naturalUpperOppositeJoin q 2 ≤ C := sup_le hU hV
  apply Subgroup.mem_center_iff.mpr
  intro x
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle (rank_two_mem_join q x)))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
