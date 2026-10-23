import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Read additive coordinates of a finite coproduct from its literal
single-coordinate factors. The abstract group boundary avoids expanding
concrete matrix and quotient implementations during this calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteCoproductAdditiveCoordinates
variable {I K M G : Type*} [Fintype I] [DecidableEq I] [Ring K]
    [AddCommGroup M] [Module K M] [Group G]

theorem coproduct_coordinates (φ : G →* Multiplicative M)
    (f : I → Multiplicative K →* G)
    (hcomm : Pairwise (fun i j => ∀ a b, Commute (f i a) (f j b)))
    (X : I → M) (hcoordinate : ∀ i a, (φ (f i a)).toAdd = a.toAdd • X i)
    (c : I → Multiplicative K) :
    (φ (MonoidHom.noncommPiCoprod f hcomm c)).toAdd = ∑ i, (c i).toAdd • X i := by
  apply Pi.mulSingle_induction (fun c =>
    (φ (MonoidHom.noncommPiCoprod f hcomm c)).toAdd = ∑ i, (c i).toAdd • X i) c
  · simp only [map_one, toAdd_one, Pi.one_apply, zero_smul, Finset.sum_const_zero]
  · intro a b ha hb
    rw [map_mul, map_mul, toAdd_mul, ha, hb]
    simp only [Pi.mul_apply, toAdd_mul, add_smul, Finset.sum_add_distrib]
  · intro i t
    rw [MonoidHom.noncommPiCoprod_mulSingle, hcoordinate]
    have hsingle : (fun j => ((Pi.mulSingle i t : I → Multiplicative K) j).toAdd) =
        Pi.single i t.toAdd := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    change t.toAdd • X i = Fintype.linearCombination K X
      (fun j => ((Pi.mulSingle i t : I → Multiplicative K) j).toAdd)
    rw [hsingle, Fintype.linearCombination_apply_single]

end SymmetricSubgroupAsymptotics.CFSGFiniteCoproductAdditiveCoordinates
