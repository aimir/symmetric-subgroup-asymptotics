import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBruhatUniqueness
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOpposition

/-! Opposition reverses the actual native complete flag. Thus the actual
positive unipotent group has trivial intersection with the opposed original
Borel. This is matrix geometry, without any simplicity or Bruhat assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOpposedFlagIntersection
open CFSGGTwoSerreMatrices CFSGGTwoNaturalBruhatFlag CFSGGTwoLongestWeylMonomial
open CFSGTypeAMonomialMatrices CFSGMatrixFlagSubgroups
open CFSGGTwoOriginalBruhatUniqueness CFSGReeGTwoOriginalOpposition
open CFSGGTwoPositiveWordSubgroup CFSGGTwoOriginalBorel
variable (K : Type) [Field K]

private theorem monomial_mul_entry (sigma : Equiv.Perm Index) (d : Index → K)
    (M : Mat K) (i j : Index) :
    (monomial sigma d*M) i j=d i*M (sigma i) j := by
  simp only [Matrix.mul_apply,monomial_apply]
  rw [Finset.sum_eq_single (sigma i)]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro hk
    exact False.elim (hk (Finset.mem_univ _))

private theorem mul_monomial_entry (sigma : Equiv.Perm Index) (d : Index → K)
    (M : Mat K) (i j : Index) :
    (M*monomial sigma d) i j=M i (sigma.symm j)*d (sigma.symm j) := by
  simp only [Matrix.mul_apply,monomial_apply]
  rw [Finset.sum_eq_single (sigma.symm j)]
  · simp
  · intro k _ hk
    have hne : sigma k≠j := by
      intro h
      exact hk (sigma.injective (h.trans (sigma.apply_symm_apply j).symm))
    simp [hne]
  · intro hk
    exact False.elim (hk (Finset.mem_univ _))

theorem opposed_entry (M : (Mat K)ˣ) (i j : Index) :
    (↑(longestUnit K*M*(longestUnit K)⁻¹) : Mat K) i j=
      (M : Mat K) (oppositePermutation i) (oppositePermutation j) := by
  have hi : (longestUnit K)⁻¹=longestUnit K :=
    inv_eq_of_mul_eq_one_right (longestUnit_square K)
  rw [hi]
  change (((longestUnit K : Mat K)*(M : Mat K))*(longestUnit K : Mat K)) i j=_
  rw [longestUnit_val,mul_monomial_entry,monomial_mul_entry]
  have hs : oppositePermutation.symm j=oppositePermutation j := by cases j <;> rfl
  rw [hs]
  ring

theorem opposite_order (i j : Index) :
    coordinateOrder (oppositePermutation j)<coordinateOrder (oppositePermutation i) ↔
      coordinateOrder i<coordinateOrder j := by
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem unipotent_opposed_upper_eq_one (M : (Mat K)ˣ)
    (hM : M∈unipotentUnits coordinateOrder)
    (hOpp : longestUnit K*M*(longestUnit K)⁻¹∈flagBorel K) : M=1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    exact (hM.2 i).trans (Matrix.one_apply_eq i).symm
  · have hne : coordinateOrder i≠coordinateOrder j := coordinateOrder.injective.ne h
    have hz : (M : Mat K) i j=0 := by
      rcases lt_or_gt_of_ne hne with hij | hij
      · have ho := hOpp ((opposite_order i j).mpr hij)
        rw [opposed_entry] at ho
        have oi : oppositePermutation (oppositePermutation i)=i := by cases i <;> rfl
        have oj : oppositePermutation (oppositePermutation j)=j := by cases j <;> rfl
        simpa only [oi,oj] using ho
      · exact hM.1 hij
    change (M : Mat K) i j=(1 : Mat K) i j
    simpa only [Matrix.one_apply,if_neg h] using hz

theorem nativeHom_longestWord : nativeHom K (longestWord K)=longestUnit K :=
  longestWord_native K

variable [CharP K 3]

theorem original_opposed_positive_intersection
    (u : CFSG.Models.Chevalley.Model CartanMatrix.G₂ K)
    (hu : u∈positiveWordGroup K)
    (hb : longestWord K*u*(longestWord K)⁻¹∈borel K) : u=1 := by
  apply nativeHom_injective K
  rw [map_one]
  apply unipotent_opposed_upper_eq_one K (nativeHom K u)
    (native_positive_unipotent K u hu)
  have h := native_borel_upper K _ hb
  simpa only [map_mul,map_inv,nativeHom_longestWord] using h

end SymmetricSubgroupAsymptotics.CFSGGTwoOpposedFlagIntersection
