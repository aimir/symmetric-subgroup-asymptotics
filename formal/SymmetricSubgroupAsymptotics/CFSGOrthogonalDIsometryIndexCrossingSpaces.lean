import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailLinearExtension
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents

/-! Literal one-pair-crossed maximal singular spaces. Their dimensions,
quadratic zero, and distance ONE from the original positive space are
proved in actual coordinates in all characteristics. No component label
is substituted for a subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCrossingSpaces
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexTailCoordinates CFSGOrthogonalDIndexSingularComponents
variable (K : Type) [Field K]

def crossingSpace (r : ℕ) (j : Fin r) : Submodule K (Index r → K) where
  carrier := {v | v (Sum.inl j) = 0 ∧ ∀ i : Fin r, i ≠ j → v (Sum.inr i) = 0}
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  add_mem' {v w} hv hw := ⟨by simp only [Pi.add_apply, hv.1, hw.1, add_zero],
    fun i hi => by simp only [Pi.add_apply, hv.2 i hi, hw.2 i hi, add_zero]⟩
  smul_mem' c {v} hv := ⟨by simp only [Pi.smul_apply, smul_eq_mul, hv.1, mul_zero],
    fun i hi => by simp only [Pi.smul_apply, smul_eq_mul, hv.2 i hi, mul_zero]⟩

def crossingCoordinates (r : ℕ) (j : Fin r) : (Fin r → K) ≃ₗ[K] crossingSpace K r j where
  toFun x := ⟨Sum.elim (fun i => if i = j then 0 else x i)
    (fun i => if i = j then x i else 0), by
      refine ⟨?_, ?_⟩
      · exact if_pos rfl
      · intro i hi
        exact if_neg hi⟩
  invFun v i := if i = j then v.val (Sum.inr i) else v.val (Sum.inl i)
  left_inv x := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  right_inv v := by
    apply Subtype.ext
    funext i
    rcases i with i | i
    · by_cases hi : i = j
      · subst i; simp only [Sum.elim_inl, v.property.1, if_true]
      · simp only [Sum.elim_inl, if_neg hi]
    · by_cases hi : i = j
      · simp only [Sum.elim_inr, if_pos hi]
      · simp only [Sum.elim_inr, if_neg hi, v.property.2 i hi]
  map_add' x y := by
    apply Subtype.ext
    funext i
    rcases i with i | i <;> by_cases hi : i = j <;> simp [hi]
  map_smul' c x := by
    apply Subtype.ext
    funext i
    rcases i with i | i <;> by_cases hi : i = j <;> simp [hi]

theorem crossingSpace_finrank (r : ℕ) (j : Fin r) :
    Module.finrank K (crossingSpace K r j) = r := by
  simpa using (crossingCoordinates K r j).finrank_eq.symm

theorem crossingSpace_singular (r : ℕ) (j : Fin r)
    (v : Index r → K) (hv : v ∈ crossingSpace K r j) : splitQuadraticForm K r v = 0 := by
  rw [splitQuadraticForm_apply]
  change (∑ i : Fin r, v (Sum.inl i) * v (Sum.inr i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = j
  · subst i
    rw [hv.1, zero_mul]
  · rw [hv.2 i hi, mul_zero]

theorem crossing_distance_one (r : ℕ) (j : Fin r) :
    distance r (positiveSpace K r) (crossingSpace K r j) = 1 := by
  let P := positiveSpace K r
  let f : P →ₗ[K] K := (LinearMap.proj (Sum.inl j)).comp P.subtype
  have hf : Function.Surjective f := by
    intro a
    refine ⟨positiveEquiv K r (Pi.single j a), ?_⟩
    change (Pi.single j a : Fin r → K) j = a
    simp only [Pi.single_apply, if_true]
  have hk : f.ker.map P.subtype = P ⊓ crossingSpace K r j := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_, fun i _ => x.property i⟩
      exact hx
    · rintro ⟨hv, hc⟩
      exact ⟨⟨v, hv⟩, hc.1, rfl⟩
  have hi : Module.finrank K (P ⊓ crossingSpace K r j : Submodule K (Index r → K)) =
      Module.finrank K f.ker :=
    (congrArg (fun T : Submodule K (Index r → K) => Module.finrank K T) hk).symm.trans
      (Submodule.finrank_map_subtype_eq P f.ker)
  have hr : Module.finrank K f.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
    exact Module.finrank_self K
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, positiveSpace_finrank, ← hi] at hd
  change r - Module.finrank K (P ⊓ crossingSpace K r j : Submodule K (Index r → K)) = 1
  omega

theorem positive_of_tail (n : ℕ) (v : Index (n + 1) → K)
    (hn : v (Sum.inr 0) = 0) (ht : tailRestrictionLinear K n v ∈ positiveSpace K n) :
    v ∈ positiveSpace K (n + 1) := by
  intro i
  refine Fin.cases hn (fun j => ht j) i

theorem crossing_of_tail (n : ℕ) (j : Fin n) (v : Index (n + 1) → K)
    (hn : v (Sum.inr 0) = 0) (ht : tailRestrictionLinear K n v ∈ crossingSpace K n j) :
    v ∈ crossingSpace K (n + 1) j.succ := by
  refine ⟨ht.1, ?_⟩
  intro i
  refine Fin.cases (fun _ => hn) (fun k hik => ?_) i
  exact ht.2 k (fun h => hik (congrArg Fin.succ h))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCrossingSpaces
