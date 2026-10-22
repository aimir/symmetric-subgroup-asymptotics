import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalForm
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSL
import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular

/-! The literal three-block upper arrays are actual natural elementary
matrices after the displayed Fin reindex. Determinant1, upperness and
diagonal1 are proved on their actual entries, without a unitary group
identification or any source/derived membership assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
variable (K : Type) [Field K] (s : ℕ)

def naturalUpperUnit (w v : Fin (s + 1) → K) (b : K) : (Mat K (s + 2))ˣ :=
  Units.map (Matrix.reindexAlgEquiv K K (splitEquiv s)).toRingHom.toMonoidHom (upperUnit w v b)

theorem naturalUpperUnit_val (w v : Fin (s + 1) → K) (b : K) :
    (naturalUpperUnit K s w v b : Mat K (s + 2)) =
      Matrix.reindex (splitEquiv s) (splitEquiv s) (upperArray w v b) := rfl

theorem naturalUpperUnit_apply (w v : Fin (s + 1) → K) (b : K)
    (i j : Index (Fin (s + 1))) :
    (naturalUpperUnit K s w v b : Mat K (s + 2)) (splitEquiv s i) (splitEquiv s j) =
      upperArray w v b i j := by
  rw [naturalUpperUnit_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem naturalUpperUnit_det (w v : Fin (s + 1) → K) (b : K) :
    Matrix.det (naturalUpperUnit K s w v b : Mat K (s + 2)) = 1 := by
  rw [naturalUpperUnit_val, Matrix.det_reindex_self, upperArray_det]

theorem naturalUpperUnit_upper (w v : Fin (s + 1) → K) (b : K) :
    (naturalUpperUnit K s w v b : Mat K (s + 2)).BlockTriangular id := by
  intro i j hji
  obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
  obtain ⟨y, rfl⟩ := (splitEquiv s).surjective j
  rw [naturalUpperUnit_apply]
  change (splitIndex s y).val < (splitIndex s x).val at hji
  rcases x with u | (i | u) <;> rcases y with v | (j | v)
  all_goals try cases u
  all_goals try cases v
  all_goals simp only [splitIndex, Fin.val_zero, Fin.val_last] at hji
  all_goals try have hi := i.isLt
  all_goals try have hj := j.isLt
  all_goals try omega
  all_goals simp only [upperArray]
  split_ifs with he
  · subst j; omega
  · rfl

theorem naturalUpperUnit_diag (w v : Fin (s + 1) → K) (b : K) (i : Fin (s + 3)) :
    (naturalUpperUnit K s w v b : Mat K (s + 2)) i i = 1 := by
  obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
  rw [naturalUpperUnit_apply]
  rcases x with u | (i | u)
  all_goals simp only [upperArray, if_true]

def naturalUpperElement (w v : Fin (s + 1) → K) (b : K) : NaturalElementary K (s + 2) :=
  ⟨naturalUpperUnit K s w v b,
    unit_mem_natural_of_det K (s + 2) _ (naturalUpperUnit_det K s w v b)⟩

theorem naturalUpperElement_upper (w v : Fin (s + 1) → K) (b : K) :
    naturalToSpecialLinear K (s + 2) (naturalUpperElement K s w v b) ∈
      CFSGUpperUnitriangular.upperUnitriangular K (s + 3) :=
  ⟨naturalUpperUnit_upper K s w v b, naturalUpperUnit_diag K s w v b⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
