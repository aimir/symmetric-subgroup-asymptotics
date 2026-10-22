import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleAction

/-! The literal two-step array subgroup and its actual additive vector
quotient. The middle action and quotient map are proved on matrices;
no normalizer, derived or unitary-group conclusion is postulated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

def arrayGroup : Subgroup (Matrix (Index J) (Index J) K)ˣ where
  carrier := {u | ∃ w v : J → K, ∃ b : K, u = upperUnit w v b}
  one_mem' := ⟨0, 0, 0, Units.ext upperArray_zero.symm⟩
  mul_mem' := by
    rintro u v ⟨w, x, b, rfl⟩ ⟨w', x', b', rfl⟩
    exact ⟨w + w', x + x', b + b' + dotProduct w x', upperUnit_mul _ _ _ _ _ _⟩
  inv_mem' := by
    rintro u ⟨w, v, b, rfl⟩
    exact ⟨-w, -v, -b + dotProduct w v, upperUnit_inv _ _ _⟩

def vectorParameterHom : arrayGroup (K := K) (J := J) →* Multiplicative (J → K) where
  toFun u := Multiplicative.ofAdd (fun i =>
    (u.val : Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inr ())))
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext i
    simp
  map_mul' u v := by
    obtain ⟨w, x, b, hu⟩ := u.property
    obtain ⟨w', x', b', hv⟩ := v.property
    change Multiplicative.ofAdd (fun i =>
      ((u.val * v.val : (Matrix (Index J) (Index J) K)ˣ) : Matrix (Index J) (Index J) K)
        (.inr (.inl i)) (.inr (.inr ()))) =
      Multiplicative.ofAdd ((fun i => (u.val : Matrix (Index J) (Index J) K)
        (.inr (.inl i)) (.inr (.inr ()))) +
        (fun i => (v.val : Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inr ()))))
    rw [hu, hv, upperUnit_mul]
    rfl

theorem vectorParameterHom_upper (w v : J → K) (b : K) :
    vectorParameterHom (⟨upperUnit w v b, ⟨w, v, b, rfl⟩⟩ : arrayGroup) =
      Multiplicative.ofAdd v := rfl

theorem middle_conjugate_mem_arrayGroup (A : (Matrix J J K)ˣ)
    (u : (Matrix (Index J) (Index J) K)ˣ) (hu : u ∈ arrayGroup) :
    middleUnit A * u * (middleUnit A)⁻¹ ∈ arrayGroup := by
  obtain ⟨w, v, b, rfl⟩ := hu
  exact ⟨w ᵥ* ((A⁻¹ : (Matrix J J K)ˣ) : Matrix J J K),
    (A : Matrix J J K) *ᵥ v, b, middleUnit_conjugate_upper A w v b⟩

theorem vectorParameterHom_middle_conjugate (A : (Matrix J J K)ˣ) (u : arrayGroup (K := K) (J := J)) :
    vectorParameterHom
      ⟨middleUnit A * u.val * (middleUnit A)⁻¹, middle_conjugate_mem_arrayGroup A u.val u.property⟩ =
      Multiplicative.ofAdd ((A : Matrix J J K) *ᵥ (vectorParameterHom u).toAdd) := by
  obtain ⟨w, v, b, hu⟩ := u.property
  change Multiplicative.ofAdd (fun i =>
    ((middleUnit A * u.val * (middleUnit A)⁻¹ : (Matrix (Index J) (Index J) K)ˣ) :
      Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inr ()))) =
    Multiplicative.ofAdd ((A : Matrix J J K) *ᵥ (fun i =>
      (u.val : Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inr ()))))
  rw [hu, middleUnit_conjugate_upper]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
