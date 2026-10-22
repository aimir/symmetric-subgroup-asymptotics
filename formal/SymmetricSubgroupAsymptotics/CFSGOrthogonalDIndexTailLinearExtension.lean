import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailQuadratic

/-! Explicit extension by a zero hyperbolic pair, and its literal
left inverse. Both new head coordinates are zero. This is a linear map
on the original natural spaces, not a classical-model identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def tailExtension (n : ℕ) : (Index n → K) →ₗ[K] (Index (n + 1) → K) where
  toFun v x := Sum.elim v (fun _ => 0) ((tailEquiv n).symm x)
  map_add' v w := by
    funext x
    change Sum.elim (v + w) (fun _ => 0) ((tailEquiv n).symm x) =
      Sum.elim v (fun _ => 0) ((tailEquiv n).symm x) +
        Sum.elim w (fun _ => 0) ((tailEquiv n).symm x)
    rcases (tailEquiv n).symm x with i | i
    · rfl
    · exact (zero_add (0 : K)).symm
  map_smul' a v := by
    funext x
    change Sum.elim (a • v) (fun _ => 0) ((tailEquiv n).symm x) =
      a * Sum.elim v (fun _ => 0) ((tailEquiv n).symm x)
    rcases (tailEquiv n).symm x with i | i
    · rfl
    · exact (mul_zero a).symm

@[simp] theorem tailExtension_tailIndex (n : ℕ) (v : Index n → K) (i : Index n) :
    tailExtension K n v (tailIndex n i) = v i := by
  simp only [tailExtension, LinearMap.coe_mk, AddHom.coe_mk, tailEquiv_symm_tailIndex, Sum.elim_inl]

@[simp] theorem tailExtension_positive_head (n : ℕ) (v : Index n → K) :
    tailExtension K n v (Sum.inl (0 : Fin (n + 1))) = 0 := by
  simp only [tailExtension, LinearMap.coe_mk, AddHom.coe_mk, tailEquiv_symm_positive_zero, Sum.elim_inr]

@[simp] theorem tailExtension_negative_head (n : ℕ) (v : Index n → K) :
    tailExtension K n v (Sum.inr (0 : Fin (n + 1))) = 0 := by
  simp only [tailExtension, LinearMap.coe_mk, AddHom.coe_mk, tailEquiv_symm_negative_zero, Sum.elim_inr]

def tailRestrictionLinear (n : ℕ) : (Index (n + 1) → K) →ₗ[K] (Index n → K) where
  toFun := tailRestriction K n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem tailRestriction_extension (n : ℕ) (v : Index n → K) :
    tailRestrictionLinear K n (tailExtension K n v) = v := by
  funext i
  exact tailExtension_tailIndex K n v i

theorem tailExtension_norm (n : ℕ) (v : Index n → K) :
    splitQ K (tailExtension K n v) = splitQ K v := by
  rw [splitQ_tail_of_negative_head_zero K n _ (tailExtension_negative_head K n v)]
  change splitQ K (tailRestrictionLinear K n (tailExtension K n v)) = _
  rw [tailRestriction_extension]

def twiceTailExtension (n : ℕ) : (Index n → K) →ₗ[K] (Index (n + 2) → K) :=
  (tailExtension K (n + 1)).comp (tailExtension K n)

def twiceTailRestriction (n : ℕ) : (Index (n + 2) → K) →ₗ[K] (Index n → K) :=
  (tailRestrictionLinear K n).comp (tailRestrictionLinear K (n + 1))

@[simp] theorem twiceTail_leftInverse (n : ℕ) (v : Index n → K) :
    twiceTailRestriction K n (twiceTailExtension K n v) = v := by
  simp only [twiceTailRestriction, twiceTailExtension, LinearMap.comp_apply, tailRestriction_extension]

theorem twiceTail_norm (n : ℕ) (v : Index n → K) :
    splitQ K (twiceTailExtension K n v) = splitQ K v := by
  change splitQ K (tailExtension K (n + 1) (tailExtension K n v)) = _
  rw [tailExtension_norm, tailExtension_norm]

@[simp] theorem twiceTail_positive_zero (n : ℕ) (v : Index n → K) :
    twiceTailExtension K n v (Sum.inl 0) = 0 :=
  tailExtension_positive_head K (n + 1) (tailExtension K n v)

@[simp] theorem twiceTail_negative_zero (n : ℕ) (v : Index n → K) :
    twiceTailExtension K n v (Sum.inr 0) = 0 :=
  tailExtension_negative_head K (n + 1) (tailExtension K n v)

def tailSecondIndex (n : ℕ) : Fin (n + 2) := ⟨1, by omega⟩

@[simp] theorem twiceTail_positive_second (n : ℕ) (v : Index n → K) :
    twiceTailExtension K n v (Sum.inl (tailSecondIndex n)) = 0 := by
  change tailExtension K (n + 1) (tailExtension K n v)
    (tailIndex (n + 1) (Sum.inl 0)) = 0
  rw [tailExtension_tailIndex, tailExtension_positive_head]

@[simp] theorem twiceTail_negative_second (n : ℕ) (v : Index n → K) :
    twiceTailExtension K n v (Sum.inr (tailSecondIndex n)) = 0 := by
  change tailExtension K (n + 1) (tailExtension K n v)
    (tailIndex (n + 1) (Sum.inr 0)) = 0
  rw [tailExtension_tailIndex, tailExtension_negative_head]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
