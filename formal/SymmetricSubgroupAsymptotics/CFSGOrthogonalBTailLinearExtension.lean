import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailGram
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPairOperator

/-! Explicit extension by a zero hyperbolic pair, and its literal
left inverse. The middle coordinate is retained. This is a linear map
on the original natural spaces, not a classical-model identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
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
    tailExtension K n v (pos (n + 1) 0) = 0 := by
  simp only [tailExtension, LinearMap.coe_mk, AddHom.coe_mk, tailEquiv_symm_pos_zero, Sum.elim_inr]

@[simp] theorem tailExtension_negative_head (n : ℕ) (v : Index n → K) :
    tailExtension K n v (neg (n + 1) 0) = 0 := by
  simp only [tailExtension, LinearMap.coe_mk, AddHom.coe_mk, tailEquiv_symm_neg_zero, Sum.elim_inr]

def tailRestrictionLinear (n : ℕ) : (Index (n + 1) → K) →ₗ[K] (Index n → K) where
  toFun := tailRestriction K n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem tailRestriction_extension (n : ℕ) (v : Index n → K) :
    tailRestrictionLinear K n (tailExtension K n v) = v := by
  funext i
  exact tailExtension_tailIndex K n v i

theorem tailExtension_norm (n : ℕ) (v : Index n → K) :
    (gram K (n + 1)).toBilin' (tailExtension K n v) (tailExtension K n v) =
      (gram K n).toBilin' v v := by
  rw [gram_norm_tail_of_negative_head_zero K n _ (tailExtension_negative_head K n v)]
  change (gram K n).toBilin' (tailRestrictionLinear K n (tailExtension K n v))
    (tailRestrictionLinear K n (tailExtension K n v)) = _
  rw [tailRestriction_extension]

def twiceTailExtension (s : ℕ) : (Index (s + 1) → K) →ₗ[K] (Index (s + 3) → K) :=
  (tailExtension K (s + 2)).comp (tailExtension K (s + 1))

def twiceTailRestriction (s : ℕ) : (Index (s + 3) → K) →ₗ[K] (Index (s + 1) → K) :=
  (tailRestrictionLinear K (s + 1)).comp (tailRestrictionLinear K (s + 2))

@[simp] theorem twiceTail_leftInverse (s : ℕ) (v : Index (s + 1) → K) :
    twiceTailRestriction K s (twiceTailExtension K s v) = v := by
  simp only [twiceTailRestriction, twiceTailExtension, LinearMap.comp_apply, tailRestriction_extension]

theorem twiceTail_norm (s : ℕ) (v : Index (s + 1) → K) :
    (gram K (s + 3)).toBilin' (twiceTailExtension K s v) (twiceTailExtension K s v) =
      (gram K (s + 1)).toBilin' v v := by
  change (gram K (s + 3)).toBilin'
    (tailExtension K (s + 2) (tailExtension K (s + 1) v))
    (tailExtension K (s + 2) (tailExtension K (s + 1) v)) = _
  rw [tailExtension_norm, tailExtension_norm]

@[simp] theorem twiceTail_positive_zero (s : ℕ) (v : Index (s + 1) → K) :
    twiceTailExtension K s v (pos (s + 3) 0) = 0 :=
  tailExtension_positive_head K (s + 2) (tailExtension K (s + 1) v)

@[simp] theorem twiceTail_negative_zero (s : ℕ) (v : Index (s + 1) → K) :
    twiceTailExtension K s v (neg (s + 3) 0) = 0 :=
  tailExtension_negative_head K (s + 2) (tailExtension K (s + 1) v)

@[simp] theorem twiceTail_positive_second (s : ℕ) (v : Index (s + 1) → K) :
    twiceTailExtension K s v (pos (s + 3) (secondIndex s)) = 0 := by
  change tailExtension K (s + 2) (tailExtension K (s + 1) v)
    (tailIndex (s + 2) (pos (s + 2) 0)) = 0
  rw [tailExtension_tailIndex, tailExtension_positive_head]

@[simp] theorem twiceTail_negative_second (s : ℕ) (v : Index (s + 1) → K) :
    twiceTailExtension K s v (neg (s + 3) (secondIndex s)) = 0 := by
  change tailExtension K (s + 2) (tailExtension K (s + 1) v)
    (tailIndex (s + 2) (neg (s + 2) 0)) = 0
  rw [tailExtension_tailIndex, tailExtension_negative_head]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
