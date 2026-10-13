import SymmetricSubgroupAsymptotics.BinaryIrreducibleTuple

/-!
# Central involutions of a normal kernel in the ambient group

The relative binary character argument uses the central involutions of a
normal kernel, but its three module layers are obtained before passing to
that kernel subtype.  This file realizes those involutions as a literal
ambient normal subgroup.  The construction records kernel membership,
centrality inside the kernel, and exponent two directly, so its ambient
normality does not depend on an abstract characteristic-subgroup API.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {Q B : Type*} [Group Q] [Group B]

/-- The central involutions of `ker π`, retained as elements of `Q`. -/
def normalKernelCentralOmega (π : Q →* B) : Subgroup Q where
  carrier := {x | x ∈ π.ker ∧
    (∀ a : π.ker, Commute x a.1) ∧ x ^ 2 = 1}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_, one_pow _⟩
    intro a
    exact Commute.one_left a.1
  mul_mem' := by
    intro x y hx hy
    refine ⟨π.ker.mul_mem hx.1 hy.1, ?_, ?_⟩
    · intro a
      calc
        x * y * a.1 = x * (y * a.1) := by group
        _ = x * (a.1 * y) := by rw [(hy.2.1 a).eq]
        _ = (x * a.1) * y := by group
        _ = (a.1 * x) * y := by rw [(hx.2.1 a).eq]
        _ = a.1 * (x * y) := by group
    · let ax : π.ker := ⟨x, hx.1⟩
      have hyx : Commute y x := hy.2.1 ax
      calc
        (x * y) ^ 2 = x * (y * x) * y := by
          simp only [pow_two, mul_assoc]
        _ = x * (x * y) * y := by rw [hyx.eq]
        _ = (x ^ 2) * (y ^ 2) := by
          simp only [pow_two, mul_assoc]
        _ = 1 := by rw [hx.2.2, hy.2.2, one_mul]
  inv_mem' := by
    intro x hx
    refine ⟨π.ker.inv_mem hx.1, ?_, ?_⟩
    · intro a
      exact (hx.2.1 a).inv_left
    · rw [inv_pow, hx.2.2, inv_one]

instance normalKernelCentralOmega_normal (π : Q →* B) :
    (normalKernelCentralOmega π).Normal := by
  constructor
  intro x hx q
  refine ⟨Subgroup.Normal.conj_mem inferInstance x hx.1 q, ?_, ?_⟩
  · intro a
    let a' : π.ker :=
      ⟨q⁻¹ * a.1 * q,
        by simpa only [inv_inv] using
          Subgroup.Normal.conj_mem inferInstance a.1 a.2 q⁻¹⟩
    have hc := hx.2.1 a'
    change Commute x (q⁻¹ * a.1 * q) at hc
    change (q * x * q⁻¹) * a.1 = a.1 * (q * x * q⁻¹)
    calc
      q * x * q⁻¹ * a.1 = q * (x * (q⁻¹ * a.1 * q)) * q⁻¹ := by group
      _ = q * ((q⁻¹ * a.1 * q) * x) * q⁻¹ := by rw [hc.eq]
      _ = a.1 * (q * x * q⁻¹) := by group
  · calc
      (q * x * q⁻¹) ^ 2 = q * (x ^ 2) * q⁻¹ := by
        simp only [pow_two, mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [hx.2.2]; simp

/-- The ambient normal subgroup is exactly the intrinsic central omega of
the kernel, including its elementary binary module structure. -/
noncomputable def binaryCentralOmegaEquivNormalKernel
    (π : Q →* B) :
    binaryCentralOmega π.ker ≃* normalKernelCentralOmega π := by
  let inclusion : binaryCentralOmega π.ker →*
      normalKernelCentralOmega π := {
    toFun z := ⟨z.1.1.1, z.1.1.2, (by
      intro a
      exact congrArg (fun y : π.ker => (y : Q))
        (Subgroup.mem_center_iff.mp z.1.2 a).symm),
      congrArg (fun y : Subgroup.center π.ker => ((y.1 : π.ker) : Q)) z.2⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply MulEquiv.ofBijective inclusion
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : normalKernelCentralOmega π => (y : Q)) hxy
  · intro x
    let k : π.ker := ⟨x.1, x.2.1⟩
    let z : Subgroup.center π.ker :=
      ⟨k, Subgroup.mem_center_iff.mpr (by
        intro a
        apply Subtype.ext
        exact (x.2.2.1 a).symm.eq)⟩
    let omega : binaryCentralOmega π.ker :=
      ⟨z, by
        apply Subtype.ext
        apply Subtype.ext
        exact x.2.2.2⟩
    refine ⟨omega, ?_⟩
    apply Subtype.ext
    rfl

end SymmetricSubgroupAsymptotics

end
