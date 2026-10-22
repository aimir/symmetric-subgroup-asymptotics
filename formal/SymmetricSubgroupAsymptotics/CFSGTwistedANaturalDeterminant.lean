import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! All literal natural elementary A lifts have determinant one. The
proof uses the actual adjacent transvections, not an identification with
SL or a property of an abstract model of the same order. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

theorem naturalRootUnit_det (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    Matrix.det (naturalRootUnit K r neg i t : Mat K r) = 1 := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg (fun j : Fin (r + 1) => j.val) h
    change i.val = i.val + 1 at hv
    omega
  cases neg
  · change Matrix.det (1 + t • positive K r i) = 1
    simpa only [positive, Matrix.transvection, Matrix.smul_single,
      smul_eq_mul, mul_one] using
        Matrix.det_transvection_of_ne i.castSucc i.succ hne t
  · change Matrix.det (1 + t • negative K r i) = 1
    simpa only [negative, positive, Matrix.transpose_single,
      Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one] using
        Matrix.det_transvection_of_ne i.succ i.castSucc (Ne.symm hne) t

theorem naturalElementary_det (K : Type) [Field K] (r : ℕ)
    (u : NaturalElementary K r) : Matrix.det (u.val : Mat K r) = 1 := by
  let H : Subgroup (Mat K r)ˣ :=
    (Matrix.GeneralLinearGroup.det : (Mat K r)ˣ →* Kˣ).ker
  have hle : NaturalElementary K r ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rintro v ⟨neg, i, t, rfl⟩
    change Matrix.GeneralLinearGroup.det (naturalRootUnit K r neg i t) = 1
    apply Units.ext
    exact naturalRootUnit_det K r neg i t
  have he : Matrix.GeneralLinearGroup.det u.val = 1 := hle u.property
  exact congrArg (fun c : Kˣ => (c : K)) he

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
