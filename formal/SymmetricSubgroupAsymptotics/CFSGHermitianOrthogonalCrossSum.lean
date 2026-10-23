import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan

/-! The full cross-pairing on an orthogonal one-dimensional extension.
Both scalar factors, including the genuine field involution, are kept. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem hermitian_orthogonal_cross_sum (sigma : K ≃+* K) (H : Matrix I I K)
    (x y h : I → K) (a b : K)
    (hxh : hermitianPair sigma H x h = 0) (hhy : hermitianPair sigma H h y = 0) :
    hermitianPair sigma H (x + a • h) (y + b • h) =
      hermitianPair sigma H x y + sigma a * b * hermitianPair sigma H h h := by
  have hxs := hermitianPair_smul sigma H 1 b x h
  have hsy := hermitianPair_smul sigma H a 1 h y
  have hss := hermitianPair_smul sigma H a b h h
  simp only [one_smul,map_one,one_mul,hxh,hhy,mul_zero,mul_one] at hxs hsy
  rw [hermitianPair_add_left,hermitianPair_add_right,hermitianPair_add_right,hxs,hsy,hss]
  simp only [add_zero,zero_add]

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
