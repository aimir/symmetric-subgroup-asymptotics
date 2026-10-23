import SymmetricSubgroupAsymptotics.CFSGHermitianPairTransport

/-! Reciprocal orthogonality and fixed multipliers for literal signed
Hermitian matrix pairings. All characteristics are retained; no
polarization by division by two is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonality
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem zero_iff_swap (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (eps : K) (heps : eps ≠ 0) (H : Matrix I I K)
    (hH : H.map sigma = eps • H.transpose) (v w : I → K) :
    hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0 := by
  have hh := hermitianPair_sigma sigma hsigma eps H hH v w
  have he : sigma (hermitianPair sigma H v w) = 0 ↔
      hermitianPair sigma H w v = 0 := by
    rw [hh]
    exact mul_eq_zero_iff_left heps
  exact sigma.map_eq_zero_iff.symm.trans he

theorem zero_iff_swap_of_transpose (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (eps : K) (heps : eps ≠ 0)
    (H : Matrix I I K) (hH : (H.map sigma).transpose = eps • H) (v w : I → K) :
    hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0 := by
  apply zero_iff_swap sigma hsigma eps heps H ?_ v w
  have hh := congrArg Matrix.transpose hH
  simpa only [Matrix.transpose_transpose, Matrix.transpose_smul] using hh

theorem multiplier_fixed [DecidableEq I] (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (eps : K)
    (htau : tau eps = eps) (H : (Matrix I I K)ˣ)
    (hH : (H : Matrix I I K).map sigma = eps • (H : Matrix I I K).transpose)
    (f : (I → K) → (I → K)) (c : K)
    (hform : ∀ v w, hermitianPair sigma H (f v) (f w) =
      c * tau (hermitianPair sigma H v w)) (i₀ : I) : sigma c = c := by
  let v : I → K := Pi.single i₀ 1
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h i₀
    simp [v] at hh
  obtain ⟨w, hw⟩ := hermitianPair_surjective sigma H v hv 1
  have hbase : eps * hermitianPair sigma H w v = 1 := by
    have hh := hermitianPair_sigma sigma hsigma eps H hH v w
    rw [hw, map_one] at hh
    exact hh.symm
  have ht : eps * tau (hermitianPair sigma H w v) = 1 := by
    have hh := congrArg tau hbase
    simpa only [map_mul, htau, map_one] using hh
  have hh := hermitianPair_sigma sigma hsigma eps H hH (f v) (f w)
  rw [hform, hform, hw, map_one, mul_one] at hh
  calc
    sigma c = eps * (c * tau (hermitianPair sigma H w v)) := hh
    _ = c * (eps * tau (hermitianPair sigma H w v)) := by ring
    _ = c := by rw [ht, mul_one]

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonality
