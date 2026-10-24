import SymmetricSubgroupAsymptotics.CFSGQuadraticTracePairing

/-! Signed central trace pairings in the literal quadratic field.
The chosen nonzero central coordinate is retained in every identity;
these statements also hold in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGQuadraticSignedTracePairing
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField CFSGQuadraticTracePairing

theorem signedTrace_eq_scaled_trace (q : CFSG.PrimePower) (eps : ℤ)
    (heps : eps = 1 ∨ eps = -1) (delta : q.Extension 2) (hdelta : delta ≠ 0)
    (hfixed : definingFieldAutomorphism q 2 delta = (eps : q.Extension 2) * delta)
    (z : q.Extension 2) :
    z + (eps : q.Extension 2) * definingFieldAutomorphism q 2 z =
      delta * (traceLinear q (z / delta) : q.Extension 2) := by
  rw [traceLinear_val, map_div₀, hfixed]
  rcases heps with rfl | rfl <;> norm_num <;> field_simp <;> ring

theorem signedProduct_eq_coordinate_sum (q : CFSG.PrimePower) (eps : ℤ)
    (heps : eps = 1 ∨ eps = -1) (delta : q.Extension 2) (hdelta : delta ≠ 0)
    (hfixed : definingFieldAutomorphism q 2 delta = (eps : q.Extension 2) * delta)
    (x y : q.Extension 2) :
    x * y + (eps : q.Extension 2) * definingFieldAutomorphism q 2 (x * y) =
      delta * ((∑ i : Fin 2, firstCoordinates q x i *
        secondCoordinates q (y / delta) i : fixedField q) : q.Extension 2) := by
  rw [signedTrace_eq_scaled_trace q eps heps delta hdelta hfixed]
  have hxy : x * y / delta = x * (y / delta) := by ring
  rw [hxy]
  exact congrArg (fun c : fixedField q => delta * (c : q.Extension 2))
    (pairing_eq_coordinate_sum q x (y / delta))

theorem signedProduct_coordinates (q : CFSG.PrimePower) (eps : ℤ)
    (heps : eps = 1 ∨ eps = -1) (delta : q.Extension 2) (hdelta : delta ≠ 0)
    (hfixed : definingFieldAutomorphism q 2 delta = (eps : q.Extension 2) * delta)
    (a b : Fin 2 → fixedField q) :
    (firstCoordinates q).symm a * (delta * (secondCoordinates q).symm b) +
        (eps : q.Extension 2) * definingFieldAutomorphism q 2
          ((firstCoordinates q).symm a * (delta * (secondCoordinates q).symm b)) =
      delta * ((∑ i : Fin 2, a i * b i : fixedField q) : q.Extension 2) := by
  rw [signedProduct_eq_coordinate_sum q eps heps delta hdelta hfixed]
  have hdiv : (delta * (secondCoordinates q).symm b) / delta =
      (secondCoordinates q).symm b := by field_simp
  rw [hdiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end SymmetricSubgroupAsymptotics.CFSGQuadraticSignedTracePairing
