import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-!
# Reusable numerical record for padded pre-E7 comparators

The character, semisimple, and abelian-tower templates all use the same
controlled padding.  This file packages its thirteen scalar inequalities
once, including the zero-tail row used by multiplicative certificates.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A nonnegative exponent with the original padding margin gives the full
entry parameter record at the fixed pre-E7 value `rho = 1/8192`. -/
theorem preE7Padded_entryParameters
    {w v0 : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta) (hv0 : 2 ≤ v0)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - v0) / 8 - eta) :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (paddedComparatorDegree preE7CharacterRho v0 w) eta
      (paddedComparatorDelta preE7CharacterRho eta v0 w)
      ((paddedComparatorDegree preE7CharacterRho v0 w : ℝ) / 8 +
        paddedComparatorDelta preE7CharacterRho eta v0 w / 2)
      (eta + ((paddedComparatorDegree preE7CharacterRho v0 w : ℝ) / 8 +
        paddedComparatorDelta preE7CharacterRho eta v0 w / 2)) 0 := by
  let idx : ℕ → Type := fun w' => {_u : Unit // w' = w}
  have hP := growingPadded_parameterBound (ι := idx)
    (ρ := preE7CharacterRho) (fun _ _ => v0) (fun _ _ => eta)
    (by norm_num [preE7CharacterRho])
    (by norm_num [preE7CharacterRho])
    (fun _ _ => heta) (fun _ _ => hv0)
    (by
      rintro w' ⟨_, rfl⟩
      exact hmargin)
  let j : idx w := ⟨(), rfl⟩
  refine
    { delta_nonneg := hP.delta_nonneg w j
      degree_pos := hP.degree_pos w j
      ratio := hP.ratio w j
      degree_upper := hP.degree_upper w j
      delta_lower := hP.delta_lower w j
      hot_margin := hP.hot_margin w j
      threshold_eq := hP.threshold_eq w j
      delta_upper := hP.delta_upper w j
      degree_lower := hP.degree_lower w j
      degree_width := hP.degree_width w j
      cold_slope := hP.cold_slope w j
      cold_gap := hP.cold_gap w j
      tail_gap := ?_ }
  have heven : (evenWidth w : ℝ) = 2 * halfDegree w := by
    exact_mod_cast (show evenWidth w = 2 * halfDegree w by rfl)
  have hv0nonneg : (0 : ℝ) ≤ v0 := by positivity
  nlinarith

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
