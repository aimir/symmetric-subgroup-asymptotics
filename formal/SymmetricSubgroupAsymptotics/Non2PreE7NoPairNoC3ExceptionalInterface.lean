import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveExceptional
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3AdditiveTailInterface

/-!
# Exceptional source-summed interface for the final pre-E7 residual

This is the physical integration boundary for the three historical binary
rank-tail families.  One certificate-retaining cover may use the ordinary
comparator/additive rows on most cells and an already source-summed scalar on
exceptional cells.  The literal original action and its normalizer remain in
every local term.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Structural and local physical data for a mixed ordinary/exceptional
pre-`E7` cover.  The local inequality is stated after physical pointing:
this is exactly where a rank-tail certificate first becomes comparable with
ordinary comparator cells. -/
structure PreE7NoPairNoC3LocalExceptionalData (r : ℕ) where
  P : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) b,
    Subgroup (preE7NonPairFirstOwnerAction w i ×
      Equiv.Perm (Fin b)) → Prop
  P_natural : ∀ w i b,
    FusionOrbitNatural (preE7NonPairFirstOwnerAction w i) (P w i b)
  physical_cover : ∀ n (H : Subgroup (Equiv.Perm (Fin n))),
    H ∈ PreE7NoPairNoC3ResidualSubgroupSet n →
      ∃ j : GrowingQuotientPhysicalIndex
          (ι := fun w => PreE7NonPairFirstOwnerIndex (r + 1) w) 3 n,
        H ∈ GrowingQuotientCanonicalFamily 3 n
          preE7NonPairFirstOwnerAction P j
  D : ∀ w (_i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ), ℝ
  T : ∀ w (_i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ), ℝ
  X : ∀ w (_i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ), ℝ
  A : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ
  eta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  delta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  cutoff : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  alpha : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  theta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  D_nonneg : ∀ w i b, 0 ≤ D w i b
  T_nonneg : ∀ w i b, 0 ≤ T w i b
  A_eq : ∀ w i, A w i =
    (Nat.card (Subgroup.normalizer
      (preE7NonPairFirstOwnerAction w i :
        Set (Equiv.Perm (Fin w)))) : ℝ)
  local_bound : GrowingQuotientAdditiveExceptionalLocalPhysicalBound 3
    preE7NonPairFirstOwnerAction P D T X A v eta delta cutoff alpha theta

/-- Numerical data for the mixed cover.  The two ordinary menu masses use
the existing growing-quotient estimates; the exceptional total has its own
zero-kernel exponential scalar bound. -/
structure PreE7NoPairNoC3LocalExceptionalNumericalCertificate {r : ℕ}
    (D : PreE7NoPairNoC3LocalExceptionalData r) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le_eighth : rho ≤ 1 / 8
  parameters : GrowingQuotientParameterBound rho
    D.v D.eta D.delta D.cutoff D.alpha
  tail_gap : ∀ w i,
    D.theta w i ≤ (halfDegree w : ℝ) / 4 - rho * w / 4
  main_menu : GrowingMenuMassBound 3 D.D D.A
  tail_menu : GrowingMenuMassBound 3 D.T D.A
  exceptional : ExponentialScalarBound
    (growingQuotientExceptionalTotal 3 D.X)

namespace PreE7NoPairNoC3LocalExceptionalData

variable {r : ℕ} (D : PreE7NoPairNoC3LocalExceptionalData r)

theorem A_pos (w i) : 0 < D.A w i := by
  rw [D.A_eq w i]
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7NonPairFirstOwnerAction w i : Set (Equiv.Perm (Fin w)))))

/-- The exact residual ratio is covered by the ordinary comparator rows plus
the exceptional source-summed scalar. -/
theorem physical_bound : GrowingQuotientAdditiveExceptionalPhysicalBound
    preE7NoPairNoC3ResidualRatio 3 D.D D.T D.X D.A D.v D.eta D.delta
      D.cutoff D.alpha D.theta :=
  growingQuotientAdditiveExceptionalPhysicalBound_of_local
    preE7NoPairNoC3ResidualRatio 3 (by omega)
    PreE7NoPairNoC3ResidualSubgroupSet preE7NonPairFirstOwnerAction D.P
    D.D D.T D.X D.A D.v D.eta D.delta D.cutoff D.alpha D.theta
    (Filter.Eventually.of_forall (fun n => by
      rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet n]))
    D.physical_cover D.local_bound

end PreE7NoPairNoC3LocalExceptionalData

/-- The mixed ordinary/exceptional package closes the final pre-`E7`
frontier. -/
noncomputable def
    preE7NoPairNoC3_exponentialForwardEstimate_of_localExceptionalData
    {r : ℕ} (D : PreE7NoPairNoC3LocalExceptionalData r)
    (Numerics : PreE7NoPairNoC3LocalExceptionalNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio :=
  growingQuotientAdditiveExceptional_exponentialForwardEstimate
    preE7NoPairNoC3ResidualRatio 3 D.D D.T D.X D.A D.v D.eta D.delta
      D.cutoff D.alpha D.theta Numerics.rho_pos Numerics.rho_le_eighth
      (by omega) D.D_nonneg D.T_nonneg D.A_pos Numerics.parameters
      Numerics.tail_gap Numerics.main_menu Numerics.tail_menu hcoarse
      Numerics.exceptional D.physical_bound

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
