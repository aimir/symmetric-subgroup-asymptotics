import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics

/-! Install a fixed actual cold-rank source without changing its action,
normal axes or comparator. The only additional certificates are explicit
numerical margins and coefficient growth. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.FixedColdRankSourceInstallation

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- A fixed factorial rank-tail loss is harmless after the original
physical pointing. This keeps the complete raw source visible. -/
def numericalMargin
    (S : PreE7DegreeTwoPairSummedSource w U)
    (h k l L : ℕ) (hw : w=2*h) (hh : 6≤h) (hwidth : w≤12288)
    (eta delta cutoff alpha : ℝ)
    (hmain : S.mainCoefficient=(2 : ℝ)^L)
    (hcold : S.coldCoefficient=fun _ => 0)
    (heta : S.eta=eta) (htheta : S.theta=0)
    (hraw : S.exceptionalRaw=BinaryKernelRankTailNumerics.raw ((2 : ℝ)^l) k)
    (hparams : PreE7CharacterEntryParameters preE7CharacterRho w S.v eta delta cutoff alpha 0)
    (hgrowth : ∀ b : ℕ,(2 : ℝ)^L ≤
      (2 : ℝ)^(16*(w : ℝ)*Real.log ((w+b+2 : ℕ) : ℝ)^2)) : S.NumericalMargin where
  D := fun _ => (2 : ℝ)^L
  combinedEta := eta
  delta := delta
  cutoff := cutoff
  alpha := alpha
  alpha_eq := hparams.cold_slope
  D_nonneg := fun _ => pow_nonneg (by norm_num) _
  width_upper := hwidth
  parameters := hparams
  total_growth := hgrowth
  combined_summed := by
    intro b P
    have hs := S.summed b P
    simpa only [hmain,hcold,heta,htheta] using hs
  exceptional := by
    intro hc
    let a : ℝ := Nat.card (Subgroup.normalizer
      (preE7NonPairAction w U : Set (Equiv.Perm (Fin w))))
    have ha : 1≤a := by
      dsimp only [a]
      exact_mod_cast Nat.succ_le_of_lt (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))))
    have heq : S.exceptionalScalar=BinaryKernelRankTailNumerics.pointed h a ((2 : ℝ)^l) k := by
      funext b
      change growingQuotientNormalizedPointing b w a*S.exceptionalRaw b=
        growingQuotientNormalizedPointing b (2*h) a*
          BinaryKernelRankTailNumerics.raw ((2 : ℝ)^l) k b
      rw [congrFun hraw b]
      exact congrArg (fun v => growingQuotientNormalizedPointing b v a*
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^l) k b) hw
    rw [heq]
    exact BinaryKernelRankTailNumerics.exponentialBound hc h k hh a _ ha
      (pow_nonneg (by norm_num) _)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.FixedColdRankSourceInstallation
