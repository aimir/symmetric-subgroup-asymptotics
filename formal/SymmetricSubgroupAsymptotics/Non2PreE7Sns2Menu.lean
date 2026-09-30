import SymmetricSubgroupAsymptotics.Non2PreE7Sns2ExceptionalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairMenuMassAggregation

/-!
# The literal all-width SNS2 menu

An SNS2 index is an original non-pair action class carrying the full weighted
rank-tail certificate.  The certificate is selected once from that proof and
all numerical functions below retain its quotient rank, semisimple factor,
and original normalizer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

abbrev PreE7Sns2MenuIndex (w : ℕ) :=
  {i : PreE7NonPairActionClass w //
    Nonempty (PreE7Sns2RankTailCertificate w i)}

noncomputable def preE7Sns2MenuCertificate {w : ℕ}
    (i : PreE7Sns2MenuIndex w) :
    PreE7Sns2RankTailCertificate w i.1 :=
  Classical.choice i.2

def preE7Sns2MenuAction {w : ℕ} (i : PreE7Sns2MenuIndex w) :=
  preE7NonPairAction w i.1

def preE7Sns2MenuNormalizer {w : ℕ} (i : PreE7Sns2MenuIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7Sns2MenuAction i : Set (Equiv.Perm (Fin w))))

theorem preE7Sns2MenuNormalizer_pos {w : ℕ} (i : PreE7Sns2MenuIndex w) :
    0 < preE7Sns2MenuNormalizer i := by
  change (0 : ℝ) < Nat.card (Subgroup.normalizer
    (preE7Sns2MenuAction i : Set (Equiv.Perm (Fin w))))
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7Sns2MenuAction i : Set (Equiv.Perm (Fin w)))))

def preE7Sns2MenuCoefficient {w : ℕ} (i : PreE7Sns2MenuIndex w)
    (b : ℕ) : ℝ :=
  (preE7Sns2MenuCertificate i).normalCount *
    (preE7Sns2MenuCertificate i).outerFactor b

theorem preE7Sns2MenuCoefficient_nonneg {w : ℕ}
    (i : PreE7Sns2MenuIndex w) (b : ℕ) :
    0 ≤ preE7Sns2MenuCoefficient i b :=
  mul_nonneg (preE7Sns2MenuCertificate i).normalCount_nonneg
    ((preE7Sns2MenuCertificate i).outerFactor_nonneg b)

def preE7Sns2MenuSlope {w : ℕ} (i : PreE7Sns2MenuIndex w) : ℝ :=
  ((preE7Sns2MenuCertificate i).quotientRank : ℝ) * (51 / 200)

/-- Remove exactly the universal quarter-square cost of the binary quotient
normal-subgroup menu.  What remains is subexponential in `w*n`. -/
def preE7Sns2NormalizedCoefficient {w : ℕ}
    (i : PreE7Sns2MenuIndex w) (b : ℕ) : ℝ :=
  preE7Sns2MenuCoefficient i b *
    (2 : ℝ) ^ (-(((preE7Sns2MenuCertificate i).quotientRank : ℝ) ^ 2 / 4))

theorem preE7Sns2NormalizedCoefficient_nonneg {w : ℕ}
    (i : PreE7Sns2MenuIndex w) (b : ℕ) :
    0 ≤ preE7Sns2NormalizedCoefficient i b :=
  mul_nonneg (preE7Sns2MenuCoefficient_nonneg i b) (by positivity)

theorem preE7Sns2MenuCoefficient_eq_normalized {w : ℕ}
    (i : PreE7Sns2MenuIndex w) (b : ℕ) :
    preE7Sns2MenuCoefficient i b =
      preE7Sns2NormalizedCoefficient i b *
        (2 : ℝ) ^ (((preE7Sns2MenuCertificate i).quotientRank : ℝ) ^ 2 / 4) := by
  unfold preE7Sns2NormalizedCoefficient
  calc
    _ = preE7Sns2MenuCoefficient i b * 1 := by ring
    _ = preE7Sns2MenuCoefficient i b *
        (2 : ℝ) ^
          (-(((preE7Sns2MenuCertificate i).quotientRank : ℝ) ^ 2 / 4) +
            ((preE7Sns2MenuCertificate i).quotientRank : ℝ) ^ 2 / 4) := by
      rw [show -(((preE7Sns2MenuCertificate i).quotientRank : ℝ) ^ 2 / 4) +
          ((preE7Sns2MenuCertificate i).quotientRank : ℝ) ^ 2 / 4 = 0 by ring,
        Real.rpow_zero]
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring

/-- The precise menu-mass target left after the quarter-square quotient cost.
It follows from the Fusari--Spiga order bound, the uniform semisimple-factor
bound, and the labelled transitive-action count. -/
def PreE7Sns2NormalizedMenuMassBound : Prop :=
  GrowingMenuMassBound 5
    (fun w i => preE7Sns2NormalizedCoefficient (w := w) i)
    (fun w i => preE7Sns2MenuNormalizer (w := w) i)

def preE7Sns2MenuExceptional {w : ℕ} (i : PreE7Sns2MenuIndex w)
    (b : ℕ) : ℝ :=
  preE7Sns2ExceptionalScalar (preE7Sns2MenuCertificate i) b

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
