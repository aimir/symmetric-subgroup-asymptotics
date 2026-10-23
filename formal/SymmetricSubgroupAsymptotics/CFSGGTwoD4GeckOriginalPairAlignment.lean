import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParabolicAction
import SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment

/-! Every automorphism of the same original G2 model admits an actual
inner adjustment preserving the literal opposed pair and permuting
the two minimal parabolics. The Bool permutation remains unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairAlignment
open CFSGGTwoD4GeckOriginalOppositeAlignment CFSGGTwoD4GeckOriginalProjection
open CFSGGTwoD4GeckOriginalUpperNormalizer CFSGGTwoD4GeckOriginalParabolicAction
open CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
local instance originalFinite : Finite (Projective CartanMatrix.G₂ K) := original_finite K

theorem original_exists_inner_fix_pair (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MulAut (Projective CartanMatrix.G₂ K)) :
    ∃ g : Projective CartanMatrix.G₂ K,
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
        (MulAut.conj g * f).toMonoidHom =
          (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) ∧
      (originalNegative K).map (MulAut.conj g * f).toMonoidHom = originalNegative K :=
  CFSGOppositeSylowOfAlignment.exists_inner_fix_pair
    (originalPositiveSylow K p) (originalOppositeSylow K p) (originalNegative K)
    (original_opposite_sylows_disjoint K p) (original_opposite_conjugate_by_positive K p) f

theorem exists_inner_fix_pair_and_parabolic_permutation (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MulAut (Projective CartanMatrix.G₂ K)) :
    ∃ (g : Projective CartanMatrix.G₂ K) (sigma : Equiv.Perm Bool),
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
        (MulAut.conj g * f).toMonoidHom =
          (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) ∧
      (originalNegative K).map (MulAut.conj g * f).toMonoidHom = originalNegative K ∧
      ∀ a : Bool, (originalSimpleParabolic K a).map (MulAut.conj g * f).toMonoidHom =
        originalSimpleParabolic K (sigma a) := by
  obtain ⟨g, hgU, hgV⟩ := original_exists_inner_fix_pair K p f
  obtain ⟨sigma, hsigma⟩ := exists_original_parabolic_permutation K p (MulAut.conj g * f) hgU
  exact ⟨g, sigma, hgU, hgV, hsigma⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairAlignment
