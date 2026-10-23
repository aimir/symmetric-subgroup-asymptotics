import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction

/-! Original automorphisms preserving the actual positive Sylow
permute its two minimal parabolics. The permutation is retained in
every characteristic, including the characteristic-three graph case. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParabolicAction
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalUpperNormalizer
open CFSGGTwoD4GeckOriginalMinimalParabolics CFSGMinimalOvergroupAutomorphismAction
open CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

theorem exists_original_parabolic_permutation (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MulAut (Projective CartanMatrix.G₂ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
      f.toMonoidHom = (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K))) :
    ∃ sigma : Equiv.Perm Bool, ∀ a : Bool,
      (originalSimpleParabolic K a).map f.toMonoidHom = originalSimpleParabolic K (sigma a) := by
  have hB : (Subgroup.normalizer
      (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K))).map f.toMonoidHom =
      Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) := by
    have hn := Subgroup.map_equiv_normalizer_eq
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) f
    have he := congrArg (fun P : Subgroup (Projective CartanMatrix.G₂ K) =>
      Subgroup.normalizer (P : Set (Projective CartanMatrix.G₂ K))) hU
    exact hn.trans he
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)))
    (originalSimpleParabolic K) (original_upper_lt_simpleParabolic K p)
    (original_simpleParabolic_minimal K p) (original_minimal_overgroup_eq_simpleParabolic K p)
    (originalSimpleParabolic_injective K) f hB

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParabolicAction
