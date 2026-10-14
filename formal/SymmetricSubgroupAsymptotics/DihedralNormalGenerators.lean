import SymmetricSubgroupAsymptotics.MetacyclicNormalGenerators
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Two normal generators for finite dihedral groups and affine images

The actual parity map to C2 has the cyclic rotation subgroup as kernel.
The metacyclic theorem therefore bounds every normal subgroup by two
generators, for all finite dihedral groups simultaneously. This supplies
the order-eight dihedral base needed below irreducible affine extensions.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DihedralNormalGenerators

open DihedralGroup

def parity (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .r _ => Multiplicative.ofAdd 0
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · change Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 + 1)
      congr 1

theorem parity_ker (n : ℕ) [NeZero n] :
    (parity n).ker = Subgroup.zpowers (r (1 : ZMod n)) := by
  ext x
  cases x with
  | r i =>
    constructor
    · intro _hx
      have hp : (r (1 : ZMod n)) ^ i.val = r i := by
        rw [r_one_pow, ZMod.natCast_zmod_val]
      exact hp ▸ Subgroup.npow_mem_zpowers (r 1) i.val
    · intro _hx
      rfl
  | sr i =>
    constructor
    · intro hx
      change Multiplicative.ofAdd (1 : ZMod 2) = 1 at hx
      have h := congrArg Multiplicative.toAdd hx
      change (1 : ZMod 2) = 0 at h
      exact ((by decide : (1 : ZMod 2) ≠ 0) h).elim
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [r_zpow] at hk
      cases hk

theorem parity_ker_isCyclic (n : ℕ) [NeZero n] : IsCyclic (parity n).ker := by
  rw [parity_ker]
  infer_instance

/-- Unconditional uniform bound on all actual normal subgroups. -/
theorem normal_generating_pairs (n : ℕ) [NeZero n] :
    ∀ N : Subgroup (DihedralGroup n), N.Normal →
      ∃ x : Fin 2 → DihedralGroup n, Subgroup.normalClosure (Set.range x) = N := by
  letI := parity_ker_isCyclic n
  exact normal_generating_pairs_of_cyclic_kernel (parity n)

theorem quotientSocle_two (n : ℕ) [NeZero n]
    (N : Subgroup (DihedralGroup n)) [N.Normal] :
    SocleNormalGeneratorBound (DihedralGroup n ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_pairs n) N

end DihedralNormalGenerators

namespace AffineModel

/-- The original generated complement may be the actual image of a
dihedral group; the same two positions suffice for its affine extension. -/
theorem normal_generating_pairs_of_irreducible_dihedral_image
    {p d : ℕ} [Fact p.Prime] (R : Subgroup (GLV p d))
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    (n : ℕ) [NeZero n] (q : DihedralGroup n →* R) (hq : Function.Surjective q) :
    ∀ N : Subgroup (Aff R), N.Normal →
      ∃ x : Fin 2 → Aff R, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_irreducible_complement R hirr v hv (by decide)
    (normal_generating_tuples_of_surjective q hq
      (DihedralNormalGenerators.normal_generating_pairs n))

end AffineModel
end SymmetricSubgroupAsymptotics

end
