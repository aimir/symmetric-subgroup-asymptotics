import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowEvenIntersection

/-! Every symmetric Sylow containing an alternating Sylow normalizes
its literal ambient image, because that image is exactly the even part. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowAmbientNormalizer
open Equiv

theorem sylow_le_normalizer {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (Q : Sylow 2 (Perm X))
    (hPQ : (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ Q) :
    (Q : Subgroup (Perm X)) ≤ Subgroup.normalizer
      (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X)) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  rw [CFSGAlternatingSylowEvenIntersection.mem_ambient_iff P Q hPQ,
    CFSGAlternatingSylowEvenIntersection.mem_ambient_iff P Q hPQ]
  have hq : g * a * g⁻¹ ∈ Q ↔ a ∈ Q := by
    constructor
    · intro h
      have hh := Q.mul_mem (Q.mul_mem (Q.inv_mem hg) h) hg
      simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
    · intro h
      exact Q.mul_mem (Q.mul_mem hg h) (Q.inv_mem hg)
  have he : g * a * g⁻¹ ∈ alternatingGroup X ↔ a ∈ alternatingGroup X := by
    simp only [Perm.mem_alternatingGroup, map_mul, map_inv]
    constructor <;> intro h
    · have hh := congrArg (fun z : ℤˣ => (Perm.sign g)⁻¹ * z * Perm.sign g) h
      simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel_right, inv_mul_cancel,
        one_mul, mul_one] using hh
    · rw [h, mul_one, mul_inv_cancel]
  exact (and_congr hq he).symm

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowAmbientNormalizer
