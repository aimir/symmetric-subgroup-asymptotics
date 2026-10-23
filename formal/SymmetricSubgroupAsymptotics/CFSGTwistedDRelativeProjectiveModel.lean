import SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCenter
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeDerivedImage
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootOrders
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterPrimeCoprime

/-! The SAME original twisted-D model is the literal relative-root
group modulo its full centre. The actual action kernel is central;
p-torsion generation and the proved p-prime scalar centre prevent a
second central quotient from losing additional elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeCenter CFSGTwistedDRelativeDerivedImage

def centerInclusion (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup.center (relativeRootGroup (s + 2) q) →*
      Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) where
  toFun z := ⟨⟨z.val.val, relativeRootGroup_le_elementary (s + 2) q z.val.property⟩,
    (elementaryRootGroup_center_iff_scalar (q.Extension 2) (s + 2) _).mpr
      ((relativeRootGroup_center_iff_scalar (s + 2) q z.val).mp z.property)⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem centerInclusion_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (centerInclusion s q) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) =>
    z.val.val) h

theorem relative_center_card_le_two (s : ℕ) (q : CFSG.PrimePower) :
    Nat.card (Subgroup.center (relativeRootGroup (s + 2) q)) ≤ 2 :=
  (Nat.card_le_card_of_injective (centerInclusion s q) (centerInclusion_injective s q)).trans
    (CFSGOrthogonalDCenterCardinality.center_card_le_two (q.Extension 2) s)

theorem relative_center_prime_coprime (s : ℕ) (q : CFSG.PrimePower) :
    q.prime.Coprime (Nat.card (Subgroup.center (relativeRootGroup (s + 2) q))) := by
  exact Nat.Coprime.of_dvd_right
    (Subgroup.card_dvd_of_injective (centerInclusion s q) (centerInclusion_injective s q))
    (CFSGOrthogonalDCenterPrimeCoprime.center_prime_coprime (q.Extension 2) s q.prime)

theorem relative_generators_closure (n : ℕ) (q : CFSG.PrimePower) :
    Subgroup.closure ((relativeRootGroup n q).subtype ⁻¹' relativeGenerators n q) = ⊤ := by
  let R := relativeRootGroup n q
  have hset : R.subtype '' (R.subtype ⁻¹' relativeGenerators n q) = relativeGenerators n q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, Subgroup.subset_closure hy⟩, hy, rfl⟩
  apply Subgroup.map_injective (show Function.Injective R.subtype from Subtype.val_injective)
  rw [MonoidHom.map_closure, hset, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem relative_generator_pow (n : ℕ) (q : CFSG.PrimePower)
    (x : relativeRootGroup n q) (hx : x.val ∈ relativeGenerators n q) : x ^ q.prime = 1 := by
  apply Subtype.ext
  exact CFSGTwistedDRelativeRootOrders.relative_generator_pow_prime n q x.val hx

theorem relative_action_kernel_central (s : ℕ) (q : CFSG.PrimePower) :
    (relativeImageAction s q).rangeRestrict.ker ≤
      Subgroup.center (relativeRootGroup (s + 2) q) := by
  intro u hu
  have he := congrArg Subtype.val hu
  change elementaryImageAction (q.Extension 2) (s + 4) (by omega)
    (Subgroup.inclusion (relativeRootGroup_le_elementary (s + 2) q) u) = 1 at he
  have hz : Subgroup.inclusion (relativeRootGroup_le_elementary (s + 2) q) u ∈
      Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) := by
    rw [← elementaryImageAction_ker (q.Extension 2) s]
    exact he
  exact (relativeRootGroup_center_iff_scalar (s + 2) q u).mpr
    ((elementaryRootGroup_center_iff_scalar (q.Extension 2) (s + 2) _).mp hz)

def relativeProjectiveImageEquiv (s : ℕ) (q : CFSG.PrimePower) :
    (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) ≃*
      ((relativeImageAction s q).range ⧸ Subgroup.center (relativeImageAction s q).range) :=
  CFSGPGeneratedCentralLift.projectiveEquiv (relativeImageAction s q).rangeRestrict
    (relativeImageAction s q).rangeRestrict_surjective (relative_action_kernel_central s q)
    q.prime (relative_center_prime_coprime s q)
    ((relativeRootGroup (s + 2) q).subtype ⁻¹' relativeGenerators (s + 2) q)
    (relative_generators_closure (s + 2) q) (relative_generator_pow (s + 2) q)

def originalRelativeProjectiveEquiv (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    CFSG.Models.TwistedD (s + 4) q ≃*
      (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) :=
  (originalProjectiveRelativeImageEquiv s q).trans (relativeProjectiveImageEquiv s q).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
