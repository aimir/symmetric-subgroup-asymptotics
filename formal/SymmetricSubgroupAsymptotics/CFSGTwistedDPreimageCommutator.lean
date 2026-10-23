import SymmetricSubgroupAsymptotics.CFSGTwistedDPreimageRelativeStructure
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRootOrders
import SymmetricSubgroupAsymptotics.CFSGOddGeneratedDoubleIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCharTwoQuantitative

/-! The original Fixed action's natural preimage has commutator inside
the literal relative-root subgroup. Odd characteristic keeps both
index-two layers; characteristic two uses the actual trivial centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPreimageCommutator
open CFSGOrthogonalDSerreMatrices CFSGTwistedDPreimageRelativeStructure
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeRootOrders
open CFSGOddGeneratedIndexTwo CFSGOddGeneratedDoubleIndex

theorem relativePreimage_closure (s : ℕ) (q : CFSG.PrimePower) :
    relativePreimage s q = Subgroup.closure
      ((naturalInclusion s q) ⁻¹' relativeGenerators (s + 2) q) := by
  apply Subgroup.map_injective (naturalInclusion_injective s q)
  rw [relativePreimage_map, MonoidHom.map_closure]
  change Subgroup.closure (relativeGenerators (s + 2) q) = _
  congr 1
  apply Set.ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := relative_le_naturalInclusion_range s q (Subgroup.subset_closure hy)
    exact ⟨x, by change naturalInclusion s q x ∈ relativeGenerators (s + 2) q; rw [hx]; exact hy, hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

theorem relativePreimage_generator_pow (s : ℕ) (q : CFSG.PrimePower)
    (x : PreimageGroup s q)
    (hx : x ∈ (naturalInclusion s q) ⁻¹' relativeGenerators (s + 2) q) :
    x ^ q.prime = 1 := by
  apply naturalInclusion_injective s q
  rw [map_pow, map_one]
  exact relative_generator_pow_prime (s + 2) q (naturalInclusion s q x) hx

theorem commutator_le_relative_odd (s : ℕ) (q : CFSG.PrimePower) (hp : q.prime ≠ 2) :
    commutator (PreimageGroup s q) ≤ relativePreimage s q := by
  apply commutator_le_of_generated_odd_torsion (relativePreimage s q) (literalFixedKernel s q)
    (relative_le_literalFixedKernel s q) (relativePreimage_index_in_kernel_le_two s q)
    (literalFixedKernel_index_le_two s q)
    ((naturalInclusion s q) ⁻¹' relativeGenerators (s + 2) q) (relativePreimage_closure s q)
  intro x hx
  exact ⟨q.prime, q.prime_isPrime.odd_of_ne_two hp, relativePreimage_generator_pow s q x hx⟩

theorem literalFixedKernel_eq_top_char_two (s : ℕ) (q : CFSG.PrimePower) (hp : q.prime = 2) :
    literalFixedKernel s q = ⊤ := by
  letI : CharP (q.Extension 2) 2 :=
    Eq.mp (congrArg (CharP (q.Extension 2)) hp) inferInstance
  apply top_unique
  intro u _
  rw [← centralDifference_ker]
  change centralDifference s q u = 1
  apply Subtype.ext
  exact (CFSGOrthogonalDCharTwoQuantitative.center_eq_bot (q.Extension 2) s).le
    (centralDifference s q u).property

theorem commutator_le_relative (s : ℕ) (q : CFSG.PrimePower) :
    commutator (PreimageGroup s q) ≤ relativePreimage s q := by
  by_cases hp : q.prime = 2
  · have hi := relativePreimage_index_in_kernel_le_two s q
    rw [literalFixedKernel_eq_top_char_two s q hp] at hi
    change (relativePreimage s q).relIndex ⊤ ≤ 2 at hi
    rw [Subgroup.relIndex_top_right] at hi
    letI : (relativePreimage s q).Normal := normal_of_index_le_two _ hi
    have hcard : Nat.card (PreimageGroup s q ⧸ relativePreimage s q) ∣ 2 :=
      index_dvd_two _ hi
    letI : IsCyclic (PreimageGroup s q ⧸ relativePreimage s q) :=
      isCyclic_of_card_dvd_prime (p := 2) hcard
    letI : CommGroup (PreimageGroup s q ⧸ relativePreimage s q) := IsCyclic.commGroup
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  · exact commutator_le_relative_odd s q hp

end SymmetricSubgroupAsymptotics.CFSGTwistedDPreimageCommutator
