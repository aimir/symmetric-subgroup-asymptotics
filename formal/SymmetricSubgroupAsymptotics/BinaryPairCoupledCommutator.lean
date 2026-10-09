import SymmetricSubgroupAsymptotics.BinaryCoupledHeadCertificate
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import SymmetricSubgroupAsymptotics.BinaryPairPermutationGeneratorExtension

/-!
# The product denominator from two nested pair frames

For two successive pair frames, let `D` be a subgroup of the original
action whose commutators lie in `N`.  Its image in the second pair kernel
gives a top flip space `K`; its intersection with the first pair kernel
gives a point space `B`.  Pair-sum and pair-constant coordinates give the
middle and bottom spaces `W` and `L`.  The literal affine commutator identity
then proves `KW ≤ L`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X : Type*} {s t : ℕ}
  {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin s))
  (E : BinaryPairFrame F.top.range (Fin t))

/-- The coupled product containment, with every space defined from the two
literal pair frames and the original subgroup `D`. -/
theorem nestedPair_productSpan_le_constantPreimage
    (N D : Subgroup U) (hND : N ≤ D)
    (hcomm : ∀ (u : U), u ∈ D → ∀ (k : F.top.ker), (k : U) ∈ D →
      ((k : U)⁻¹ * u * (k : U) * u⁻¹) ∈ N) :
    binaryCoordinateProductSpan
        (E.ambientAxis (D.map F.top.rangeRestrict))
        ((F.ambientAxis D).map E.pairSum) ≤
      (F.ambientAxis D).comap E.pairConstant := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨a, haD, hax⟩ := (E.mem_ambientAxis
    (D.map F.top.rangeRestrict) x).mp hx
  obtain ⟨f, hfB, hfw⟩ := hw
  obtain ⟨k, hkD, hkf⟩ := (F.mem_ambientAxis D f).mp hfB
  obtain ⟨u, huD, hua⟩ := haD
  have htop : F.top.rangeRestrict u = (a : F.top.range) := hua
  let c : F.top.ker := k⁻¹ * MulAut.conjNormal u k
  have hcN : (c : U) ∈ N := by
    change ((k : U)⁻¹ * u * (k : U) * u⁻¹) ∈ N
    exact hcomm u huD k hkD
  have hcB : F.bits c ∈ F.ambientAxis D :=
    (F.bits_mem_ambientAxis D c).mpr (hND hcN)
  change E.pairConstant (x * w) ∈ F.ambientAxis D
  rw [← hax, ← hfw, ← hkf]
  have hdisp := E.kernel_displacement_eq_pairConstant_product a (F.bits k)
  have hcommBits := F.bits_commutator u k
  change F.bits c =
    F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k) -
      F.bits k at hcommBits
  rw [htop] at hcommBits
  change F.bits c =
    permutationFunctionRepresentation (ZMod 2) F.top.range (Fin s)
        (a : F.top.range) (F.bits k) - F.bits k at hcommBits
  rw [hdisp] at hcommBits
  rw [← hcommBits]
  exact hcB

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
