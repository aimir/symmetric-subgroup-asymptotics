import SymmetricSubgroupAsymptotics.ElementarySupplementRelativeRank
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
import SymmetricSubgroupAsymptotics.BinaryNormalDegreeRecurrence
import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators

/-! Proper normals save a generator when an actual elementary kernel
supplements them. The image and the index refer to the original group.
These elementary lemmas do not use a finite excess classifier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A proper normal with an elementary supplement has strictly smaller
normal rank than the original whole finite p-group. -/
theorem normalGen_add_one_le_top_of_elementary_supplement
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G) (E N : Subgroup G) [N.Normal]
    (hsup : E ⊔ N = ⊤) (hE : IsMulCommutative E)
    (hexp : ∀ e : E, e ^ p = 1) (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N + 1 ≤ MarkedC4.normalGen (⊤ : Subgroup G) := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨j, hj⟩ := hG.index N
  have hjpos : 0 < j := by
    by_contra he
    have hjzero : j = 0 := by omega
    have hi : N.index = 1 := by simpa only [hjzero, pow_zero] using hj
    exact hproper (Subgroup.index_eq_one.mp hi)
  have heq := normalGen_add_indexExponent_eq_of_elementary_supplement
    p E N hsup hE hexp hG j hj
  obtain ⟨S, hS, hgen⟩ := MarkedC4.genRank_spec (G := G)
  have hchar := (primeCharacterRank_le_generators p S hgen).trans_eq hS
  have htop := MarkedC4.genRank_le_normalGen_top (G := G)
  omega

/-- A proper subgroup of an original regular elementary action saves one
from the degree exponent. This bound does not require classifying normals. -/
theorem elementary_transitive_proper_normalGen_add_one_le_exponent
    {G X : Type} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := G) (X := X))
    (x : X) (k : ℕ) (hdegree : Nat.card X = 2 ^ k)
    (N : Subgroup G) [N.Normal] (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N + 1 ≤ k := by
  have hc : Nat.card G = 2 ^ k :=
    (ElementaryBinaryTransitiveNormalRank.card_eq_degree hel x).trans hdegree
  have hind : 2 ≤ N.index := N.one_lt_index_of_ne_top hproper
  have hmul := N.card_mul_index
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hlt : Nat.card N < 2 ^ k := by nlinarith
  have hpow := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card N
  have hpowlt : 2 ^ MarkedC4.normalGen N < 2 ^ k := hpow.trans_lt hlt
  have hrank := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpowlt
  omega

namespace BinaryPairFrame

variable {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- A full actual top image makes the SAME correlated pair kernel an
elementary supplement. A proper normal therefore saves one whole-group
generator, independently of the size or splitting of the kernel. -/
theorem normalGen_add_one_le_top_of_full_actual_image
    (hU : IsPGroup 2 U) (N : Subgroup U) [N.Normal]
    (himage : N.map F.top.rangeRestrict = ⊤) (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N + 1 ≤ MarkedC4.normalGen (⊤ : Subgroup U) := by
  letI := Fintype.ofFinite I
  let f := F.top.rangeRestrict
  have hker : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  have hsup : F.top.ker ⊔ N = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨n, hn, hng⟩ :=
      show f g ∈ N.map f by rw [himage]; trivial
    have hk : g * n⁻¹ ∈ F.top.ker := by
      rw [← hker]
      change f (g * n⁻¹) = 1
      rw [map_mul, map_inv, hng]
      exact mul_inv_cancel _
    have hprod : (g * n⁻¹) * n ∈ F.top.ker ⊔ N :=
      (F.top.ker ⊔ N).mul_mem
        ((show F.top.ker ≤ F.top.ker ⊔ N from le_sup_left) hk)
        ((show N ≤ F.top.ker ⊔ N from le_sup_right) hn)
    simpa only [inv_mul_cancel_right] using hprod
  have hcomm : IsMulCommutative F.top.ker := IsMulCommutative.of_comm fun a b =>
    F.kernelChart.injective (by rw [map_mul, map_mul, mul_comm])
  have hexp (e : F.top.ker) : e ^ 2 = 1 := by
    apply F.kernelChart.injective
    rw [map_pow, map_one]
    change (2 : ℕ) • (F.kernelChart e).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  exact normalGen_add_one_le_top_of_elementary_supplement
    2 hU F.top.ker N hsup hcomm hexp hproper

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
