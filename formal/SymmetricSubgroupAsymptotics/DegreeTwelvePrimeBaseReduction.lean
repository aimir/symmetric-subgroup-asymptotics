import SymmetricSubgroupAsymptotics.DegreeTwelveTopGeometry
import SymmetricSubgroupAsymptotics.DegreeTwentySevenClosure

/-!
# The ternary prime-base reduction in degree twelve

In the saturated `3 × 4` branch the original relative ternary head has
rank two, whereas the original normal top image has rank one.  A nontrivial
sign on any three-point fibre would force the former rank below the latter.
Consequently every fibre sign is trivial and the literal block kernel is a
3-group.  This is the first structural part of the prime-base owner; it keeps
the actual minimal block system and makes no appeal to the degree-twelve
action catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

include D in
/-- In a three-point-fibre block system, a strict rank gain from the literal
top to the original normal subgroup kills every fibre inversion. -/
theorem ternaryBlock_coordinateSigns_eq_one_of_rank_gt_top
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    [Fintype D.Points]
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) <
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant = 1 := by
  letI : Nonempty Ω := ⟨ω₀⟩
  let e := D.ternaryFibreCharts hFibre
  by_contra hSigns
  have hexists : ∃ x : D.Points,
      OriginalBlockSignCoordinates.coordinateSign D.map D.map_equivariant x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    apply hSigns
    apply MonoidHom.ext
    intro k
    funext x
    simpa only [DegreeThreeBlockInversionHead.coordinateSigns,
      MonoidHom.one_apply] using DFunLike.congr_fun (h x) k
  obtain ⟨x₀, hx₀⟩ := hexists
  have hHead :=
    DegreeThreeBlockInversionHead.originalNormal_primeRelativeHead_le_top
      (hb := D.map_equivariant) D.map N e x₀ hx₀
  change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
    Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) at hHead
  omega

include D in
/-- The literal kernel of a saturated `3 × 4` degree-twelve block system is
a 3-group.  The numerical equalities are kept explicit so this theorem is
reusable independently of the high-pair selector. -/
theorem degreeTwelve_ternaryBlock_kernel_isPGroup
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hOriginalRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 N) = 2)
    (hTopRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1) :
    IsPGroup 3 D.topMap.ker := by
  letI : Nonempty Ω := ⟨ω₀⟩
  letI : Fintype D.Points := Fintype.ofFinite _
  letI (x : D.Points) : Fintype (originalBlockFibre D.map x) :=
    Fintype.ofFinite _
  let e := D.ternaryFibreCharts hFibre
  have hRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) <
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
    omega
  have hSigns := D.ternaryBlock_coordinateSigns_eq_one_of_rank_gt_top
    N hFibre hRank
  exact
    DegreeThreeBlockInversionHead.kernel_isPGroup_of_coordinateSigns_eq_one
      (hb := D.map_equivariant) D.map e hSigns

omit [MulAction.IsPretransitive A Ω] in
include D in
/-- In the saturated `3 × 4` branch, the exact restriction sequence retains
one dimension of whole-ambient invariant characters on the physical
intersection of the original normal subgroup with the block kernel.  This is
the marking datum that rules out the augmentation-only kernel; merely knowing
that the block kernel is a 3-group would not do so. -/
theorem degreeTwelve_ternaryBlock_retained_finrank_eq_one
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hOriginalRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 N) = 2)
    (hTopRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1) :
    Module.finrank (ZMod 3)
        (normalChainRetainedCharacters (N ⊓ D.topMap.ker) N 3 inf_le_left) = 1 := by
  have hChain :=
    primeRelativeHead_chain_eq (N ⊓ D.topMap.ker) N 3 inf_le_left
  rw [primeRelativeHead_second_isomorphism 3 N D.topMap.ker,
    primeRelativeHead_original_range 3 D.topMap N] at hChain
  omega

omit [MulAction.IsPretransitive A Ω] in
include D in
/-- A literal nonzero retained character witnessing the one-dimensional
kernel contribution.  Keeping membership in the restriction range is
essential: the later invariant-submodule argument uses this exact
whole-ambient character, rather than an arbitrary character after shrinking
the acting group to the block kernel. -/
theorem degreeTwelve_ternaryBlock_exists_retained_character
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hOriginalRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 N) = 2)
    (hTopRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1) :
    ∃ χ : primeRelativeCharacters 3 (N ⊓ D.topMap.ker),
      χ ≠ 0 ∧
      χ ∈ normalChainRetainedCharacters (N ⊓ D.topMap.ker) N 3 inf_le_left := by
  let R := normalChainRetainedCharacters (N ⊓ D.topMap.ker) N 3 inf_le_left
  have hR : Module.finrank (ZMod 3) R = 1 :=
    D.degreeTwelve_ternaryBlock_retained_finrank_eq_one
      N hOriginalRank hTopRank
  have hpos : 0 < Module.finrank (ZMod 3) R := by omega
  letI : Nontrivial R := Module.finrank_pos_iff.mp hpos
  obtain ⟨η, hη⟩ := exists_ne (0 : R)
  refine ⟨η.1, ?_, η.2⟩
  intro hzero
  apply hη
  apply Subtype.ext
  exact hzero

end OriginalMinimalBlock

/-- The high degree-twelve structural fork, strengthened in the `3 × 4`
branch by the fact that its actual block kernel is a 3-group. -/
theorem degreeTwelve_high_primeBase_or_fourPointFibre
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀),
      ((Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 4 ∧
          IsNaturalA4Action D.Top D.Points ∧ IsPGroup 3 D.topMap.ker ∧
          Module.finrank (ZMod 3)
            (normalChainRetainedCharacters (N ⊓ D.topMap.ker) N 3 inf_le_left) = 1) ∨
        (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 3 ∧
          Nat.card D.Top = 3)) ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 ∧
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2 := by
  obtain ⟨ω₀, D, c, horient, _hv, ht, hd⟩ :=
    degreeTwelve_high_top_geometry
      hChief hWeight hPrimitive h18 N hDegree hHigh
  refine ⟨ω₀, D, ?_, ht, hd⟩
  rcases horient with h34 | h43
  · exact Or.inl ⟨h34.1, h34.2.1, h34.2.2,
      D.degreeTwelve_ternaryBlock_kernel_isPGroup N h34.1 hd ht,
      D.degreeTwelve_ternaryBlock_retained_finrank_eq_one N hd ht⟩
  · exact Or.inr h43

end SymmetricSubgroupAsymptotics

end
