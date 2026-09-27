import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.DegreeTwentySevenClosure
import SymmetricSubgroupAsymptotics.TransitiveTernaryStability

/-!
# The three-by-two degree-six owner

Suppose a transitive degree-six action is presented by an actual minimal
block system with three points in each of two blocks.  The faithful top on
the two blocks has order two.  If one fibre contains an inversion, the
signed ternary-coordinate theorem annihilates the complete relative
3-head.  Hence a high normal pair forces every fibre sign to be trivial;
the literal block kernel is then a normal 3-group of index two.  This is
exactly the first intrinsic earlier-owner witness, with no finite catalogue.
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
/-- The actual faithful top of a two-block transitive action has order two. -/
theorem twoBlock_top_card [Finite A] [Finite Ω]
    (hPoints : Nat.card D.Points = 2) : Nat.card D.Top = 2 := by
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : Finite D.Top := D.top_finite
  have hPerm : Nat.card (Equiv.Perm D.Points) = 2 := by
    rw [Nat.card_perm, hPoints]
    norm_num
  have hUpper : Nat.card D.Top ≤ 2 := by
    have h := Subgroup.card_le_card_group D.Top
    simpa only [hPerm] using h
  have hIndex : (MulAction.stabilizer D.Top D.base).index = 2 := by
    simpa only [hPoints] using
      MulAction.index_stabilizer_of_transitive D.Top D.base
  have hMul := (MulAction.stabilizer D.Top D.base).card_mul_index
  rw [hIndex] at hMul
  have hStabilizerPos : 0 < Nat.card (MulAction.stabilizer D.Top D.base) :=
    Nat.card_pos
  omega

include D in
/-- In the three-point-fibre branch, every high normal pair produces an
actual normal 3-subgroup of index two in the original group. -/
theorem degreeSix_ternaryBlock_owner
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hPoints : Nat.card D.Points = 2)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) := by
  letI : Nonempty Ω := ⟨ω₀⟩
  letI : Fintype D.Points := Fintype.ofFinite _
  letI (x : D.Points) : Fintype (originalBlockFibre D.map x) :=
    Fintype.ofFinite _
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  let e := D.ternaryFibreCharts hFibre
  have hTopCard : Nat.card D.Top = 2 := D.twoBlock_top_card hPoints
  have hTopPGroup : IsPGroup 2 D.Top :=
    IsPGroup.of_card (n := 1) (by simpa using hTopCard)
  have hSigns :
      DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant = 1 := by
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
    let T := originalNormalRange D.topMap N
    have hTPGroup : IsPGroup 2 T := hTopPGroup.to_subgroup T
    have hTopZero : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 T) = 0 :=
      primeRelativeHead_power_group 3 T 2 (by decide) hTPGroup
    have hHead :=
      DegreeThreeBlockInversionHead.originalNormal_primeRelativeHead_le_top
        (hb := D.map_equivariant) D.map N e x₀ hx₀
    change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) at hHead
    rw [hTopZero] at hHead
    have hΩpos : 0 < Nat.card Ω := Nat.card_pos
    omega
  refine ⟨{
      ternary := D.topMap.ker
      normal := inferInstance
      ternaryPGroup :=
        DegreeThreeBlockInversionHead.kernel_isPGroup_of_coordinateSigns_eq_one
          (hb := D.map_equivariant) D.map e hSigns
      index_two := ?_ }⟩
  rw [Subgroup.index_ker]
  exact hTopCard

end OriginalMinimalBlock

/-- Every high degree-six pair either already has the normal index-two
ternary owner, or its internally selected minimal block system is the sole
remaining two-by-three binary-block branch. -/
theorem degreeSix_high_oddIndexOwner_or_binaryBlock
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 6)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀),
        Nat.card D.Fibre = 2 ∧ Nat.card D.Points = 3 := by
  have hΩtwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩtwo
  have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
    intro hp
    letI : MulAction.IsPreprimitive A Ω := hp
    have hSafe := hPrimitive A Ω (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 6 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hfactors : (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) := by
    have hrdiv : r ∣ 6 := ⟨s, hrs.symm⟩
    have hrle : r ≤ 6 := Nat.le_of_dvd (by decide) hrdiv
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  rcases hfactors with hrs23 | hrs32
  · exact Or.inr ⟨ω₀, D, by simpa only [r] using hrs23.1,
      by simpa only [s] using hrs23.2⟩
  · exact Or.inl (D.degreeSix_ternaryBlock_owner N
      (by simpa only [r] using hrs32.1)
      (by simpa only [s] using hrs32.2) hHigh)

end SymmetricSubgroupAsymptotics

end
