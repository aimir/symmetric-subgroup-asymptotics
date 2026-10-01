import SymmetricSubgroupAsymptotics.AbelianKernelLocalChiefDescent
import SymmetricSubgroupAsymptotics.DegreeTwentySevenClosure
import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockOwner
import SymmetricSubgroupAsymptotics.SmallTransitiveTernaryHead

/-!
# The three-by-six degree-eighteen head bound

For blocks of size three with a degree-six top, a nontrivial fibre sign
annihilates the kernel contribution.  If all signs vanish, the literal block
kernel is an abelian 3-group.  Its local chief series then descends to the
faithful degree-six top and is controlled by the already proved odd-index-two
or cyclic-binary owner.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [Finite A] [Finite Ω] [MulAction.IsPretransitive A Ω]
variable [FaithfulSMul A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The image of the original stabilizer of a block is exactly the point
stabilizer in the faithful top action. -/
theorem topRange_stabilizer_image (x : D.Points) :
    subgroupImage D.topMap.rangeRestrict (MulAction.stabilizer A x) =
      MulAction.stabilizer D.Top x := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hq
    obtain ⟨a, ha⟩ := D.topMap.rangeRestrict_surjective q
    have hax : a • x = x := by
      change D.topMap a x = x
      have hq' : (q : Equiv.Perm D.Points) x = x := hq
      calc
        D.topMap a x = (q : Equiv.Perm D.Points) x := by
          exact congrArg (fun r : D.Top => (r : Equiv.Perm D.Points) x) ha
        _ = x := hq'
    exact ⟨a, hax, ha⟩

/-- The literal block kernel is contained in every block stabilizer. -/
theorem topRange_kernel_le_stabilizer (x : D.Points) :
    D.topMap.rangeRestrict.ker ≤ MulAction.stabilizer A x := by
  intro a ha
  change a • x = x
  have h := congrArg (fun q : D.Top => (q : Equiv.Perm D.Points) x)
    (MonoidHom.mem_ker.mp ha)
  simpa using h

/-- A degree-six top with relative head one supplies exactly the owner form
needed by the sharp abelian-kernel recurrence. -/
theorem degreeSix_top_cosetOwner_or_cyclic
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (T : Subgroup D.Top) [T.Normal]
    (hPoints : Nat.card D.Points = 6)
    (hT : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 1) :
    (∃ g : D.Top,
      MulAction.IsPretransitive (Subgroup.zpowers g)
        (D.Top ⧸ subgroupImage D.topMap.rangeRestrict
          (MulAction.stabilizer A D.base))) ∨
      (∃ W : C1CyclicBinaryModuleOwnerWitness D.Top,
        Nat.card W.complement = 3) := by
  letI : Finite D.Top := D.top_finite
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  have hHigh : 3 * Nat.card D.Points <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) := by
    rw [hPoints, hT]
    norm_num
  rcases degreeSix_high_structuralOwnerWithComplementCard
      hPrimitive T hPoints hHigh with hOdd | ⟨W, hW⟩
  · left
    obtain ⟨W⟩ := hOdd
    have hTne : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 T) ≠ 0 := by omega
    obtain ⟨g, hg⟩ := W.exists_six_cycle_of_relativeHead_ne_zero
      hPoints T hTne
    refine ⟨g, ?_⟩
    letI : MulAction.IsPretransitive (Subgroup.zpowers g) D.Points := hg
    have hc : MulAction.IsPretransitive (Subgroup.zpowers g)
        (D.Top ⧸ MulAction.stabilizer D.Top D.base) :=
      cyclicQuotientStabilizer_pretransitive g D.base
    rw [D.topRange_stabilizer_image D.base]
    exact hc
  · exact Or.inr ⟨W, hW⟩

include D in
/-- In the all-even branch, the original intersection with the block kernel
has relative head at most one. -/
theorem threeBySix_allEven_kernelIntersection_head_le_one
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hPoints : Nat.card D.Points = 6)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (hSigns : DegreeThreeBlockInversionHead.coordinateSigns
      D.map D.map_equivariant = 1) :
    Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ D.topMap.ker)) ≤ 1 := by
  letI : Fintype D.Points := Fintype.ofFinite _
  let P : Subgroup A := N ⊓ D.topMap.ker
  letI : P.Normal := inferInstance
  let H : Subgroup A := MulAction.stabilizer A D.base
  let π : A →* D.Top := D.topMap.rangeRestrict
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  let c := actualChiefSeries D.Component
  have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
    permutationChiefWeight_le_one_of_card_le_five D.Component c (by
      rw [hFibre]
      norm_num)
  have hπker : π.ker = D.topMap.ker := MonoidHom.ker_rangeRestrict D.topMap
  letI : IsMulCommutative π.ker := by
    rw [hπker]
    exact DegreeThreeBlockInversionHead.kernel_isMulCommutative_of_coordinateSigns_eq_one
      (hb := D.map_equivariant) D.map (D.ternaryFibreCharts hFibre) hSigns
  have hP : P ≤ π.ker := by
    rw [hπker]
    exact inf_le_right
  have hKH : π.ker ≤ H := by
    exact D.topRange_kernel_le_stabilizer D.base
  let T := originalNormalRange D.topMap N
  letI : T.Normal := originalNormalRange_normal D.topMap N
  have hT : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 1 := by
    simpa only [T] using hTop
  have hOwner := D.degreeSix_top_cosetOwner_or_cyclic hPrimitive T hPoints hT
  have hSharp := actualLocalChiefHead_le_weight_of_owners
    π D.topMap.rangeRestrict_surjective P H hP hKH
    (originalBlockEvaluation D.map D.map_equivariant D.base P inf_le_right)
    (originalBlockProjection D.map D.map_equivariant D.base)
    (originalBlockEvaluation_conjugation D.map D.map_equivariant D.base P inf_le_right)
    (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    (originalBlockEvaluation_conjugates_separate
      D.map D.map_equivariant D.base P inf_le_right) c hOwner
  exact hSharp.trans hc

include D in
/-- Every normal pair in the three-by-six degree-eighteen orientation has
ternary relative head at most two. -/
theorem degreeEighteen_threeBySix_ternaryHead_le_two
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hPoints : Nat.card D.Points = 6) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 := by
  letI : Fintype D.Points := Fintype.ofFinite _
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite _
  let T := originalNormalRange D.topMap N
  letI : T.Normal := originalNormalRange_normal D.topMap N
  letI : Finite D.Top := D.top_finite
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  have hTopLe := transitive_degreeSix_ternaryHead_le_one hPrimitive T hPoints
  by_cases hTopZero : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 0
  · letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    let c := actualChiefSeries D.Component
    have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
      permutationChiefWeight_le_one_of_card_le_five D.Component c (by
        rw [hFibre]
        norm_num)
    have h := D.head_bound_nat N c
    rw [show Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 0 by
        simpa only [T] using hTopZero] at h
    rw [hPoints, ternaryIndexWidth_six, add_zero] at h
    omega
  · have hTopOne : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 T) = 1 := by omega
    let e := D.ternaryFibreCharts hFibre
    by_cases hSigns : DegreeThreeBlockInversionHead.coordinateSigns
        D.map D.map_equivariant = 1
    · have hKernel := D.threeBySix_allEven_kernelIntersection_head_le_one
        hPrimitive N hFibre hPoints (by simpa only [T] using hTopOne) hSigns
      have hchain := primeRelativeHead_chain_le (N ⊓ D.topMap.ker) N 3 inf_le_left
      rw [primeRelativeHead_second_isomorphism 3 N D.topMap.ker,
        primeRelativeHead_original_range 3 D.topMap N] at hchain
      change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (N ⊓ D.topMap.ker)) +
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) at hchain
      omega
    · have hx : ∃ x : D.Points,
          OriginalBlockSignCoordinates.coordinateSign
            D.map D.map_equivariant x ≠ 1 := by
        by_contra h
        push_neg at h
        apply hSigns
        apply MonoidHom.ext
        intro k
        funext x
        have hx := congrArg (fun f :
          DegreeThreeBlockInversionHead.Kernel (A := A) (X := D.Points) →*
            Multiplicative (ZMod 2) => f k) (h x)
        simpa only [map_one] using hx
      obtain ⟨x, hx⟩ := hx
      have hInv := DegreeThreeBlockInversionHead.originalNormal_primeRelativeHead_le_top
        (hb := D.map_equivariant) D.map N e x hx
      change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) at hInv
      omega

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics

end
