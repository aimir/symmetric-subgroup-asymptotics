import SymmetricSubgroupAsymptotics.FourPointBlockTwoClassOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FourPointBlockDistinctClassesOrdinaryGenerators
import SymmetricSubgroupAsymptotics.BinaryPlaneSingleClassOrdinaryGenerators
import SymmetricSubgroupAsymptotics.HomogeneousFourPointPartition
import SymmetricSubgroupAsymptotics.OriginalFourPointSharedChooseCost
import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics

/-! The literal degree-sixteen source with a primitive affine four-point
component pays the sharp floor. The actual odd-kernel partition has one,
two, or four classes. One class uses its actual half translation bound;
two classes share one odd and one sign seed; four classes have one
translation seed. The zero-odd case retains the primitive native top
injection. No global generator bound or smaller-action input occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalFourPointSixteenSharpStep
open OriginalAffineBlockCharacteristicHead FourPointBlockAffineCoordinates
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_six (hfour : Nat.card block.Fibre = 4) (hn : n = 16) :
    MarkedC4.genRank J ≤ 6 := by
  have hproduct : 4*Nat.card block.Points = n := by
    simpa only [hfour,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 4 := by omega
  have htF : Fintype.card block.Points = 4 := by rw [Fintype.card_eq_nat_card,ht]
  have htop : MarkedC4.genRank block.Top ≤ 2 :=
    SmallFourPointOrdinaryGenerators.genRank_le_two ht
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 2 := by exact_mod_cast htop
  have hdpos : 0 < translationDimension J block P :=
    (P.elementaryChart block.component_preprimitive).d_pos
  have hpow : P.p^translationDimension J block P = 4 :=
    (fibre_card_eq_prime_pow_dimension J block P).symm.trans hfour
  have hpdiv : P.p ∣ 2^2 := by
    change P.p ∣ 4
    rw [←hpow]
    exact dvd_pow_self _ hdpos.ne'
  have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime Nat.prime_two hpdiv
  have hd : translationDimension J block P = 2 := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (by simpa only [hp] using hpow)
  have hdiv : 2^2 ∣ Fintype.card block.Points := by rw [htF]; decide
  let C := linearImage block.map block.map_equivariant block.base hfour
  by_cases hO : oddKernel C = ⊥
  · have hh := OriginalFourPointZeroOddCharacteristicCost.genRank_le_primary_choose
      J block P hfour hp hO block.base 2 hdiv
    norm_num [hd,htF,ActualWreathChooseDivisorCapacity.primaryRate] at hh
    exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 6 by linarith)
  have htrans := image_transitive block.map block.map_equivariant block.base hfour
  have hpartition := HomogeneousFourPointPartition.single_or_two_or_injective
    (localKernel C) ht (by
      intro i j
      obtain ⟨h,hh⟩ := htrans i j
      refine ⟨MulAction.toPerm (h : LinearFrame (G := J) (X := block.Points)).right,hh,?_⟩
      intro x y
      exact BinaryPlaneOddKernelMultiplicityUniform.kernel_covariance C h x y)
  rcases hpartition with ⟨i,hsingle⟩ | ⟨i,j,hne,hcover⟩ | hinj
  · have htopSurj : Function.Surjective (PermutationalWreathProduct.rightHom.comp C.subtype) := by
      intro q
      obtain ⟨g,hg⟩ := (ActualBlockWreathEmbedding.topMap (A := J) (X := block.Points)).rangeRestrict_surjective q
      refine ⟨projection block.map block.map_equivariant block.base hfour g,?_⟩
      change (linearMap block.map block.map_equivariant block.base hfour g).right = q
      rw [linearMap_right]
      exact hg
    have hnative : MarkedC4.genRank C ≤ MarkedC4.genRank block.Top + 2 :=
      BinaryPlaneSingleClassOrdinaryGenerators.genRank_le_top_add_two C htopSurj i hsingle
        (all_local_nontrivial C hO htrans i)
    have hq : MarkedC4.genRank (quotientState J block P).A ≤ 4 := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (OriginalFourPointZeroOddCharacteristicCost.quotientStateEquivLinearImage J block P hfour hp)]
      change MarkedC4.genRank C ≤ 4
      omega
    have hh := OriginalFourPointSharedTranslationKernel.genRank_le_half_add_quotient
      J block P hfour hp hO
    rw [ht] at hh
    omega
  · exact FourPointBlockTwoClassOrdinaryGenerators.genRank_le_six_of_four_blocks
      block.map block.map_equivariant block.base hfour ht hO i j hne hcover
  · have htail := ActualWreathSixOrderChooseCost.genRank_le_primary_choose_add_primeTo
      (quotientState J block P) block.base (by omega : 2 ≤ Fintype.card block.Points)
      (OriginalFourPointSharedChooseCost.quotientState_card_dvd_six J block P hp hd) 2 hdiv
    norm_num [htF,ActualWreathChooseDivisorCapacity.primaryRate] at htail
    have hq : MarkedC4.genRank (quotientState J block P).A ≤ 5 := by
      exact_mod_cast (show (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤ 5 by linarith)
    have hnative : MarkedC4.genRank C ≤ 5 := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (OriginalFourPointZeroOddCharacteristicCost.quotientStateEquivLinearImage J block P hfour hp)] at hq
      exact hq
    have hh := FourPointBlockDistinctClassesOrdinaryGenerators.genRank_le_image_add_one
      block.map block.map_equivariant block.base hfour hO hinj
    change MarkedC4.genRank J ≤ MarkedC4.genRank C + 1 at hh
    omega

include P in
theorem genRank_le_sharpFloor (hfour : Nat.card block.Fibre = 4) (hn : n = 16) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  have hsix : 6 ≤ sharpFloor 16 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
    16 6 4 (by decide)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 16 4 (by decide) (by decide)) (by decide)
  exact (genRank_le_six J block P hfour hn).trans (by simpa only [hn] using hsix)

include P in
theorem exists_generating_finset (hfour : Nat.card block.Fibre = 4) (hn : n = 16) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_sharpFloor J block P hfour hn)⟩

end SymmetricSubgroupAsymptotics.OriginalFourPointSixteenSharpStep
