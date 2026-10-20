import SymmetricSubgroupAsymptotics.SixPairElementaryCubicObservation
import SymmetricSubgroupAsymptotics.ElementaryBinaryKernelOriginalChart
import SymmetricSubgroupAsymptotics.OriginalKernelCubicObservationDualSections
import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelTwoEnvelope
import SymmetricSubgroupAsymptotics.TransitiveThreePointQuotientType
import SymmetricSubgroupAsymptotics.SixPairAbelianKernelOrder

/-! Every original normal quotient of an elementary coarse kernel keeps
its exact kernel section, actual residual top and complete source fibre.
The two dual generators come from proved original physical observations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairElementaryCoarseKernelQuotientSum
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart
variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

 theorem kernel_commutative
    (hsquare : ∀ k : (SixPairNestedTopFrames.nestedFrame F E).top.ker,k^2=1)
    (a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker) : a*b=b*a := by
  have hi (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker) : x⁻¹=x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare x)
  calc
    a*b=(a*b)⁻¹ := (hi _).symm
    _=b⁻¹*a⁻¹ := mul_inv_rev _ _
    _=b*a := by rw [hi,hi]

 theorem original_order_le_nine
    (hsquare : ∀ k : (SixPairNestedTopFrames.nestedFrame F E).top.ker,k^2=1) : Nat.card U≤2^9 :=
  SixPairAbelianKernelOrder.original_card_le F E (kernel_commutative F E hsquare)

 theorem quotient_sum_le [MulAction.IsPretransitive U X]
    (hsquare : ∀ k : (SixPairNestedTopFrames.nestedFrame F E).top.ker,k^2=1)
    (hKP : KovacsPraegerAbelianizationBound)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ))≤
      BinaryKernelRankTailNumerics.raw 1 15 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let T := C.top.range
  let pi := C.top.rangeRestrict
  have hpi : Function.Surjective pi := C.top.rangeRestrict_surjective
  have hk : pi.ker=C.top.ker := by
    ext g
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hsquarePi (k : pi.ker) : k^2=1 := by
    apply (MulEquiv.subgroupCongr hk).injective
    rw [map_pow,map_one]
    exact hsquare _
  let A := ElementaryBinaryKernelOriginalChart.kernelModule pi hpi hsquarePi
  let D := ElementaryBinaryKernelOriginalChart.originalChart pi hpi hsquarePi
  let cubic := TwoBinaryThreePermutationCoordinates.cubicHom T
    (ThreePointTransitiveCubicMembership.frame_rotation_mem C
      (fun x y => MulAction.exists_smul_eq U x y))
  obtain ⟨q,hq⟩ := SixPairElementaryCubicObservation.exists_separating_observation F E A D hsquarePi
  have hgen := D.sectionDualGeneratedBy_two_of_cubic_observation pi A hpi cubic q hq N
  let R := U ⧸ (pi.ker ⊔ N)
  let rho : T →* R := sectionTop pi N hpi
  have hrho : Function.Surjective rho := by
    intro r
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) r
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  letI : MulAction.IsPretransitive T (Fin 3) :=
    ⟨C.top_range_transitive (fun x y => MulAction.exists_smul_eq U x y)⟩
  have htype := TransitiveThreePointQuotientType.cyclic_or_symmetric T rho hrho
  have hTcard : Nat.card R≤6 := (Nat.card_le_card_of_surjective rho hrho).trans
    (FiniteTopKernelHomLiftCount.top_card_le_six T.subtype Subtype.val_injective)
  have hQ : Nat.card (U ⧸ N)≤2^9 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (original_order_le_nine F E hsquare)
  exact FiniteTopBinaryDualKernelTwo.raw_sum_le (base pi N) (base_surjective pi N)
    (D.sectionRepresentation pi A N) (D.quotientChart pi A N) hgen hTcard hQ htype hKP b

end SymmetricSubgroupAsymptotics.SixPairElementaryCoarseKernelQuotientSum
