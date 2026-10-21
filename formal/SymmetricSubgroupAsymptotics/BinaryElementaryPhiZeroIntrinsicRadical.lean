import SymmetricSubgroupAsymptotics.BinaryElementaryCanonicalCarryTop
import SymmetricSubgroupAsymptotics.BinaryPairElementaryOriginalGraphRigidity
import SymmetricSubgroupAsymptotics.RepresentationRadicalFromActualGeneratorBasis
import SymmetricSubgroupAsymptotics.ActualGeneratorTupleFromFaithfulImage
import SymmetricSubgroupAsymptotics.RepresentationCoordinateChangeRadical

/-! Four actual original generators identify the entire intrinsic
radical of the elementary phi-zero module. Only44 generator/basis
columns are checked; no full source-row displacement table is needed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroIntrinsicRadical
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryElementary16GraphHeadRigidity
private def inclusion : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 16 5
    (![65280,135,75,45,30] : Fin 5 → ℕ)).mulVecLin
private def dualMasks : Fin 5 → ℕ := ![32768,128,64,32,16]
private def coordinates : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 5 16
    (fun i => binaryVectorMask (fun j => binaryVectorOfMask 16 (dualMasks j) i))).mulVecLin
private theorem basis_left : ∀ i : Fin 5, coordinates (inclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem left_inverse (v : Fin 5 → ZMod 2) : coordinates (inclusion v) = v := by
  have he : coordinates.comp inclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 5 → ZMod 2) = c • Pi.single i 1 := by
      funext j
      simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,basis_left,LinearMap.id_apply]
  exact DFunLike.congr_fun he v

def radical : BinaryCoordinateSpace 16 5 := ⟨inclusion,coordinates,left_inverse⟩
private theorem kill_basis : ∀ i : Fin 4, ∀ j : Fin 11,
    action i ((stateChart 0).inclusion (Pi.single j 1)) -
      (stateChart 0).inclusion (Pi.single j 1) ∈ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem generator_top_original : ∀ i : Fin 4, generatorTop i = 1 ∨
    ∃ j : Fin 3, generatorTop i = BinaryMenuCayley8T3.generators j := by decide +kernel
private theorem generator_offset_kernel : ∀ i : Fin 4,
    generatorOffset i ∈ (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem canonical_rows : ∀ i : Fin 4, ∀ x : Fin 16,
    binaryEightCanonicalPairFrame.affinePermutation (generatorTop i) (generatorOffset i) x =
      BinaryElementary16PhiZeroOuterCarries.generators i x := by decide +kernel

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin 8))

theorem original_radical_eq
    (hzero : U = E.splitAffineAction)
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : (E.originalCoordinateSubrepresentation W).toSubmodule = (stateChart 0).space)
    (hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 6) :
    ((Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype).map
      E.originalCoordinateEquiv.toLinearMap = radical.space := by
  have ht (i : Fin 4) : generatorTop i ∈ E.top.range := by
    rcases generator_top_original i with h | ⟨j,h⟩
    · rw [h];exact E.top.range.one_mem
    · rw [h,hH];exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 4) : generatorOffset i ∈ E.kernelSpace := by
    rw [hK];exact generator_offset_kernel i
  let u : Fin 4 → U := fun i => E.originalZeroRow hzero ⟨generatorTop i,ht i⟩
    (generatorOffset i) (ha i)
  let e := E.canonicalPointLabels.permCongrHom
  let j : U →* Equiv.Perm (Fin 16) := e.toMonoidHom.comp U.subtype
  have hj : Function.Injective j := e.injective.comp Subtype.val_injective
  have hju (i : Fin 4) : j (u i) = BinaryElementary16PhiZeroOuterCarries.generators i := by
    change E.canonicalPointLabels.permCongrHom
      (E.affinePermutation (generatorTop i) (generatorOffset i)) = _
    exact (E.canonical_affinePermutation _ _).trans (Equiv.ext (canonical_rows i))
  have hrange : j.range = U.map e.toMonoidHom := by
    ext p
    constructor
    · rintro ⟨a,rfl⟩;exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩;exact ⟨⟨a,ha⟩,rfl⟩
  have hfullimage : j.range = Subgroup.closure
      (Set.range BinaryElementary16PhiZeroOuterCarries.generators) :=
    hrange.trans (E.canonical_elementary_four_closure hzero hH hK)
  obtain ⟨v,hv,hfull⟩ := exists_actual_generating_tuple_of_injective_image
    j hj BinaryElementary16PhiZeroOuterCarries.generators hfullimage
  have he : v = u := funext fun i => hj ((hv i).trans (hju i).symm)
  rw [he] at hfull
  have hact (i : Fin 4) : E.originalCoordinateRepresentation (u i) = action i :=
    E.originalCoordinateRepresentation_zeroRow hzero ⟨generatorTop i,ht i⟩ _ (ha i)
  have hc : Module.finrank (ZMod 2)
      (E.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants ≤ 6 := by
    rw [← E.originalCoordinateSubrepresentation_head W];exact hcap
  have hr := representation_radical_eq_of_actual_generators_basis E.originalCoordinateRepresentation
    (E.originalCoordinateSubrepresentation W) (stateChart 0) radical u hfull hW
    (fun i l => by rw [hact];exact kill_basis i l) hc (by decide : 11 = 5 + 6)
  exact (RepresentationCoordinateChange.subrepresentation_radical
    (permutationFunctionRepresentation (ZMod 2) U X) E.originalCoordinateEquiv W).trans hr

end SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroIntrinsicRadical
