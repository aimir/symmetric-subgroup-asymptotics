import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralLines
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointSplitModels
import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows
import SymmetricSubgroupAsymptotics.NormalFQuotientPacketTransport

/-! Transfer the three-denominator calculation through the actual original
point conjugation of every saturated K14 extension. Arbitrary original
normal denominators follow the SAME group equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryHeisenbergFourCentralModel

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

omit [Finite X] in
private theorem kernelSpace_eq_heisenberg_W
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14) : F.kernelSpace = W :=
  hK.trans BinaryHeisenbergEightNaturalHeads.kernel14_space.symm

/-- Both coordinate maps retain the original bit functions and top
permutations. The group law is therefore the same literal affine law. -/
def heisenbergFourSplitEquiv
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14) :
    F.SplitAffineModel ≃* Model where
  toFun g := ⟨Multiplicative.ofAdd
      ⟨g.left.toAdd.val, (F.kernelSpace_eq_heisenberg_W hK) ▸ g.left.toAdd.property⟩,
    ⟨g.right.val, by simpa only [hH] using g.right.property⟩⟩
  invFun g := ⟨Multiplicative.ofAdd
      ⟨g.left.toAdd.val, (F.kernelSpace_eq_heisenberg_W hK).symm ▸ g.left.toAdd.property⟩,
    ⟨g.right.val, by simpa only [hH] using g.right.property⟩⟩
  left_inv g := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      rfl
    · rfl
  right_inv g := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

theorem heisenbergFour_original_equiv
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) =
      BinaryHeisenbergEightSquareCarry.R14) : Nonempty (U ≃* Model) := by
  obtain ⟨u, a, hu, ha⟩ := F.heisenberg14_joint_exists_zero_offset_model
    hU hrank hH hK hR
  have hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range := by
    rw [show (fun i => F.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected
      from funext hu, BinaryHeisenbergEightSquareCarry.selected_closure_eq_original, ← hH]
  have hm : F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) =
      F.splitAffineAction :=
    (F.splitAffinePermutationHom_range_eq_generated_model u hgen).symm.trans
      F.splitAffinePermutationHom_range
  let c := MulAut.conj (F.physicalFlip a)
  let e : U ≃* F.splitAffineAction :=
    (c.subgroupMap U).trans (MulEquiv.subgroupCongr (ha.trans hm))
  exact ⟨(e.trans F.splitAffineModelEquiv.symm).trans (F.heisenbergFourSplitEquiv hH hK)⟩

theorem heisenbergFour_five_quarters_normalF_packet
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) =
      BinaryHeisenbergEightSquareCarry.R14)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  obtain ⟨e⟩ := F.heisenbergFour_original_equiv hU hrank hH hK hR
  exact NormalFEquivalenceTransport.quotient_packet_of_equiv e (5 / 4) 8 4
    BinaryHeisenbergFourCentralLines.all_nonabelian_quotients_normalF N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
