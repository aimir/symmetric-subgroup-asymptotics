import SymmetricSubgroupAsymptotics.BinaryPairFrameOrientation
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointSplitModels
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointWidthRankModels

/-! Joint rank/width saturation yields zero affine frames on the SAME
original degree-sixteen source, retaining the exact actual kernel radical. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem affineGeneratedModel_zero_eq_split {J : Type} (u : J → U)
    (hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range) :
    F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) =
      F.splitAffineAction :=
  (F.splitAffinePermutationHom_range_eq_generated_model u hgen).symm.trans
    F.splitAffinePermutationHom_range

theorem eq_reoriented_split_of_generated_conjugate {J : Type} (u : J → U)
    (hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range)
    (a : Fin w → ZMod 2)
    (hconj : U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom =
      F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0)) :
    U = (F.reorient a).splitAffineAction :=
  F.eq_reoriented_split_of_conjugate a
    (hconj.trans (F.affineGeneratedModel_zero_eq_split u hgen))

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

include F

/-- The only two source templates at the joint frontier have literal
zero frames on the original points and original group, with their original
kernel and intrinsic radical still identified. -/
theorem exists_joint_zero_frame
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 6 ≤ MarkedC4.genRank U)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    ∃ E : BinaryPairFrame U (Fin 8), U = E.splitAffineAction ∧
      ((E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ∧
        E.kernelSpace = BinaryRegularEightSquareCarry.K46 ∧
        E.ambientAxis (primeRelativeRadical 2 E.top.ker) = BinaryRegularEightSquareCarry.R46) ∨
      (E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) ∧
        E.kernelSpace = BinaryHeisenbergEightSquareCarry.K14 ∧
        E.ambientAxis (primeRelativeRadical 2 E.top.ker) = BinaryHeisenbergEightSquareCarry.R14)) := by
  rcases SymmetricSubgroupAsymptotics.BinaryPairFrame.six_le_rank_four_le_head_literal_kernel_models
      F hU hhigh W hwide with
    ⟨g,hH,hK,hR⟩ | ⟨g,hH,hK,hR⟩
  · let E := F.reindex g
    obtain ⟨u,a,hu,hconj⟩ := E.regular46_joint_exists_zero_offset_model hU hhigh hH hK hR
    have hgen : Subgroup.closure (Set.range fun i => E.top (u i)) = E.top.range := by
      rw [show (fun i => E.top (u i)) = BinaryMenuCayley8T3.generators from funext hu,← hH]
    refine ⟨E.reorient a,E.eq_reoriented_split_of_generated_conjugate u hgen a hconj,Or.inl ?_⟩
    simpa only [reorient_top,reorient_kernelSpace,reorient_ambientAxis] using
      (show E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ∧
        E.kernelSpace = BinaryRegularEightSquareCarry.K46 ∧
        E.ambientAxis (primeRelativeRadical 2 E.top.ker) = BinaryRegularEightSquareCarry.R46 from
          ⟨hH,hK,hR⟩)
  · let E := F.reindex g
    obtain ⟨u,a,hu,hconj⟩ := E.heisenberg14_joint_exists_zero_offset_model hU hhigh hH hK hR
    have hgen : Subgroup.closure (Set.range fun i => E.top (u i)) = E.top.range := by
      rw [show (fun i => E.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected from funext hu,
        BinaryHeisenbergEightSquareCarry.selected_closure_eq_original,← hH]
    refine ⟨E.reorient a,E.eq_reoriented_split_of_generated_conjugate u hgen a hconj,Or.inr ?_⟩
    simpa only [reorient_top,reorient_kernelSpace,reorient_ambientAxis] using
      (show E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) ∧
        E.kernelSpace = BinaryHeisenbergEightSquareCarry.K14 ∧
        E.ambientAxis (primeRelativeRadical 2 E.top.ker) = BinaryHeisenbergEightSquareCarry.R14 from
          ⟨hH,hK,hR⟩)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
