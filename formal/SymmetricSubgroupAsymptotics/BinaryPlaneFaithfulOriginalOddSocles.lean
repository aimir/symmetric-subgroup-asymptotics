import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOrder
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import SymmetricSubgroupAsymptotics.LinearThreeSolvable

/-! Every literal original quotient has nonbinary-primary socle bound
one. Solvability and the single cubic order factor are proved from the
actual elementary kernel and faithful A4/S4 top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOddSocles
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)

theorem normalGen_le_one {G : Type} [Group G] [Finite G]
    (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (pi : G →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) [Finite A]
    (E : OriginalKernelModuleChart pi A) (N : Subgroup G) [N.Normal] :
    MarkedC4.normalGen
      (minimalNormalSoclePart (G ⧸ N) (fun M => ¬ IsPGroup 2 M))≤1 := by
  letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
  letI : IsSolvable C := solvable_of_solvable_injective hinj
  letI : IsSolvable pi.ker := isSolvable_of_comm (fun x y =>
    E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm]))
  letI : IsSolvable G := solvable_of_ker_le_range pi.ker.subtype pi
    (by rw [Subgroup.range_subtype])
  obtain ⟨k,hG⟩ := BinaryPlaneFaithfulOriginalOrder.exists_single_cubic_order
    C hinj heven pi hpi A E
  have hdiv : Nat.card (G ⧸ N)∣2^k*3 := by
    simpa only [hG,Nat.mul_comm] using Subgroup.card_quotient_dvd_card N
  exact nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart hdiv

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOddSocles
