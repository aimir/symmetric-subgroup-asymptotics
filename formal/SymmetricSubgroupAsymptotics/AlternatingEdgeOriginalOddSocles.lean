import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalSocleCoinvariance
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOddSocles

/-! A literal elementary-binary extension of A4 has one cubic order
factor, so the nonbinary part of every original quotient socle costs one. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalOddSocles
open AlternatingEdgeOriginalSocleCoinvariance (Top)

theorem exists_single_cubic_order {G : Type} [Group G] [Finite G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) Top) [Finite A]
    (E : OriginalKernelModuleChart pi A) : ∃ k : ℕ, Nat.card G=3*2^k := by
  have hk : Nat.card pi.ker=2^Module.finrank (ZMod 2) A := by
    rw [← Nat.card_congr E.equiv.toEquiv]
    change Nat.card A=2^Module.finrank (ZMod 2) A
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hp := pi.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hpi,
    Nat.card_congr Subgroup.topEquiv.toEquiv,hk] at hp
  have hc : Nat.card Top=12 := alternatingGroup.card_of_card_eq_four (by simp)
  refine ⟨Module.finrank (ZMod 2) A+2,?_⟩
  rw [hc] at hp
  rw [← hp,pow_add]
  norm_num <;> ring

theorem normalGen_le_one {G : Type} [Group G] [Finite G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) Top) [Finite A]
    (E : OriginalKernelModuleChart pi A) (N : Subgroup G) [N.Normal] :
    MarkedC4.normalGen
      (minimalNormalSoclePart (G ⧸ N) (fun M => ¬ IsPGroup 2 M)) ≤ 1 := by
  letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
  letI : IsSolvable Top := solvable_of_solvable_injective
    (show Function.Injective (alternatingGroup (Fin 4)).subtype from fun _ _ h => Subtype.ext h)
  letI : IsSolvable pi.ker := isSolvable_of_comm (fun x y =>
    E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm]))
  letI : IsSolvable G := solvable_of_ker_le_range pi.ker.subtype pi
    (by rw [Subgroup.range_subtype])
  obtain ⟨k,hG⟩ := exists_single_cubic_order pi hpi A E
  have hdiv : Nat.card (G ⧸ N) ∣ 2^k*3 := by
    simpa only [hG,Nat.mul_comm] using Subgroup.card_quotient_dvd_card N
  exact nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart hdiv

end SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalOddSocles
