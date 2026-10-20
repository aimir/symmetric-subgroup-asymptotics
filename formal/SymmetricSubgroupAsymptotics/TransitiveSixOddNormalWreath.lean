import SymmetricSubgroupAsymptotics.ActualThreeByTwoWreathCard
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection

/-! A nontrivial odd-order normal subgroup of an actual faithful
transitive six-point group has two three-point orbits. Its ORIGINAL
ambient group consequently embeds in the actual three-by-two wreath. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)]
    [MulAction.IsPretransitive G (Fin 6)]
    (N : Subgroup G) [N.Normal]

private theorem divisor_six_eq_three (n : ℕ) (hd : n ∣ 6)
    (hne : n ≠ 1) (hodd : ¬ 2 ∣ n) : n = 3 := by
  have hn : n ≤ 6 := Nat.le_of_dvd (by decide) hd
  interval_cases n <;> norm_num at *

/-- Normality makes all orbits uniform; oddness and faithfulness exclude
all sizes other than three. -/
theorem transitiveSix_odd_normal_orbit_card
    (hN : N ≠ ⊥) (hodd : ¬ 2 ∣ Nat.card N) :
    Nat.card (MulAction.orbit N (0 : Fin 6)) = 3 := by
  have hp := normal_orbit_card_mul_classes N (0 : Fin 6)
  have hd : Nat.card (MulAction.orbit N (0 : Fin 6)) ∣ 6 := by
    exact ⟨Nat.card (MulAction.orbitRel.Quotient N (Fin 6)),by simpa only [Nat.card_fin] using hp.symm⟩
  have hdiv : Nat.card (MulAction.orbit N (0 : Fin 6)) ∣ Nat.card N := by
    rw [Nat.card_coe_set_eq,← MulAction.index_stabilizer]
    exact (MulAction.stabilizer N (0 : Fin 6)).index_dvd_card
  exact divisor_six_eq_three _ hd
    (normal_orbit_card_ne_one_of_ne_bot N hN 0)
    (fun h => hodd (h.trans hdiv))

/-- The block points are actual translates of the original normal orbit. -/
abbrev normalOrbitBlocks := MulAction.orbit G (MulAction.orbit N (0 : Fin 6))

def normalOrbitBlockMap : Fin 6 → normalOrbitBlocks N := fun x =>
  ⟨MulAction.orbit N x,by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (0 : Fin 6) x
    refine ⟨g,?_⟩
    change g • MulAction.orbit N (0 : Fin 6) = MulAction.orbit N x
    rw [MulAction.smul_orbit_eq_orbit_smul,hg]⟩

theorem normalOrbitBlockMap_equivariant (g : G) (x : Fin 6) :
    normalOrbitBlockMap N (g • x) = g • normalOrbitBlockMap N x := by
  apply Subtype.ext
  exact (MulAction.smul_orbit_eq_orbit_smul N x g).symm

def normalOrbitBase : normalOrbitBlocks N :=
  ⟨MulAction.orbit N (0 : Fin 6),MulAction.mem_orbit_self _⟩

def normalOrbitFibreEquiv :
    originalBlockFibre (normalOrbitBlockMap N) (normalOrbitBase N) ≃
      MulAction.orbit N (0 : Fin 6) where
  toFun x := ⟨x.1,by
    have hx := congrArg Subtype.val x.2
    change MulAction.orbit N x.1 = MulAction.orbit N (0 : Fin 6) at hx
    exact MulAction.orbit_eq_iff.mp hx⟩
  invFun x := ⟨x.1,Subtype.ext (MulAction.orbit_eq_iff.mpr x.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- No ambient subgroup enumeration is involved: the actual faithful
wreath embedding yields divisibility by 72. -/
theorem transitiveSix_odd_normal_card_dvd_seventyTwo
    (hN : N ≠ ⊥) (hodd : ¬ 2 ∣ Nat.card N) : Nat.card G ∣ 72 := by
  have hthree := transitiveSix_odd_normal_orbit_card N hN hodd
  have hprod := normal_orbit_card_mul_classes N (0 : Fin 6)
  rw [hthree,Nat.card_fin] at hprod
  have hblocks : Nat.card (normalOrbitBlocks N) = 2 := by
    rw [← Nat.card_congr (normalOrbitClassesEquivBlockOrbit N (0 : Fin 6))]
    omega
  have hfibre : Nat.card (originalBlockFibre
      (normalOrbitBlockMap N) (normalOrbitBase N)) = 3 :=
    (Nat.card_congr (normalOrbitFibreEquiv N)).trans hthree
  exact actual_threeByTwo_card_dvd (normalOrbitBlockMap N)
    (normalOrbitBlockMap_equivariant N) (normalOrbitBase N) hblocks hfibre

end SymmetricSubgroupAsymptotics
end
