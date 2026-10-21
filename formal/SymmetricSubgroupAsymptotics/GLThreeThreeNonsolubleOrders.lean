import SymmetricSubgroupAsymptotics.GLThreeThreePrimeThirteenReduction
import SymmetricSubgroupAsymptotics.GLThreeThreeSingerNormalizer
import SymmetricSubgroupAsymptotics.GLThreeThreeSmallIndex
import SymmetricSubgroupAsymptotics.SmallAffineTwentySevenOrderSolvability
import Mathlib.GroupTheory.Transfer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

/-! Actual nonsoluble GL3(F3) subgroups have order5616 or11232.
This follows from Sylow13 arithmetic, the selected normalizer bound,
Burnside transfer at the small order702, and the simple determinant
kernel's elementary coset-index obstruction. No primitive catalogue or
irreducible matrix-group classification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GLThreeThreeNonsolubleOrders
open StandardThreeDimensionalLinearGroups
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem order_receipt : ∀ m∈(11232 : ℕ).divisors,13∣m →
    ∀ n∈(m/13).divisors,n%13=1 → m≤78*n →
      m=13 ∨ m=26 ∨ m=39 ∨ m=52 ∨ m=78 ∨ m=351 ∨ m=702 ∨
      m=1404 ∨ m=1872 ∨ m=2808 ∨ m=3744 ∨ m=5616 ∨ m=11232 := by
  decide +kernel

theorem isSolvable_of_card702 {L : Type} [Group L] [Finite L]
    (hL : Nat.card L=702) : IsSolvable L := by
  let P : Sylow 2 L := Classical.choice inferInstance
  have hP : Nat.card P=2 := by rw [P.card_eq_multiplicity,hL]; decide +kernel
  letI : IsCyclic P := isCyclic_of_prime_card hP
  have hp : (Nat.card L).minFac=2 := by rw [hL]; decide +kernel
  have hnc := IsCyclic.normalizer_le_centralizer (P := P) hp (inferInstance : IsCyclic P)
  let f := MonoidHom.transferSylow P hnc
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hnc
  have hker : Nat.card f.ker=351 := by
    have hm := hcomp.card_mul
    change Nat.card f.ker*Nat.card P=Nat.card L at hm
    rw [hP,hL] at hm
    omega
  letI : IsSolvable f.ker := burnsideTwoPrimeSolvability.solvable f.ker 3 13 3 1
    Nat.prime_three (by decide) (by simpa only [pow_one] using hker)
  letI : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact solvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

private theorem normalizer_card_le {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (P : Subgroup L) (hP : Nat.card P=13) :
    Nat.card (Subgroup.normalizer (P : Set L))≤78 := by
  let Q := P.map f
  have hQ : Nat.card Q=13 :=
    (Nat.card_congr (P.equivMapOfInjective f hf).toEquiv).symm.trans hP
  have hle := P.le_normalizer_map f
  have he := Nat.card_congr
    ((Subgroup.normalizer (P : Set L)).equivMapOfInjective f hf).toEquiv
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  exact he.le.trans (hc.trans (GLThreeThreeSingerNormalizer.order_thirteen_normalizer_card_le Q hQ))

theorem actual_order_cases {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (h13 : 13∣Nat.card L) :
    Nat.card L=13 ∨ Nat.card L=26 ∨ Nat.card L=39 ∨ Nat.card L=52 ∨
    Nat.card L=78 ∨ Nat.card L=351 ∨ Nat.card L=702 ∨ Nat.card L=1404 ∨
    Nat.card L=1872 ∨ Nat.card L=2808 ∨ Nat.card L=3744 ∨
    Nat.card L=5616 ∨ Nat.card L=11232 := by
  have hd := GLThreeThreePrimeThirteenReduction.actual_order_dvd f hf
  have hv : (Nat.card L).factorization 13=1 := by
    have hhi := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (by decide : (11232 : ℕ)≠0)).mpr hd 13
    have hlo := (show Nat.Prime 13 by decide).factorization_pos_of_dvd
      (Nat.card_pos (α := L)).ne' h13
    have hconst : (11232 : ℕ).factorization 13=1 := by decide +kernel
    rw [hconst] at hhi
    omega
  let P : Sylow 13 L := Classical.choice inferInstance
  have hP : Nat.card P=13 := by rw [P.card_eq_multiplicity,hv]; rfl
  have hi : P.index=Nat.card L/13 := by
    have hm := (P : Subgroup L).card_mul_index
    rw [hP] at hm
    omega
  have hn := P.card_dvd_index
  rw [hi] at hn
  have hm0 : Nat.card L/13≠0 := by
    have hle := Nat.le_of_dvd (Nat.card_pos (α := L)) h13
    omega
  have hm := (Subgroup.normalizer (P : Set L)).card_mul_index
  rw [←P.card_eq_index_normalizer] at hm
  have hN := normalizer_card_le f hf (P : Subgroup L) hP
  have hbudget : Nat.card L≤78*Nat.card (Sylow 13 L) := by
    rw [←hm]
    exact Nat.mul_le_mul_right _ hN
  have hmod := card_sylow_modEq_one 13 L
  change Nat.card (Sylow 13 L)%13=1%13 at hmod
  exact order_receipt (Nat.card L) (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h13
    (Nat.card (Sylow 13 L)) (Nat.mem_divisors.mpr ⟨hn,hm0⟩) hmod hbudget

theorem nonsoluble_order {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (hL : ¬IsSolvable L) : Nat.card L=5616 ∨ Nat.card L=11232 := by
  have h13 := GLThreeThreePrimeThirteenReduction.thirteen_dvd_of_nonsoluble f hf hL
  rcases actual_order_cases f hf h13 with h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact (hL (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inl h)))).elim
  · exact (hL (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  · exact (hL (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
  · exact (hL (burnsideTwoPrimeSolvability.solvable L 2 13 2 1
      Nat.prime_two (by decide) (by simpa only [pow_one] using h))).elim
  · exact (hL (isSolvable_of_card_seventyEight h)).elim
  · exact (hL (burnsideTwoPrimeSolvability.solvable L 3 13 3 1
      Nat.prime_three (by decide) (by simpa only [pow_one] using h))).elim
  · exact (hL (isSolvable_of_card702 h)).elim
  · have he := MonoidHom.ofInjective hf
    have hc : Nat.card f.range=1404 := (Nat.card_congr he.toEquiv).symm.trans h
    exact ((GLThreeThreeSmallIndex.card_ne_small_index_orders f.range).1 hc).elim
  · have he := MonoidHom.ofInjective hf
    have hc : Nat.card f.range=1872 := (Nat.card_congr he.toEquiv).symm.trans h
    exact ((GLThreeThreeSmallIndex.card_ne_small_index_orders f.range).2.1 hc).elim
  · have he := MonoidHom.ofInjective hf
    have hc : Nat.card f.range=2808 := (Nat.card_congr he.toEquiv).symm.trans h
    exact ((GLThreeThreeSmallIndex.card_ne_small_index_orders f.range).2.2.1 hc).elim
  · have he := MonoidHom.ofInjective hf
    have hc : Nat.card f.range=3744 := (Nat.card_congr he.toEquiv).symm.trans h
    exact ((GLThreeThreeSmallIndex.card_ne_small_index_orders f.range).2.2.2 hc).elim
  · exact Or.inl h
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.GLThreeThreeNonsolubleOrders
