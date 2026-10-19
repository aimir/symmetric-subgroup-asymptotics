import SymmetricSubgroupAsymptotics.PrimitiveEightCanonicalMatch
import Mathlib.GroupTheory.OrderOfElement

/-! Seven divides each primitive eight-point component order exactly once.
The lower bound uses one literal seven-cycle in each pinned canonical
model; the upper bound is the subgroup divisibility into 8 factorial. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise Classical
namespace SymmetricSubgroupAsymptotics
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
local instance primitiveEightSylowSevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_dvd_of_generator {n : ℕ}
    (g : Fin n → Equiv.Perm (Fin 8)) (i : Fin n)
    (hp : g i ^ 7 = 1) (hne : g i ≠ 1) :
    7 ∣ Nat.card (Subgroup.closure (Set.range g)) := by
  let x : Subgroup.closure (Set.range g) :=
    ⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hx : orderOf x = 7 := orderOf_eq_prime
    (Subtype.ext hp) (fun h => hne (congrArg Subtype.val h))
  rw [← hx]
  exact orderOf_dvd_natCard x

private theorem canonical_seven_dvd (j : Fin 24) (hj : 17 ≤ j.val) :
    7 ∣ Nat.card (DegreeEightCanonicalCatalogue.canonical j) := by
  fin_cases j
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop18CatalogueBinding.catalogueGenerators))
    exact seven_dvd_of_generator _ (3 : Fin 4)
      (by decide +kernel) (by decide +kernel)
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop19CatalogueBinding.catalogueGenerators))
    exact seven_dvd_of_generator _ (3 : Fin 5)
      (by decide +kernel) (by decide +kernel)
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop20CatalogueBinding.catalogueGenerators))
    exact seven_dvd_of_generator _ (3 : Fin 6)
      (by decide +kernel) (by decide +kernel)
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop21CatalogueBinding.catalogueGenerators))
    exact seven_dvd_of_generator _ (0 : Fin 3)
      (by decide +kernel) (by decide +kernel)
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop22CatalogueBinding.catalogueGenerators))
    exact seven_dvd_of_generator _ (0 : Fin 3)
      (by decide +kernel) (by decide +kernel)
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop23CatalogueBinding.catalogueGenerators))
    exact seven_dvd_of_generator _ (0 : Fin 2)
      (by decide +kernel) (by decide +kernel)
  · change 7 ∣ Nat.card (Subgroup.closure
      (Set.range PrimitiveAffineEightTop24CatalogueBinding.catalogueGenerators))
    let a := PrimitiveAffineEightTop24CatalogueBinding.catalogueGenerators
    let g : Subgroup.closure (Set.range a) :=
      ⟨a 0 * a 1, Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_range_self 0))
        (Subgroup.subset_closure (Set.mem_range_self 1))⟩
    have hp : g ^ 7 = 1 := by
      apply Subtype.ext
      change (a 0 * a 1) ^ 7 = (1 : Equiv.Perm (Fin 8))
      decide +kernel
    have hn : g ≠ 1 := by
      intro h
      have hh := congrArg Subtype.val h
      have hne : a 0 * a 1 ≠ (1 : Equiv.Perm (Fin 8)) := by decide +kernel
      exact hne hh
    have ho : orderOf g = 7 := orderOf_eq_prime hp hn
    rw [← ho]
    exact orderOf_dvd_natCard g

/-- The exact local component is retained under the published point chart. -/
theorem primitiveEight_seven_factorization
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    {X : Type} [Finite X] (C : Subgroup (Equiv.Perm X))
    [MulAction.IsPreprimitive C X] (hX : Nat.card X = 8) :
    (Nat.card C).factorization 7 = 1 := by
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch published C hX
  have hc : Nat.card C = Nat.card (DegreeEightCanonicalCatalogue.canonical M.index) := by
    calc
      _ = Nat.card (DegreeTwoPairedEightSharedTops.interface M.index).top :=
        Nat.card_congr M.groupEquiv.toEquiv
      _ = Nat.card ↥(MulAut.conj (DegreeEightCanonicalCatalogue.conjugator M.index) •
          (DegreeTwoPairedEightSharedTops.interface M.index).top : Subgroup (Equiv.Perm (Fin 8))) :=
        Nat.card_congr (Subgroup.equivSMul
          (MulAut.conj (DegreeEightCanonicalCatalogue.conjugator M.index)) _).toEquiv
      _ = _ := congrArg (fun H : Subgroup (Equiv.Perm (Fin 8)) => Nat.card H)
        (DegreeEightCanonicalCatalogue.literal_conjugated_eq M.index)
  have hseven : 7 ∣ Nat.card C := by
    rw [hc]
    exact canonical_seven_dvd M.index M.primitive_index
  have hd : Nat.card C ∣ Nat.factorial 8 := by
    have hh := C.card_subgroup_dvd_card
    simpa only [Nat.card_perm, hX] using hh
  have hu := (Nat.factorization_le_iff_dvd
    (Nat.card_pos (α := C)).ne' (Nat.factorial_ne_zero 8)).mpr hd 7
  have hl := (show Nat.Prime 7 by decide).factorization_pos_of_dvd
    (Nat.card_pos (α := C)).ne' hseven
  have hfac : (Nat.factorial 8).factorization 7 = 1 := by decide +kernel
  omega

end SymmetricSubgroupAsymptotics
