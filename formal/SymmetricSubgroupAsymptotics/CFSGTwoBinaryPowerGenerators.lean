import SymmetricSubgroupAsymptotics.CFSGSylowTwoNormalizerSolvable
import SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators

/-! A reusable certificate interface for whole-element binary powers.
The raw matrix powers below are genuine required certificate inputs;
selected vector or row periods do not discharge them. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem zpowers_isPGroup_two_of_pow {G : Type*} [Group G]
    (g : G) (k : ℕ) (hpow : g ^ (2 ^ k) = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have hd : Nat.card (Subgroup.zpowers g) ∣ 2 ^ k := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card hj

theorem goodSylowTwo_of_two_power_generators {G : Type} [Group G] [Finite G]
    (hCFSG : CFSG.CFSGClassification) (x y : G) (k l : ℕ)
    (hx : x ^ (2 ^ k) = 1) (hy : y ^ (2 ^ l) = 1)
    (hgen : Subgroup.closure ({x, y} : Set G) = ⊤) : GoodSylowPrime G 2 := by
  apply goodSylowTwo_of_two_binary_subgroups hCFSG
    (Subgroup.zpowers x) (Subgroup.zpowers y)
    (zpowers_isPGroup_two_of_pow x k hx) (zpowers_isPGroup_two_of_pow y l hy)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with hzx | hz
  · subst z
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  · have hz : z = y := Set.mem_singleton_iff.mp hz
    subst z
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

/-- This single interface applies to all eight literal matrix models.
Its two power equations must be supplied by whole-matrix certificates. -/
theorem matrix_model_goodSylowTwo_of_binary_powers
    (hCFSG : CFSG.CFSGClassification) (p n : ℕ) (a b : Array String)
    [Finite (CFSG.Models.MatrixData.Model p n a b)]
    (hn : ¬IsMulCommutative (CFSG.Models.MatrixData.Model p n a b))
    (k l : ℕ)
    (ha : CFSG.Models.MatrixData.matrix p n a ^ (2 ^ k) = 1)
    (hb : CFSG.Models.MatrixData.matrix p n b ^ (2 ^ l) = 1) :
    GoodSylowPrime (CFSG.Models.MatrixData.Model p n a b) 2 := by
  obtain ⟨x, hx, y, hy, hxa, hyb, hgen⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let C := Subgroup.closure (CFSG.Models.MatrixData.generators p n a b)
  let xm : C := ⟨x, Subgroup.subset_closure hx⟩
  let ym : C := ⟨y, Subgroup.subset_closure hy⟩
  have hxpow : xm ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (x : Matrix (Fin n) (Fin n) (ZMod p)) ^ (2 ^ k) = 1
    rw [hxa]
    exact ha
  have hypow : ym ^ (2 ^ l) = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (y : Matrix (Fin n) (Fin n) (ZMod p)) ^ (2 ^ l) = 1
    rw [hyb]
    exact hb
  apply goodSylowTwo_of_two_power_generators hCFSG xm ym k l hxpow hypow
  let H : Subgroup C := Subgroup.closure ({xm, ym} : Set C)
  have hCH : C ≤ H.map C.subtype := by
    change Subgroup.closure (CFSG.Models.MatrixData.generators p n a b) ≤ H.map C.subtype
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨xm, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
    · have hz : z = y := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨ym, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  apply top_unique
  intro z _
  obtain ⟨w, hw, he⟩ := hCH z.property
  have he' : w = z := Subtype.ext he
  exact he' ▸ hw

end SymmetricSubgroupAsymptotics.CFSGReduction
