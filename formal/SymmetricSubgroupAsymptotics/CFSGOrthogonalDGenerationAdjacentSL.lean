import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration

/-! The literal adjacent A-chain roots generate SL in every dimension.
This supplies the natural D chain embedding without assuming membership
for arbitrary off-diagonal root matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationAdjacentSL
open CFSGTypeAElementaryMatrices
variable {K : Type} [Field K] (r : ℕ)

theorem eq_top_of_adjacent (H : Subgroup (Matrix.SpecialLinearGroup (Fin r) K))
    (hadj : ∀ (i j : Fin r) (hij : i ≠ j),
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) → ∀ a : K, elementary hij a ∈ H) : H = ⊤ := by
  have hcomm (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (a b : K) (ha : elementary hij a ∈ H) (hb : elementary hjk b ∈ H) :
      elementary hik (a * b) ∈ H := by
    rw [← elementary_commutator hij hjk hik]
    change elementary hij a * elementary hjk b * (elementary hij a)⁻¹ *
      (elementary hjk b)⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have upper : ∀ m : ℕ, ∀ hm : m < r, ∀ i : Fin r, i.val < m →
      ∀ (hij : i ≠ (⟨m, hm⟩ : Fin r)) (a : K), elementary hij a ∈ H := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm i him hij a
      by_cases had : i.val + 1 = m
      · exact hadj i ⟨m, hm⟩ hij (Or.inl had) a
      · let k : Fin r := ⟨m - 1, by omega⟩
        have hkm : k.val < m := by dsimp [k]; omega
        have hik : i.val < k.val := by dsimp [k]; omega
        have hik' : i ≠ k := fun h => (Nat.ne_of_lt hik) (congrArg Fin.val h)
        have hkj : k ≠ (⟨m, hm⟩ : Fin r) := fun h => (Nat.ne_of_lt hkm) (congrArg Fin.val h)
        have hi := ih k.val hkm k.isLt i hik hik' a
        have hj := hadj k ⟨m, hm⟩ hkj (Or.inl (by dsimp [k]; omega)) 1
        simpa only [mul_one] using hcomm i k ⟨m, hm⟩ hik' hkj hij a 1 hi hj
  have lower : ∀ m : ℕ, ∀ hm : m < r, ∀ j : Fin r, j.val < m →
      ∀ (hij : (⟨m, hm⟩ : Fin r) ≠ j) (a : K), elementary hij a ∈ H := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm j hjm hij a
      by_cases had : j.val + 1 = m
      · exact hadj ⟨m, hm⟩ j hij (Or.inr had) a
      · let k : Fin r := ⟨m - 1, by omega⟩
        have hkm : k.val < m := by dsimp [k]; omega
        have hjk : j.val < k.val := by dsimp [k]; omega
        have hik : (⟨m, hm⟩ : Fin r) ≠ k := fun h => (Nat.ne_of_gt hkm) (congrArg Fin.val h)
        have hkj : k ≠ j := fun h => (Nat.ne_of_gt hjk) (congrArg Fin.val h)
        have hi := hadj ⟨m, hm⟩ k hik (Or.inr (by dsimp [k]; omega)) a
        have hj := ih k.val hkm k.isLt j hjk hkj 1
        simpa only [mul_one] using hcomm ⟨m, hm⟩ k j hik hkj hij a 1 hi hj
  apply CFSGTypeAElementaryGeneration.eq_top_of_elementary
  intro i j hij a
  by_cases hlt : i.val < j.val
  · exact upper j.val j.isLt i hlt hij a
  · have hgt : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    exact lower i.val i.isLt j hgt hij a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationAdjacentSL
