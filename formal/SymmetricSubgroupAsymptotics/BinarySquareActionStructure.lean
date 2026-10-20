import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Exponent

/-! Original-action square tests used by the two-half natural-module
induction. The terminal elementary kernel is kept as an actual index-two
subgroup. No wreath classification or replacement action is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySquareActionStructure

variable {G X : Type} [Group G] [MulAction G X]

/-- The original permutation image has exponent dividing two. In a
faithful action this is exactly the elementary binary exponent condition. -/
def SquaresActTrivially : Prop := ∀ (g : G) (x : X), g ^ 2 • x = x

theorem squaresActTrivially_iff_pow_two [FaithfulSMul G X] :
    SquaresActTrivially (G := G) (X := X) ↔ ∀ g : G, g ^ 2 = 1 := by
  constructor
  · intro h g
    apply eq_of_smul_eq_smul (α := X)
    intro x
    exact (h g x).trans (one_smul G x).symm
  · intro h g x
    rw [h g, one_smul]

/-- Nontriviality of a square in a normal subgroup's original action
propagates to every one of its original transitive orbit actions. -/
theorem normal_orbit_exists_square_move [MulAction.IsPretransitive G X]
    (K : Subgroup G) [K.Normal]
    (hmove : ∃ (k : K) (x : X), k ^ 2 • x ≠ x)
    (o : MulAction.orbitRel.Quotient K X) :
    ∃ (k : K) (x : o.orbit), k ^ 2 • x ≠ x := by
  obtain ⟨k, x, hx⟩ := hmove
  let y : o.orbit := ⟨o.nonempty_orbit.choose, o.nonempty_orbit.choose_spec⟩
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G x (y : X)
  let k' : K := ⟨a * (k : G) * a⁻¹, (inferInstance : K.Normal).conj_mem _ k.property a⟩
  refine ⟨k', y, ?_⟩
  intro he
  have he' : (a * (k : G) * a⁻¹) ^ 2 • (y : X) = (y : X) :=
    congrArg Subtype.val he
  have ht : (a * (k : G) * a⁻¹) ^ 2 • (y : X) = a • ((k : G) ^ 2 • x) := by
    rw [conj_pow, ← ha, mul_smul, mul_smul, inv_smul_smul]
  apply hx
  apply MulAction.injective a
  exact ht.symm.trans (he'.trans ha.symm)

/-- An actual exponent-two permutation image is commutative. This lemma
also covers nonfaithful actions of the original subgroup. -/
theorem commute_images_of_squares_trivial
    (K : Subgroup G) (hK : SquaresActTrivially (G := K) (X := X)) (a b : K) :
    Commute (MulAction.toPermHom G X (a : G))
      (MulAction.toPermHom G X (b : G)) := by
  let f : K →* Equiv.Perm X := (MulAction.toPermHom G X).comp K.subtype
  have hs : ∀ z : f.range, z ^ 2 = 1 := by
    intro z
    obtain ⟨k, hk⟩ := z.property
    apply Subtype.ext
    change (z : Equiv.Perm X) ^ 2 = 1
    rw [← hk, ← map_pow]
    apply Equiv.ext
    exact hK k
  have hd : ∀ z : f.range, orderOf z ∣ 2 := fun z =>
    orderOf_dvd_iff_pow_eq_one.mpr (hs z)
  have he := (Commute.of_orderOf_dvd_two hd (f.rangeRestrict a) (f.rangeRestrict b)).eq
  exact congrArg Subtype.val he

/-- If an index-two original kernel has elementary permutation image,
a nontrivial original square is fixed-point-free. Its fourth power acts
trivially. This is the elementary-wreath terminal argument intrinsically. -/
theorem semiregular_four_of_index_two_elementary_kernel
    [MulAction.IsPretransitive G X]
    (K : Subgroup G) (hi : K.index = 2)
    (hK : SquaresActTrivially (G := K) (X := X))
    (g : G) (y : X) (hy : g ^ 2 • y ≠ y) :
    (∀ x : X, g ^ 4 • x = x) ∧ (∀ x : X, g ^ 2 • x ≠ x) := by
  let z : K := ⟨g ^ 2, K.sq_mem_of_index_two hi g⟩
  have hg : g ∉ K := by
    intro hg
    exact hy (hK ⟨g, hg⟩ y)
  have hzK (k : K) : Commute (MulAction.toPermHom G X (g ^ 2))
      (MulAction.toPermHom G X (k : G)) :=
    commute_images_of_squares_trivial K hK z k
  have hzg : Commute (MulAction.toPermHom G X (g ^ 2))
      (MulAction.toPermHom G X g) := by
    rw [map_pow]
    exact (Commute.refl _).pow_left 2
  have hz (h : G) : Commute (MulAction.toPermHom G X (g ^ 2))
      (MulAction.toPermHom G X h) := by
    by_cases hh : h ∈ K
    · exact hzK ⟨h, hh⟩
    · have hk : h * g⁻¹ ∈ K :=
        (K.mul_mem_iff_of_index_two hi).mpr (by simp only [hh, K.inv_mem_iff, hg])
      let k : K := ⟨h * g⁻¹, hk⟩
      have he : h = (k : G) * g := by simp only [k, inv_mul_cancel_right]
      rw [he, map_mul]
      exact (hzK k).mul_right hzg
  constructor
  · intro x
    have he := hK z x
    change (g ^ 2) ^ 2 • x = x at he
    simpa only [← pow_mul] using he
  · intro x hx
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G x y
    have he := Equiv.congr_fun (hz h).eq x
    change g ^ 2 • (h • x) = h • (g ^ 2 • x) at he
    rw [hx, hh] at he
    exact hy he

end SymmetricSubgroupAsymptotics.BinarySquareActionStructure
