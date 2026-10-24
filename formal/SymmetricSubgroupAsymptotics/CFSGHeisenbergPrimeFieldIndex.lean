import SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoActionIndex
import SymmetricSubgroupAsymptotics.CFSGSLTwoPrimeIndexLower

/-! Over the prime field the same coupled stabilizer has index at least
p cubed. Zero vector intersection forces its actual central intersection
to be trivial; otherwise both actual index factors retain their p gain. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergPrimeFieldIndex
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSLTwoStabilizers CFSGTypeASLTwoWeyl
open CFSGHeisenbergFiniteFieldIsotropy CFSGHeisenbergSLTwoActionIndex
variable {K : Type*} [Field K] [Finite K]

theorem zero_vector_eq_central (g : Element K 1) (hg : coordinateVector g = 0) :
    g = central (Multiplicative.ofAdd g.c) := by
  apply Element.ext
  · funext i
    fin_cases i
    exact congrFun hg 0
  · funext i
    fin_cases i
    exact congrFun hg 1
  · rfl

theorem prime_cube_le_index (p : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = p)
    (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g) = (A⁻¹).transpose.toLin' (coordinateVector g))
    (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K)))
    (hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl) :
    p^3 ≤ M.index := by
  let J := M.comap SemidirectProduct.inl
  let L := M.map SemidirectProduct.rightHom
  have hfactor : M.index = J.index * L.index := subgroup_index_factor φ M
  by_cases hzero : ∀ g ∈ J, coordinateVector g = 0
  · have hC : Nat.card (centralPreimage J) ≤ 1 := by
      have h := proper_additive_card_mul_prime_le p (centralPreimage J)
        (centralPreimage_ne_top J hcentre)
      rw [hK] at h
      have hp := (Fact.out : p.Prime).two_le
      nlinarith
    let f : J → centralPreimage J := fun g => ⟨g.val.c, by
      change central (Multiplicative.ofAdd g.val.c) ∈ J
      rw [← zero_vector_eq_central g.val (hzero g.val g.property)]
      exact g.property⟩
    have hf : Function.Injective f := by
      intro g h he
      apply Subtype.ext
      exact (zero_vector_eq_central g.val (hzero g.val g.property)).trans
        ((congrArg (fun c : K => central (m := 1) (Multiplicative.ofAdd c))
          (congrArg Subtype.val he)).trans
          (zero_vector_eq_central h.val (hzero h.val h.property)).symm)
    have hcard : Nat.card J = 1 := by
      have hh := (Nat.card_le_card_of_injective f hf).trans hC
      have hpos := Nat.card_pos (α := J)
      omega
    have hi : J.index = p^3 := by
      have h := J.card_mul_index
      rw [hcard, one_mul, CFSGHeisenbergCoordinateGroup.card, hK] at h
      exact h
    rw [hfactor, hi]
    exact Nat.le_mul_of_pos_right _ (Nat.card_pos (α := SL2 (F := K) ⧸ L))
  · obtain ⟨g, hg, hne⟩ : ∃ g, g ∈ J ∧ coordinateVector g ≠ 0 := by
      simpa only [not_forall, exists_prop] using hzero
    have hLproper : L ≠ ⊤ := projected_ne_top_of_nonzero_vector φ hφ M hcentre g hg hne
    have hL : p ≤ L.index := CFSGSLTwoPrimeIndexLower.prime_le_proper_index p L hLproper
    have hJ : p^2 ≤ J.index := by
      have h := CFSGHeisenbergFiniteFieldIndex.index_least p J hcentre
      simpa only [hK, pow_one, ← pow_two] using h
    rw [hfactor]
    exact (Nat.mul_le_mul hJ hL).trans_eq (by ring)

theorem degree_le_of_central_motion (p : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = p)
    (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g) = (A⁻¹).transpose.toLin' (coordinateVector g))
    {X : Type*} [Finite X] [MulAction (Element K 1 ⋊[φ] SL2 (F := K)) X]
    (x : X) (c : Multiplicative K)
    (hc : (SemidirectProduct.inl (central c) : Element K 1 ⋊[φ] SL2 (F := K)) • x ≠ x) :
    p^3 ≤ Nat.card X := by
  let M := MulAction.stabilizer (Element K 1 ⋊[φ] SL2 (F := K)) x
  have hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl := by
    intro hh
    exact hc (hh ⟨c, rfl⟩)
  exact (prime_cube_le_index p hK φ hφ M hcentre).trans
    ((MulAction.index_stabilizer _ _).trans_le (Set.ncard_le_card _))

end SymmetricSubgroupAsymptotics.CFSGHeisenbergPrimeFieldIndex
