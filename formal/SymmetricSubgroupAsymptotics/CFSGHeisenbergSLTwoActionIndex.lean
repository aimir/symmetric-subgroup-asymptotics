import SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoStabilizers
import SymmetricSubgroupAsymptotics.CFSGSLTwoProperIndexLower
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergIndex

/-! A centre-moving action of an actual Heisenberg semidirect SL2 has
degree at least the square of the coefficient field. The same original
stabilizer supplies both its Heisenberg intersection and its SL2 image;
their indices multiply by the checked kernel/index factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoActionIndex

open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSLTwoStabilizers CFSGTypeASLTwoWeyl
variable {K : Type*} [Field K]

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

private theorem card_le_of_zero_vectors [Finite K] (J : Subgroup (Element K 1))
    (hzero : ∀ g ∈ J, coordinateVector g = 0) : Nat.card J ≤ Nat.card K := by
  apply Nat.card_le_card_of_injective (fun g : J => g.val.c)
  intro g h hc
  have hg := hzero g.val g.property
  have hh := hzero h.val h.property
  have hga : g.val.a = 0 := by
    funext i
    fin_cases i
    exact congrFun hg 0
  have hgb : g.val.b = 0 := by
    funext i
    fin_cases i
    exact congrFun hg 1
  have hha : h.val.a = 0 := by
    funext i
    fin_cases i
    exact congrFun hh 0
  have hhb : h.val.b = 0 := by
    funext i
    fin_cases i
    exact congrFun hh 1
  exact Subtype.ext (Element.ext (hga.trans hha.symm) (hgb.trans hhb.symm) hc)

theorem subgroup_index_factor [Finite K] (φ : SL2 (F := K) →* MulAut (Element K 1))
    (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K))) :
    M.index = (M.comap SemidirectProduct.inl).index *
      (M.map SemidirectProduct.rightHom).index := by
  have hh := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    (SemidirectProduct.rightHom : Element K 1 ⋊[φ] SL2 (F := K) →* SL2 (F := K))
    SemidirectProduct.rightHom_surjective M
  have hJ : (M.comap SemidirectProduct.inl).index =
      M.relIndex (SemidirectProduct.rightHom : Element K 1 ⋊[φ] SL2 (F := K) →* SL2 (F := K)).ker := by
    rw [Subgroup.index_comap, SemidirectProduct.range_inl_eq_ker_rightHom]
  rw [← hJ] at hh
  exact hh

theorem field_square_le_index (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g) = (A⁻¹).transpose.toLin' (coordinateVector g))
    (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K)))
    (hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl) :
    Nat.card K ^ 2 ≤ M.index := by
  let J := M.comap SemidirectProduct.inl
  let L := M.map SemidirectProduct.rightHom
  have hfactor : M.index = J.index * L.index := subgroup_index_factor φ M
  by_cases hzero : ∀ g ∈ J, coordinateVector g = 0
  · have hcard : Nat.card J ≤ Nat.card K := card_le_of_zero_vectors J hzero
    have hJ : Nat.card K ^ 2 ≤ J.index := by
      apply Nat.le_of_mul_le_mul_left _ (Nat.card_pos (α := K))
      calc
        Nat.card K * Nat.card K ^ 2 = Nat.card K ^ 3 := by ring
        _ = Nat.card J * J.index := by
          have he := J.card_mul_index
          rw [CFSGHeisenbergCoordinateGroup.card] at he
          exact he.symm
        _ ≤ Nat.card K * J.index := Nat.mul_le_mul_right _ hcard
    rw [hfactor]
    exact hJ.trans (Nat.le_mul_of_pos_right _ (Nat.card_pos (α := SL2 (F := K) ⧸ L)))
  · have hex : ∃ g, g ∈ J ∧ coordinateVector g ≠ 0 := by
      simpa only [not_forall, exists_prop] using hzero
    obtain ⟨g, hg, hne⟩ := hex
    have hLproper : L ≠ ⊤ := projected_ne_top_of_nonzero_vector φ hφ M hcentre g hg hne
    have hL : Nat.card K ≤ 2 * L.index :=
      CFSGSLTwoProperIndexLower.field_card_le_twice_proper_index L hLproper
    have hJ : p * Nat.card K ≤ J.index := by
      simpa only [pow_one] using CFSGHeisenbergFiniteFieldIndex.index_least p J hcentre
    have hm := Nat.mul_le_mul hJ hL
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hlow : 2 * Nat.card K ^ 2 ≤ 2 * M.index := by
      calc
        2 * Nat.card K ^ 2 ≤ p * Nat.card K ^ 2 := Nat.mul_le_mul_right _ hp
        _ = (p * Nat.card K) * Nat.card K := by ring
        _ ≤ J.index * (2 * L.index) := hm
        _ = 2 * M.index := by rw [hfactor]; ring
    exact Nat.le_of_mul_le_mul_left hlow (by decide : 0 < 2)

theorem degree_le_of_central_motion (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g) = (A⁻¹).transpose.toLin' (coordinateVector g))
    {X : Type*} [Finite X] [MulAction (Element K 1 ⋊[φ] SL2 (F := K)) X]
    (x : X) (c : Multiplicative K)
    (hc : (SemidirectProduct.inl (central c) : Element K 1 ⋊[φ] SL2 (F := K)) • x ≠ x) :
    Nat.card K ^ 2 ≤ Nat.card X := by
  let M := MulAction.stabilizer (Element K 1 ⋊[φ] SL2 (F := K)) x
  have hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl := by
    intro hh
    exact hc (hh ⟨c, rfl⟩)
  calc
    Nat.card K ^ 2 ≤ M.index := field_square_le_index p φ hφ M hcentre
    _ = (MulAction.orbit (Element K 1 ⋊[φ] SL2 (F := K)) x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

end SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoActionIndex
