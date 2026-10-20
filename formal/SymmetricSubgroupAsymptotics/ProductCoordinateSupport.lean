import SymmetricSubgroupAsymptotics.PGroupProductAdaptedGenerators
import SymmetricSubgroupAsymptotics.CentralizerCosetCode
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Fixed coordinate supports in an actual finite direct product. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.ProductCoordinateSupport

variable {I : Type} [Fintype I] (P : I → Type) [∀ i, Group (P i)]

def box (T : Finset I) : Subgroup (∀ i, P i) where
  carrier := {a | ∀ i, i ∉ T → a i = 1}
  one_mem' := by
    change ∀ i, i ∉ T → (1 : ∀ i, P i) i = 1
    intro i _
    rfl
  mul_mem' := by intro a b ha hb i hi; simp only [Pi.mul_apply, ha i hi, hb i hi, mul_one]
  inv_mem' := by intro a ha i hi; simp only [Pi.inv_apply, ha i hi, inv_one]

instance box_normal (T : Finset I) : (box P T).Normal where
  conj_mem a ha b := by
    intro i hi
    change b i * a i * (b i)⁻¹ = 1
    rw [ha i hi, mul_one, mul_inv_cancel]

def restrictEquiv (T : Finset I) : box P T ≃ (∀ i : T, P i) where
  toFun a i := a.1 i
  invFun a := ⟨fun i => if h : i ∈ T then a ⟨i, h⟩ else 1, by
    intro i hi
    simp only [dif_neg hi]⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · simp only [dif_pos hi]
    · simp only [dif_neg hi, a.2 i hi]
  right_inv a := by
    funext i
    simp only [dif_pos i.2]

omit [Fintype I] in
theorem card_box_le [∀ i, Finite (P i)] (T : Finset I) (M : ℕ)
    (hM : ∀ i, Nat.card (P i) ≤ M) : Nat.card (box P T) ≤ M ^ T.card := by
  rw [Nat.card_congr (restrictEquiv P T), Nat.card_pi]
  calc
    (∏ i : T, Nat.card (P i)) ≤ ∏ _i : T, M :=
      Finset.prod_le_prod' (fun i _ => hM i)
    _ = M ^ T.card := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

variable {G : Type} [Group G] (π : G →* ∀ i, P i)

omit [Fintype I] in
theorem exists_support_code (g : G)
    (hg : PGroupProductAdaptedGenerators.SingleSupport P π g) :
    ∃ c : Option I, ∀ i, c ≠ some i → π g i = 1 := by
  rcases hg with hg | ⟨i, a, hg⟩
  · exact ⟨none, fun j _ => congrFun hg j⟩
  · refine ⟨some i, ?_⟩
    intro j hj
    rw [hg, Pi.mulSingle_eq_of_ne (by intro h; subst j; exact hj rfl)]

/-- A q-tuple supported on at most one coordinate per entry has one
common normal support box of at most q coordinates. -/
theorem exists_tuple_support {J : Type} [Fintype J] (x : J → G)
    (hx : ∀ j, PGroupProductAdaptedGenerators.SingleSupport P π (x j)) :
    ∃ T : Finset I, T.card ≤ Fintype.card J ∧
      ∀ j, π (x j) ∈ box P T := by
  choose c hc using fun j => exists_support_code P π (x j) (hx j)
  let T := Finset.univ.biUnion (fun j => (c j).toFinset)
  refine ⟨T, ?_, ?_⟩
  · calc
      T.card ≤ ∑ j : J, (c j).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _j : J, 1 := Finset.sum_le_sum (fun j _ => by cases c j <;> simp)
      _ = Fintype.card J := by simp
  · intro j i hi
    apply hc j i
    intro hji
    apply hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [hji]⟩

/-- Every tuple from the original generated subgroup shares its literal
normal top support; normal commutators add no new product coordinate. -/
theorem normalCommutator_top_le {J K : Type} (v : J → G) (x : K → G)
    (T : Finset I) (hv : ∀ j, π (v j) ∈ box P T)
    (hx : ∀ k, x k ∈ Subgroup.closure (Set.range v)) :
    (generatorNormalCommutator x).map π ≤ box P T := by
  have hcl : Subgroup.closure (Set.range v) ≤ (box P T).comap π := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact hv j
  have hn : Subgroup.normalClosure (Set.range x) ≤ (box P T).comap π := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨k, rfl⟩
    exact hcl (hx k)
  apply Subgroup.map_le_iff_le_comap.mpr
  exact (Subgroup.commutator_le_left _ _).trans hn

end SymmetricSubgroupAsymptotics.ProductCoordinateSupport
