import SymmetricSubgroupAsymptotics.MarkedC4HallSpliceCount

/-! The actual zero-physical base for the graph-first enlarged induction.
Its one global Hall polynomial is retained explicitly. This is not the
original zero-degree moment (which is1); it counts vertical mark subgroups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.VerticalHallBase

private theorem card_unit_hom (B : Type) [Group B] : Nat.card (Unit →* B)=1 := by
  letI : Unique (Unit →* B) := {
    default := 1
    uniq := fun f => by
      apply MonoidHom.ext
      intro x
      have hx : x=(1 : Unit) := Subsingleton.elim _ _
      rw [hx,f.map_one]
      rfl }
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

/-- A SINGLE polynomial pays the complete vertical Hall base. It is not
multiplied again at each physical peel. -/
def polynomial (r : ℕ) : ℝ := 16*((r : ℝ)+1)^2

theorem polynomial_one_le (r : ℕ) : 1≤polynomial r := by
  unfold polynomial
  have hr : (0 : ℝ)≤r := Nat.cast_nonneg r
  nlinarith [sq_nonneg (r : ℝ)]

/-- Actual subgroup count, including all vertical mark configurations. -/
theorem card_subgroups_le (r : ℕ) :
    (Nat.card (Subgroup (Multiplicative (Fin r → ZMod 4))) : ℝ) ≤
      polynomial r*(2 : ℝ)^markedF 0 r := by
  letI : Fintype (Subgroup (Multiplicative (Fin r → ZMod 4))) := Fintype.ofFinite _
  have h := sum_card_hom_quotient_le 2 (Multiplicative (Fin r → ZMod 4))
    (hasExp2_cyclicFourCoordinates r 2 (by omega)) Unit
  have hsum : (∑ K : Subgroup (Multiplicative (Fin r → ZMod 4)),Nat.card (Unit →* (Multiplicative (Fin r → ZMod 4)) ⧸ K))=Nat.card (Subgroup (Multiplicative (Fin r → ZMod 4))) := by
    simp only [card_unit_hom,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,
      Nat.card_eq_fintype_card]
  rw [hsum] at h
  have hz (k : ℕ) : col (Abelianization Unit) k=0 :=
    col_eq_zero_of_subsingleton _ k
  have hpsi : psi (r : ℝ) 0=(r : ℝ)^2/4 := by
    unfold psi
    split_ifs with hr
    · have hr' : (r : ℝ)=0 := le_antisymm hr (Nat.cast_nonneg r)
      rw [hr']
      norm_num
    · ring
  simp only [Finset.prod_range_succ,Finset.prod_range_zero,one_mul,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    col_cyclicFourCoordinates,Nat.reduceLT,if_true,hz,Nat.cast_zero,hpsi] at h
  have he : (r : ℝ)^2/4+(r : ℝ)^2/4=markedF 0 r := by
    unfold markedF
    ring
  rw [he] at h
  have hp : (((r : ℝ)+1)*((r : ℝ)+1))*4^2=polynomial r := by
    unfold polynomial
    ring
  rw [hp] at h
  exact h

end SymmetricSubgroupAsymptotics.MarkedC4.VerticalHallBase
