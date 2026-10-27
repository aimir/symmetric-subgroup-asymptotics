import SymmetricSubgroupAsymptotics.SimpleProductAxisStabilizerRestriction
import Mathlib.Tactic.Group

/-! The projection normalizes the literal axis intersection, even when the
stabilizer couples coordinates. The factor3 belongs to the intersection index. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CoupledSimpleProductIntersectionStructure
open SimpleProductAxisStabilizerRestriction
variable {J T : Type} [Group T] [Finite T] [Fintype J] [DecidableEq J]

private theorem axis_conjugation (i : J) (h : J → T) (a : T) :
    axis i (h i*a*(h i)⁻¹)=h*axis i a*h⁻¹ := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [axis,MonoidHom.mulSingle_apply]
  · simp [axis,MonoidHom.mulSingle_apply,Pi.mulSingle,hj]

theorem intersection_le_projection (H : Subgroup (J → T)) (i : J) :
    H.comap (axis i) ≤ H.map (coordinate i) := by
  intro a ha
  refine ⟨axis i a,ha,?_⟩
  simp [axis,coordinate,MonoidHom.mulSingle_apply]

theorem projection_le_intersection_normalizer (H : Subgroup (J → T)) (i : J) :
    H.map (coordinate i) ≤ Subgroup.normalizer (H.comap (axis i) : Set T) := by
  have hc (h : J → T) (hh : h ∈ H) (a : T) (ha : a ∈ H.comap (axis i)) :
      h i*a*(h i)⁻¹ ∈ H.comap (axis i) := by
    change axis i (h i*a*(h i)⁻¹) ∈ H
    rw [axis_conjugation]
    exact H.mul_mem (H.mul_mem hh ha) (H.inv_mem hh)
  rintro g ⟨h,hh,hg⟩
  change h i=g at hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    simpa only [hg] using hc h hh a ha
  · intro ha
    have hb := hc h⁻¹ (H.inv_mem hh) (g*a*g⁻¹) ha
    have heq : (h⁻¹) i*(g*a*g⁻¹)*((h⁻¹) i)⁻¹=a := by
      simp only [Pi.inv_apply,hg]
      group
    rwa [heq] at hb

/-- Exact intersection index, obtained by cancellation of its actual factor3. -/
theorem index_eq_three_mul_two_pow (d m : ℕ) (hd : d ∣ 3*2^m) (h3 : 3 ∣ d) :
    ∃ a : ℕ,d=3*2^a := by
  obtain ⟨b,hb⟩ := h3
  have hbdiv : b ∣ 2^m := (Nat.mul_dvd_mul_iff_left (by decide : 0<3)).mp
    (by simpa only [hb] using hd)
  obtain ⟨a,_,ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbdiv
  exact ⟨a,by rw [hb,ha]⟩

/-- A three-divisible actual axis intersection is itself a nontrivial proper
simple subgroup of index3*2^a; its projection lies in its actual normalizer. -/
theorem selected_intersection_structure [IsSimpleGroup T]
    (hn : ¬IsMulCommutative T) (H : Subgroup (J → T)) (i : J) (m : ℕ)
    (hdegree : H.index ∣ 3*2^m) (h3 : 3 ∣ (H.comap (axis i)).index) :
    H.comap (axis i) ≠ ⊥ ∧ H.comap (axis i) ≠ ⊤ ∧
    (∃ a : ℕ,(H.comap (axis i)).index=3*2^a) ∧
    H.comap (axis i) ≤ H.map (coordinate i) ∧
    H.map (coordinate i) ≤ Subgroup.normalizer (H.comap (axis i) : Set T) := by
  have hd := (axis_index_dvd_index H i).trans hdegree
  refine ⟨?_,?_,index_eq_three_mul_two_pow _ m hd h3,
    intersection_le_projection H i,projection_le_intersection_normalizer H i⟩
  · intro hb
    rw [hb,Subgroup.index_bot] at hd
    exact simple_order_not_dvd hn m hd
  · intro ht
    rw [ht,Subgroup.index_top] at h3
    norm_num at h3

end SymmetricSubgroupAsymptotics.CoupledSimpleProductIntersectionStructure
