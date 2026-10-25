import SymmetricSubgroupAsymptotics.CFSGTwoGenerationBasic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.FinCases

/-! If one generator's actual cyclic conjugate orbit is commutative,
its orbit closure is a normal abelian subgroup and the original quotient
is cyclic. Thus the actual two-generator source is solvable. The orbit
is literal, with all correlations retained; no order or catalogue input
is required. Concrete relators must prove the commutation hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.CyclicConjugateOrbitSolvable

variable {G : Type} [Group G]

def orbit (x y : G) (n : ℤ) : G := (MulAut.conj (y^n)) x

def orbitClosure (x y : G) : Subgroup G := Subgroup.closure (Set.range (orbit x y))

theorem conjugate_orbit (x y : G) (a n : ℤ) :
    (MulAut.conj (y^a)) (orbit x y n) = orbit x y (a+n) := by
  simp only [orbit,MulAut.conj_apply,zpow_add,mul_inv_rev,mul_assoc]

private theorem orbitClosure_map_le (x y : G) (a : ℤ) :
    (orbitClosure x y).map (MulAut.conj (y^a)).toMonoidHom ≤ orbitClosure x y := by
  rw [orbitClosure,MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
  exact Subgroup.subset_closure ⟨a+n,(conjugate_orbit x y a n).symm⟩

private theorem mem_orbitClosure (x y : G) : x ∈ orbitClosure x y :=
  Subgroup.subset_closure ⟨0,by simp only [orbit,zpow_zero,MulAut.conj_apply,one_mul,inv_one,mul_one]⟩

theorem orbitClosure_normal (g : Fin 2 → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) : (orbitClosure (g 0) (g 1)).Normal := by
  let H := orbitClosure (g 0) (g 1)
  have hy : g 1 ∈ Subgroup.normalizer (H : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      have hm := orbitClosure_map_le (g 0) (g 1) 1 ⟨z,hz,rfl⟩
      simpa only [zpow_one,MulAut.conj_apply] using hm
    · intro hz
      have hm := orbitClosure_map_le (g 0) (g 1) (-1) ⟨g 1*z*(g 1)⁻¹,hz,rfl⟩
      rw [zpow_neg_one] at hm
      change (g 1)⁻¹*(g 1*z*(g 1)⁻¹)*((g 1)⁻¹)⁻¹ ∈ H at hm
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hm
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact H.le_normalizer (mem_orbitClosure (g 0) (g 1))
  · exact hy

theorem isSolvable_of_commuting_orbit (g : Fin 2 → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hcomm : ∀ a b : ℤ, Commute (orbit (g 0) (g 1) a) (orbit (g 0) (g 1) b)) :
    IsSolvable G := by
  let H := orbitClosure (g 0) (g 1)
  letI : H.Normal := orbitClosure_normal g hgen
  letI : IsMulCommutative H := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact (hcomm a b).eq)
  let pi : G →* (G ⧸ H) := QuotientGroup.mk' H
  have hx : pi (g 0) = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_orbitClosure (g 0) (g 1))
  have hqgen : Subgroup.closure (Set.range (pi ∘ g)) = ⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective H)
  have hle : (⊤ : Subgroup (G ⧸ H)) ≤ Subgroup.zpowers (pi (g 1)) := by
    rw [←hqgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change pi (g 0) ∈ Subgroup.zpowers (pi (g 1))
      rw [hx]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  letI : IsCyclic (G ⧸ H) := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨pi (g 1),le_antisymm le_top hle⟩
  apply solvable_of_ker_le_range H.subtype pi
  rw [QuotientGroup.ker_mk',Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics.CyclicConjugateOrbitSolvable
