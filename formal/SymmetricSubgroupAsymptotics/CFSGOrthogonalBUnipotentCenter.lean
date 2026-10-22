import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentCenterSupport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBHighestRootCoordinates
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.FieldSimp

/-! The actual odd-B unipotent centre is its original highest long-root
group in rank at least three. Necessity is a literal matrix calculation;
sufficiency uses the nontrivial centre of the SAME finite p-group and
its actual normalizer's transitive scalar action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

theorem central_unipotent_is_highestRoot (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : unipotent K (s + 3)) (hz : z ∈ Subgroup.center (unipotent K (s + 3))) :
    ∃ a : K, z.val = highestRoot s a := by
  obtain ⟨a, ha⟩ := central_unipotent_highest_root_support h2 (s + 1) z hz
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact ha.trans (highestRoot_eq_upperShear h2 s a).symm

theorem highestRoot_central [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (b : K) :
    (⟨highestRoot s b, highestRoot_mem_unipotent h2 s b⟩ : unipotent K (s + 3)) ∈
      Subgroup.center (unipotent K (s + 3)) := by
  let U := unipotent K (s + 3)
  letI : Nontrivial U := by
    apply nontrivial_of_ne
      (⟨highestRoot s 1, highestRoot_mem_unipotent h2 s 1⟩ : U) 1
    intro h
    have he : highestRoot (K := K) s 1 = highestRoot s 0 :=
      (congrArg Subtype.val h).trans (highestRoot_zero h2 s).symm
    exact one_ne_zero (highestRoot_injective h2 s he)
  letI : Nontrivial (Subgroup.center U) :=
    (unipotent_isPGroup K (s + 3) p).center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center U)
  obtain ⟨a, ha⟩ := central_unipotent_is_highestRoot h2 s z.val z.property
  have ha0 : a ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact ha.trans (by rw [he, highestRoot_zero h2 s]; rfl)
  by_cases hb : b = 0
  · subst b
    have he : (⟨highestRoot s 0, highestRoot_mem_unipotent h2 s 0⟩ : U) = 1 :=
      Subtype.ext (highestRoot_zero h2 s)
    rw [he]
    exact (Subgroup.center U).one_mem
  · let g : Kˣ := Units.mk0 (b / a) (div_ne_zero hb ha0)
    let T : elementaryRootGroup K (s + 3) := centerTorus K s g
    let e : MulAut U := U.normalizerMonoidHom ⟨T, centerTorus_mem_normalizer K s g⟩
    let w : Subgroup.center U := Subgroup.centerCongr e z
    have hw : w.val.val = highestRoot s b := by
      change T * z.val.val * T⁻¹ = highestRoot s b
      rw [ha]
      change centerTorus K s g * highestRoot s a * (centerTorus K s g)⁻¹ = _
      rw [centerTorus_highestRoot_conjugation h2]
      congr 1
      change (b / a) * a = b
      exact div_mul_cancel₀ b ha0
    have hwu : w.val = (⟨highestRoot s b, highestRoot_mem_unipotent h2 s b⟩ : U) :=
      Subtype.ext hw
    exact hwu ▸ w.property

theorem mem_center_iff_highestRoot [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (z : unipotent K (s + 3)) :
    z ∈ Subgroup.center (unipotent K (s + 3)) ↔ ∃ a : K, z.val = highestRoot s a := by
  constructor
  · exact central_unipotent_is_highestRoot h2 s z
  · rintro ⟨a, ha⟩
    have he : z = (⟨highestRoot s a, highestRoot_mem_unipotent h2 s a⟩ : unipotent K (s + 3)) :=
      Subtype.ext ha
    exact he.symm ▸ highestRoot_central p h2 s a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
