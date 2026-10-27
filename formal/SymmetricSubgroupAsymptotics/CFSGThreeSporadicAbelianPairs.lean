import SymmetricSubgroupAsymptotics.CFSGOddRotationAbelianPairs
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.HS
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.McL
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.He
import Mathlib.Tactic.FinCases

/-! Three more literal presentations have soluble generating conjugates.
These are direct properties of the original models, not Sylow-normalizer,
intravariance or recognition statements. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGThreeSporadicAbelianPairs
open CFSG.Models

private theorem presentation_pair_closure (rels : Set (FreeGroup (Fin 2))) :
    Subgroup.closure ({PresentedGroup.of (0 : Fin 2), PresentedGroup.of (1 : Fin 2)} :
      Set (PresentedGroup rels)) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of rels]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> exact Subgroup.subset_closure (by simp)

namespace HS
open CFSG.Models.Presentations.HS
def x : Model := PresentedGroup.of (0 : Fin 2)
def y : Model := PresentedGroup.of (1 : Fin 2)

theorem x_square : x ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (FreeGroup.of (0 : Fin 2)) ^ 2)
    (by change _ ∈ relators; exact List.mem_cons_self)
  simpa only [x, map_pow, PresentedGroup.of] using h

theorem comm_fifth : (commWord x y) ^ 5 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (commWord (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2))) ^ 5)
    (by
      change _ ∈ relators
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  simpa only [commWord, x, y, map_pow, map_mul, map_inv, PresentedGroup.of] using h

theorem soluble_pair :
    ∃ (U : Subgroup Model) (g : Model), IsSolvable U ∧
      Subgroup.closure ((U : Set Model) ∪ U.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  have hi : x⁻¹ = x := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using x_square)
  have hr : (x * (y⁻¹ * x * y)) ^ 5 = 1 := by
    simpa only [commWord, hi, mul_assoc] using comm_fifth
  exact CFSGOddRotationAbelianPairs.soluble_pair x y 2 x_square hr
    (presentation_pair_closure {w | w ∈ relators})
end HS

namespace McL
open CFSG.Models.Presentations.McL
def x : Model := PresentedGroup.of (0 : Fin 2)
def y : Model := PresentedGroup.of (1 : Fin 2)

theorem x_square : x ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (FreeGroup.of (0 : Fin 2)) ^ 2)
    (by change _ ∈ relators; exact List.mem_cons_self)
  simpa only [x, map_pow, PresentedGroup.of] using h

theorem comm_fifth : (commWord x y) ^ 5 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (commWord (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2))) ^ 5)
    (by
      change _ ∈ relators
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simpa only [commWord, x, y, map_pow, map_mul, map_inv, PresentedGroup.of] using h

theorem soluble_pair :
    ∃ (U : Subgroup Model) (g : Model), IsSolvable U ∧
      Subgroup.closure ((U : Set Model) ∪ U.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  have hi : x⁻¹ = x := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using x_square)
  have hr : (x * (y⁻¹ * x * y)) ^ 5 = 1 := by
    simpa only [commWord, hi, mul_assoc] using comm_fifth
  exact CFSGOddRotationAbelianPairs.soluble_pair x y 2 x_square hr
    (presentation_pair_closure {w | w ∈ relators})
end McL

namespace He
open CFSG.Models.Presentations.He
def x : Model := PresentedGroup.of (0 : Fin 2)
def y : Model := PresentedGroup.of (1 : Fin 2)

theorem x_square : x ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (FreeGroup.of (0 : Fin 2)) ^ 2)
    (by change _ ∈ relators; exact List.mem_cons_self)
  simpa only [x, map_pow, PresentedGroup.of] using h

theorem y_seventh : y ^ 7 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (FreeGroup.of (1 : Fin 2)) ^ 7)
    (by change _ ∈ relators; exact List.mem_cons_of_mem _ List.mem_cons_self)
  simpa only [y, map_pow, PresentedGroup.of] using h

theorem comm_cube_fifth : (commWord x (y ^ 3)) ^ 5 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := {w | w ∈ relators})
    (x := (commWord (FreeGroup.of (0 : Fin 2)) ((FreeGroup.of (1 : Fin 2)) ^ 3)) ^ 5)
    (by
      change _ ∈ relators
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  simpa only [commWord, x, y, map_pow, map_mul, map_inv, PresentedGroup.of] using h

theorem cube_recovers : (y ^ 3) ^ 5 = y := by
  rw [← pow_mul]
  calc
    y ^ (3 * 5) = y ^ (7 * 2 + 1) := rfl
    _ = y := by rw [pow_succ, pow_mul, y_seventh, one_pow, one_mul]

theorem cube_pair_closure : Subgroup.closure ({x, y ^ 3} : Set Model) = ⊤ := by
  apply top_unique
  rw [← presentation_pair_closure {w | w ∈ relators}]
  apply (Subgroup.closure_le _).mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with h | h
  · subst z
    exact Subgroup.subset_closure (by simp [x])
  · have hz' : z = y := Set.mem_singleton_iff.mp h
    subst z
    have hseed : y ^ 3 ∈ Subgroup.closure ({x, y ^ 3} : Set Model) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hp := Subgroup.pow_mem _ hseed 5
    simpa only [cube_recovers] using hp

theorem soluble_pair :
    ∃ (U : Subgroup Model) (g : Model), IsSolvable U ∧
      Subgroup.closure ((U : Set Model) ∪ U.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  have hi : x⁻¹ = x := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using x_square)
  have hr : (x * ((y ^ 3)⁻¹ * x * y ^ 3)) ^ 5 = 1 := by
    simpa only [commWord, hi, mul_assoc] using comm_cube_fifth
  exact CFSGOddRotationAbelianPairs.soluble_pair x (y ^ 3) 2 x_square hr cube_pair_closure
end He

end SymmetricSubgroupAsymptotics.CFSGThreeSporadicAbelianPairs
