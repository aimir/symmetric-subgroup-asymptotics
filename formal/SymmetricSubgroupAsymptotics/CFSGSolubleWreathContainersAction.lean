import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import Mathlib.GroupTheory.Solvable

/-! Actual soluble wreath envelopes on the original product degree.
Containment of local and top groups gives literal containment of their
permutation wreath envelopes. No faithfulness or order substitute is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers

theorem functionGroup_soluble (D I : Type*) [Group D] [IsSolvable D] :
    IsSolvable (I → D) := by
  obtain ⟨n, hn⟩ := (isSolvable_def D).mp inferInstance
  apply (isSolvable_def (I → D)).mpr
  refine ⟨n, le_antisymm ?_ bot_le⟩
  intro f hf
  apply Subgroup.mem_bot.mpr
  funext i
  have hi : (Pi.evalMonoidHom (fun _ : I => D) i) f ∈ derivedSeries D n :=
    map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom (fun _ : I => D) i) n ⟨f, hf, rfl⟩
  rw [hn] at hi
  exact Subgroup.mem_bot.mp hi

def wreathBaseHom (D Q I : Type*) [Group D] [Group Q] [MulAction Q I] :
    (I → D) →* PermutationalWreathProduct D Q I where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by
    apply PermutationalWreathProduct.ext
    · funext i
      simp only [PermutationalWreathProduct.mul_left, inv_one, one_smul]
    · change (1 : Q) = 1 * 1
      rw [one_mul]

theorem wreath_soluble (D Q I : Type*) [Group D] [Group Q] [MulAction Q I]
    [IsSolvable D] [IsSolvable Q] : IsSolvable (PermutationalWreathProduct D Q I) := by
  letI solubleWreathAction_functions : IsSolvable (I → D) := functionGroup_soluble D I
  apply solvable_of_ker_le_range (wreathBaseHom D Q I)
    (PermutationalWreathProduct.rightHom (D := D) (Q := Q) (I := I))
  intro w hw
  have hr : w.right = 1 := (MonoidHom.mem_ker).mp hw
  refine ⟨w.left, ?_⟩
  apply PermutationalWreathProduct.ext
  · rfl
  · exact hr.symm

def wreathEnvelope {r s : ℕ} (D : Subgroup (Equiv.Perm (Fin r)))
    (Q : Subgroup (Equiv.Perm (Fin s))) : Subgroup (Equiv.Perm (Fin (r * s))) :=
  (PermutationalWreathProduct.toFinPerm (u := r) (s := s) D Q).range

theorem wreathEnvelope_soluble {r s : ℕ} (D : Subgroup (Equiv.Perm (Fin r)))
    (Q : Subgroup (Equiv.Perm (Fin s))) [IsSolvable D] [IsSolvable Q] :
    IsSolvable (wreathEnvelope D Q) := by
  letI solubleWreathAction_source : IsSolvable (PermutationalWreathProduct D Q (Fin s)) :=
    wreath_soluble D Q (Fin s)
  exact solvable_of_surjective
    (PermutationalWreathProduct.toFinPerm (u := r) (s := s) D Q).rangeRestrict_surjective

def wreathInclusion {r s : ℕ} {D D' : Subgroup (Equiv.Perm (Fin r))}
    {Q Q' : Subgroup (Equiv.Perm (Fin s))} (hD : D ≤ D') (hQ : Q ≤ Q') :
    PermutationalWreathProduct D Q (Fin s) →*
      PermutationalWreathProduct D' Q' (Fin s) where
  toFun w := ⟨fun i => ⟨(w.left i : Equiv.Perm (Fin r)), hD (w.left i).property⟩,
    ⟨(w.right : Equiv.Perm (Fin s)), hQ w.right.property⟩⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      rfl
    · rfl
  map_mul' _ _ := by
    apply PermutationalWreathProduct.ext
    · funext i
      rfl
    · rfl

theorem toFinPerm_wreathInclusion {r s : ℕ} {D D' : Subgroup (Equiv.Perm (Fin r))}
    {Q Q' : Subgroup (Equiv.Perm (Fin s))} (hD : D ≤ D') (hQ : Q ≤ Q')
    (w : PermutationalWreathProduct D Q (Fin s)) :
    PermutationalWreathProduct.toFinPerm (u := r) (s := s) D' Q' (wreathInclusion hD hQ w) =
      PermutationalWreathProduct.toFinPerm (u := r) (s := s) D Q w := by
  apply Equiv.ext
  intro p
  rfl

theorem wreathEnvelope_mono {r s : ℕ} {D D' : Subgroup (Equiv.Perm (Fin r))}
    {Q Q' : Subgroup (Equiv.Perm (Fin s))} (hD : D ≤ D') (hQ : Q ≤ Q') :
    wreathEnvelope D Q ≤ wreathEnvelope D' Q' := by
  rintro _ ⟨w, rfl⟩
  exact ⟨wreathInclusion hD hQ w, toFinPerm_wreathInclusion hD hQ w⟩

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
