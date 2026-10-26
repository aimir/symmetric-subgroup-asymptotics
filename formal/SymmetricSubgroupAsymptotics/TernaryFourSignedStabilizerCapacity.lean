import SymmetricSubgroupAsymptotics.TernaryFourProperModuleSignKernel
import SymmetricSubgroupAsymptotics.SignedMonomialStabilizerClassBound
import SymmetricSubgroupAsymptotics.OriginalBinaryFourTopClassCubeBound
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets

/-! Class capacities of actual signed four-coordinate stabilizers.
The zero vector keeps the actual signed subgroup; each nonzero vector
uses the proved kernel/range bound on its original support and zeros. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourSignedStabilizerCapacity
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open SignedMonomialStabilizerClassBound

theorem subgroup_class_card_le_fortyTwo (R : Subgroup Signed)
    (ht : Function.Surjective (topHom R)) : Nat.card (ConjClasses R)≤42 := by
  letI : MulAction R (Fin 4) := MulAction.compHom _ (topHom R)
  letI : MulAction.IsPretransitive R (Fin 4) := ⟨fun i j => by
    obtain ⟨g,hg⟩ := ht (Equiv.swap i j)
    exact ⟨g,(congrArg (fun s : Equiv.Perm (Fin 4) => s i) hg).trans
      (Equiv.swap_apply_left i j)⟩⟩
  let π : Multiplicative (ZMod 2) × Fin 4 → Fin 4 := Prod.snd
  have hπ : ∀ (g : R) (ω : Multiplicative (ZMod 2) × Fin 4),
      π (g • ω)=g • π ω := fun _ _ => rfl
  have hsize (i : Fin 4) : Nat.card (originalBlockFibre π i)≤2 := by
    let e : originalBlockFibre π i ≃ Multiplicative (ZMod 2) := {
      toFun := fun ω => ω.val.1
      invFun := fun z => ⟨(z,i),rfl⟩
      left_inv := fun ω => Subtype.ext (Prod.ext rfl ω.property.symm)
      right_inv := fun _ => rfl }
    have hc := (Nat.card_congr e).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
        (Nat.card_zmod 2))
    exact hc.le
  exact OriginalBinaryFourTopClassCubeBound.class_card_le_fortyTwo π hπ hsize (Nat.card_fin 4)

def supportBudget (k : ℕ) : ℕ :=
  if k=1 then 48 else if k=2 then 16 else if k=3 then 6 else 5

theorem nonzero_stabilizer_class_card_le (R : Subgroup Signed)
    (v : Fin 4 → ZMod 3) (hv : v≠0) :
    Nat.card (ConjClasses (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v))≤
      supportBudget (Nat.card {i : Fin 4 // v i≠0}) := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let t := topHom R
  let a : R → Fin 4 → (ZMod 3)ˣ := fun g i => coefficient (Fin 4) g.val i
  have hρ : Function.Injective ρ := (linearHom_injective (Fin 4)).comp Subtype.val_injective
  have hformula : ∀ (g : R) (w : Fin 4 → ZMod 3) (i : Fin 4),
      ρ g w i=(a g i : ZMod 3)*w ((t g).symm i) :=
    fun g w i => linearHom_apply (Fin 4) g.val w i
  have hunits : Nat.card (ZMod 3)ˣ=2 :=
    (Nat.card_congr OddMarkerTernaryChart.signScalarEquiv.symm.toEquiv).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
        (Nat.card_zmod 2))
  let k := Nat.card {i : Fin 4 // v i≠0}
  let z := Nat.card {i : Fin 4 // v i=0}
  have hsum : z+k=4 := by
    change Nat.card {i : Fin 4 // v i=0}+Nat.card {i : Fin 4 // v i≠0}=4
    rw [←Nat.card_sum]
    exact (Nat.card_congr (Equiv.sumCompl (fun i : Fin 4 => v i=0))).trans (Nat.card_fin 4)
  have hkpos : 0<k := by
    have hnon : Nonempty {i : Fin 4 // v i≠0} := by
      by_contra h
      apply hv
      funext i
      exact Classical.byContradiction (fun hi => h ⟨⟨i,hi⟩⟩)
    letI := hnon
    exact Nat.card_pos
  have hcases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hcases with hk|hk|hk|hk
  · have hlocal (L : Subgroup (Equiv.Perm {i : Fin 4 // v i≠0})) :
        Nat.card (ConjClasses L)≤1 := by
      have hcard := L.card_le_card_group
      rw [Nat.card_perm,show Nat.card {i : Fin 4 // v i≠0}=1 from hk] at hcard
      exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans hcard
    have h := class_card_le_zero_coefficients_mul_support_budget ρ t a hformula hρ v 1 hlocal
    have hz : Nat.card {i : Fin 4 // v i=0}=3 := by change z=3; omega
    rw [hunits,hz] at h
    rw [show Nat.card {i : Fin 4 // v i≠0}=1 from hk]
    exact h
  · have h := class_card_le_zero_coefficients_mul_support_budget ρ t a hformula hρ v 2
      (SmallPermutationClassBudgets.subgroup_class_card_le_two (show
        Nat.card {i : Fin 4 // v i≠0}≤2 from hk.le))
    have hz : Nat.card {i : Fin 4 // v i=0}=2 := by change z=2; omega
    rw [hunits,hz] at h
    rw [show Nat.card {i : Fin 4 // v i≠0}=2 from hk]
    exact h
  · have h := class_card_le_zero_coefficients_mul_support_budget ρ t a hformula hρ v 3
      (SmallPermutationClassBudgets.subgroup_class_card_le_three (show
        Nat.card {i : Fin 4 // v i≠0}≤3 from hk.le))
    have hz : Nat.card {i : Fin 4 // v i=0}=1 := by change z=1; omega
    rw [hunits,hz] at h
    rw [show Nat.card {i : Fin 4 // v i≠0}=3 from hk]
    exact h
  · have hlocal (L : Subgroup (Equiv.Perm {i : Fin 4 // v i≠0})) :
        Nat.card (ConjClasses L)≤5 :=
      FourPointPermutationClassBound.faithful_action_class_card_le_five
        L {i : Fin 4 // v i≠0} hk
    have h := class_card_le_zero_coefficients_mul_support_budget ρ t a hformula hρ v 5 hlocal
    have hz : Nat.card {i : Fin 4 // v i=0}=0 := by change z=0; omega
    rw [hunits,hz] at h
    rw [show Nat.card {i : Fin 4 // v i≠0}=4 from hk]
    exact h

end SymmetricSubgroupAsymptotics.TernaryFourSignedStabilizerCapacity
