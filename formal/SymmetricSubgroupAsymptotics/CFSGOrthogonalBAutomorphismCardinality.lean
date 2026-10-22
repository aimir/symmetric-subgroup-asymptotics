import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSemilinearPolarIsometry
import Mathlib.SetTheory.Cardinal.Finite

/-! The proved original polar realization injects actual abstract B
automorphisms into special-isometry/field data. Only an upper bound is
needed: no chosen representation is assumed unique, and no arbitrary
quotient automorphism is lifted to the original matrix group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBAutomorphismCardinality
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBPlaneFamilyAction CFSGOrthogonalBFieldGeometry
open CFSGOrthogonalBSemilinearPolarIsometry CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

noncomputable def fieldChoice (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ) (F : MulAut (elementaryProjective K (s+3))) : K≃+*K :=
  Classical.choose (original_field_special_decomposition K p h2 s F)

noncomputable def specialChoice (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ) (F : MulAut (elementaryProjective K (s+3))) : specialFormUnits K (s+3) :=
  Classical.choose (Classical.choose_spec (original_field_special_decomposition K p h2 s F))

theorem choice_spec (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ) (F : MulAut (elementaryProjective K (s+3))) :
    normalizedPoints (s+3) (originalPointAction p h2 s F).val (fieldChoice K p h2 s F)=
      CFSGOrthogonalBSpecialGeometry.point K (s+3) (specialChoice K p h2 s F) :=
  Classical.choose_spec (Classical.choose_spec (original_field_special_decomposition K p h2 s F))

def encoding (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K)≠0) (s : ℕ)
    (F : MulAut (elementaryProjective K (s+3))) : (K≃+*K)×specialFormUnits K (s+3) :=
  (fieldChoice K p h2 s F,specialChoice K p h2 s F)

theorem encoding_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+3))] :
    Function.Injective (encoding K p h2 s) := by
  intro F G h
  have hσ : fieldChoice K p h2 s F=fieldChoice K p h2 s G := congrArg Prod.fst h
  have hg : specialChoice K p h2 s F=specialChoice K p h2 s G := congrArg Prod.snd h
  have he : normalizedPoints (s+3) (originalPointAction p h2 s F).val (fieldChoice K p h2 s F)=
      normalizedPoints (s+3) (originalPointAction p h2 s G).val (fieldChoice K p h2 s F) := by
    rw [choice_spec,hg,←choice_spec,hσ]
  apply originalPointAction_injective p h2 s
  apply Subtype.ext
  apply Equiv.ext
  intro P
  apply (pointEquiv (fieldChoice K p h2 s F).symm (s+3)).injective
  exact congrArg (fun f : Equiv.Perm (Points (gram K (s+3)).toBilin')=>f P) he

theorem automorphism_card_le_special_mul_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+3))] :
    Nat.card (MulAut (elementaryProjective K (s+3)))≤
      Nat.card (specialFormUnits K (s+3))*Nat.card (K≃+*K) := by
  letI : Finite (K≃+*K) := Finite.of_injective
    (fun σ : K≃+*K=>(σ : K→K)) DFunLike.coe_injective
  letI : Finite (specialFormUnits K (s+3)) := Finite.of_injective
    (fun g : specialFormUnits K (s+3)=>(g.val : Mat K (s+3)))
    (fun x y h=>Subtype.ext (Units.ext h))
  have h := Nat.card_le_card_of_injective (encoding K p h2 s) (encoding_injective K p h2 s)
  simpa only [Nat.card_prod,mul_comm] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBAutomorphismCardinality
