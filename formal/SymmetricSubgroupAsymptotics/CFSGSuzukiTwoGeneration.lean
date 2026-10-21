import SymmetricSubgroupAsymptotics.CFSGSuzukiTwistedWeylExtraction
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentSaturation
import SymmetricSubgroupAsymptotics.CFSGSuzukiZeroFirstBruhat
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import SymmetricSubgroupAsymptotics.CFSGTwoGenerationBasic

/-! Two actual matrices generate every Suzuki model with its original
positive parameter. The pair is a primitive original torus and U(1,0)W.
A commutator supplies a nonzero first coordinate, torus conjugation
supplies all first coordinates, and actual U commutators supply the centre.
No classification of subgroups, order formula, or BN-pair is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiGeneration
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent CFSGSuzukiBruhat

theorem model_le_of_torus_twistedWeyl (m : ℕ) (hm : 1≤m)
    (c : (Field m)ˣ) (hc : ∀ d : (Field m)ˣ,d∈Subgroup.zpowers c)
    (H : Subgroup (CFSGSuzukiTorus.Ambient m))
    (hT : torusElement m c∈H) (hS : twistedWeyl m∈H) :
    CFSG.Models.SuzukiConstruction.subgroup m≤H := by
  have hcard : 4≤Nat.card (Field m) := by
    rw [field_card]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤2*m+1)
  have hsum : (c : Field m)+(c : Field m)⁻¹≠0 := by
    intro he
    have heq := CharTwo.add_eq_zero.mp he
    have hsq : (c : Field m)^2=1 := by
      calc
        (c : Field m)^2=(c : Field m)*(c : Field m) := pow_two _
        _=(c : Field m)⁻¹*(c : Field m) := congrArg (fun x : Field m => x*(c : Field m)) heq
        _=1 := inv_mul_cancel₀ (Units.ne_zero c)
    exact CFSGTypeAPrimitiveUnitSquare.square_ne_one hcard c hc hsq
  obtain ⟨b,hb⟩ := twistedWeyl_torus_commutator m c
  have hcomm : unipotentElement m ((c : Field m)+(c : Field m)⁻¹) b∈H := by
    rw [←hb,commutatorElement_def]
    have hy := H.mul_mem (H.mul_mem hS hT) (H.inv_mem hS)
    exact H.mul_mem (H.mul_mem (H.mul_mem hy hT) (H.inv_mem hy)) (H.inv_mem hT)
  have hprim : ∀ d : (Field m)ˣ,d∈Subgroup.zpowers c⁻¹ := by
    intro d
    rw [Subgroup.zpowers_inv]
    exact hc d
  have hU : unipotentSubgroup m≤H :=
    unipotent_le_of_primitive_scaling m hm H (torusElement m c) hT c⁻¹ hprim
      (((c : Field m)*theta m (c : Field m))⁻¹)
      (by
        intro x y
        simpa only [Units.val_inv_eq_inv_val] using original_torus_conjugation m c x y)
      _ b hsum hcomm
  have hW : weylElement m∈H := by
    have hu : unipotentElement m 1 0∈H := hU ⟨1,0,rfl⟩
    have hh := H.mul_mem (H.inv_mem hu) hS
    change (unipotentElement m 1 0)⁻¹*(unipotentElement m 1 0*weylElement m)∈H at hh
    simpa only [inv_mul_cancel_left] using hh
  exact model_le_of_unipotent_weyl m H hU hW

/-- This equality is in the original GL4 ambient space, with the exact
original model subgroup on the right. -/
theorem closure_torus_twistedWeyl (m : ℕ) (hm : 1≤m)
    (c : (Field m)ˣ) (hc : ∀ d : (Field m)ˣ,d∈Subgroup.zpowers c) :
    Subgroup.closure ({torusElement m c,twistedWeyl m} :
      Set (CFSGSuzukiTorus.Ambient m))=CFSG.Models.SuzukiConstruction.subgroup m := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl|hg
    · exact torusElement_mem_model m c
    · have he := Set.mem_singleton_iff.mp hg
      rw [he]
      exact (CFSG.Models.SuzukiConstruction.subgroup m).mul_mem
        (unipotentElement_mem_model m 1 0) (weylElement_mem_model m)
  · apply model_le_of_torus_twistedWeyl m hm c hc
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

/-- Genuine two-generation of the literal pinned Suzuki model, with its
original m>=1 guard. -/
theorem suzuki_twoGenerated (m : ℕ) (hm : 1≤m) :
    CFSGGeneration.TwoGenerated (CFSG.Models.Suzuki m) := by
  obtain ⟨c,hc⟩ := IsCyclic.exists_generator (α:=(Field m)ˣ)
  exact CFSGGeneration.of_mulEquiv
    (MulEquiv.subgroupCongr (closure_torus_twistedWeyl m hm c hc))
    (CFSGGeneration.closure_pair (torusElement m c) (twistedWeyl m))

end SymmetricSubgroupAsymptotics.CFSGSuzukiGeneration
