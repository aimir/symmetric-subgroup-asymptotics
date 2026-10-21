import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerHead
import Mathlib.LinearAlgebra.Isomorphisms

/-! When the actual constant layer is a scalar hyperplane, the original
module state is the graph of one scalar linear form on its actual pair-sum
layer. This reduces the width-four equality cases to2 or8 sections rather
than enumerating all sixteen-dimensional invariant submodules. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

def pairZeroRestriction : (X → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2) where
  toFun f i := f (F.frame (i, 0))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pairZeroRestriction_constant (v : Fin w → ZMod 2) :
    F.pairZeroRestriction (F.pairConstant v) = v := by
  ext i
  exact F.pairConstant_frame v i 0

/-- A full actual constant layer determines the state uniquely. -/
theorem pairModule_eq_pairSum_preimage_of_constant_top
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hL : (F.pairConstantModuleLayer W).toSubmodule = ⊤) :
    W.toSubmodule = (F.pairSumModuleLayer W).toSubmodule.comap F.pairSum := by
  apply le_antisymm
  · intro f hf
    exact ⟨f, hf, rfl⟩
  · intro f hf
    obtain ⟨g, hg, he⟩ := hf
    have hsum : F.pairSum (f - g) = 0 := by rw [map_sub, he, sub_self]
    obtain ⟨a, ha⟩ := F.pairConstant_pairSum_exact_linear.ge hsum
    change F.pairConstant a = f - g at ha
    have haL : a ∈ (F.pairConstantModuleLayer W).toSubmodule := by rw [hL]; trivial
    have hd : f - g ∈ W.toSubmodule := by
      change F.pairConstant a ∈ W.toSubmodule at haL
      rwa [ha] at haL
    simpa only [sub_add_cancel] using W.toSubmodule.add_mem hd hg

/-- The same original point module, with a hyperplane constant layer,
is specified by one scalar form on its retained pair-sum image. -/
theorem exists_pairModule_graph_of_constant_hyperplane
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (ell : (Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = ell.ker) :
    ∃ phi : (F.pairSumModuleLayer W).toSubmodule →ₗ[ZMod 2] ZMod 2,
      ∀ f : X → ZMod 2, f ∈ W.toSubmodule ↔
        ∃ hsum : F.pairSum f ∈ (F.pairSumModuleLayer W).toSubmodule,
          ell (F.pairZeroRestriction f) = phi ⟨F.pairSum f, hsum⟩ := by
  let q := (F.pairSumLayerProjection W).toLinearMap
  let z := (ell.comp F.pairZeroRestriction).comp W.toSubmodule.subtype
  have hq : Function.Surjective q := F.pairSumLayerProjection_surjective W
  have hkill : q.ker ≤ z.ker := by
    intro v hv
    have hsum : F.pairSum v.val = 0 := congrArg Subtype.val hv
    obtain ⟨a, ha⟩ := F.pairConstant_pairSum_exact_linear.ge hsum
    change F.pairConstant a = v.val at ha
    have haL : a ∈ (F.pairConstantModuleLayer W).toSubmodule := by
      change F.pairConstant a ∈ W.toSubmodule
      rw [ha]
      exact v.property
    rw [hL] at haL
    change ell (F.pairZeroRestriction v.val) = 0
    rw [← ha, F.pairZeroRestriction_constant]
    exact haL
  let phi := (q.ker.liftQ z hkill).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hphi (v : W.toSubmodule) : phi (q v) = z v := by
    change q.ker.liftQ z hkill ((q.quotKerEquivOfSurjective hq).symm (q v)) = z v
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨phi, ?_⟩
  intro f
  constructor
  · intro hf
    refine ⟨⟨f, hf, rfl⟩, ?_⟩
    exact (hphi ⟨f, hf⟩).symm
  · rintro ⟨hsum, he⟩
    obtain ⟨g, hg⟩ := hq ⟨F.pairSum f, hsum⟩
    have hgsum : F.pairSum g.val = F.pairSum f := congrArg Subtype.val hg
    have hzero : F.pairSum (f - g.val) = 0 := by rw [map_sub, hgsum, sub_self]
    obtain ⟨a, ha⟩ := F.pairConstant_pairSum_exact_linear.ge hzero
    change F.pairConstant a = f - g.val at ha
    have hvalue : ell (F.pairZeroRestriction f) = ell (F.pairZeroRestriction g.val) := by
      calc
        _ = phi ⟨F.pairSum f, hsum⟩ := he
        _ = phi (q g) := congrArg phi hg.symm
        _ = ell (F.pairZeroRestriction g.val) := hphi g
    have ha0 : ell a = 0 := by
      rw [← F.pairZeroRestriction_constant a, ha, map_sub, map_sub, hvalue, sub_self]
    have haL : a ∈ (F.pairConstantModuleLayer W).toSubmodule := by
      rw [hL]
      exact ha0
    have hd : f - g.val ∈ W.toSubmodule := by
      change F.pairConstant a ∈ W.toSubmodule at haL
      rwa [ha] at haL
    simpa only [sub_add_cancel] using W.toSubmodule.add_mem hd g.property

end SymmetricSubgroupAsymptotics.BinaryPairFrame
