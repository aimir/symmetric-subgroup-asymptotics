import SymmetricSubgroupAsymptotics.BinaryPairAffineCoboundary
import Mathlib.GroupTheory.Abelianization.Defs

/-! If the actual affine quotient module is trivial, its retained cocycle
is an ordinary homomorphism. Consequently every actual derived top element
has a ZERO-offset lift in the SAME original U. This proves selected lifts;
it does not assert the whole original affine extension is split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- No lift is changed until its exact original affine class vanishes. -/
theorem affineClass_eq_zero_of_derived_top
    (htriv : ∀ (t : F.top.range) a, F.affineQuotientRepresentation t a = a)
    (t : F.top.range) (ht : t ∈ commutator F.top.range) : F.affineClass t = 0 := by
  have hone : F.affineClass 1 = 0 := by
    have hh := F.affineClass_mul 1 1
    rw [one_mul,htriv] at hh
    have hh' : F.affineClass 1 + 0 = F.affineClass 1 + F.affineClass 1 := by
      simpa only [add_zero] using hh
    exact (add_left_cancel hh').symm
  let f : F.top.range →* Multiplicative ((I → ZMod 2) ⧸ F.kernelSpace) := {
    toFun := fun b => Multiplicative.ofAdd (F.affineClass b)
    map_one' := by change F.affineClass 1 = 0; exact hone
    map_mul' := by
      intro a b
      change F.affineClass (a*b) = F.affineClass a + F.affineClass b
      rw [F.affineClass_mul,htriv,add_comm] }
  have hf := Abelianization.commutator_subset_ker f ht
  exact MonoidHom.mem_ker.mp hf

/-- The physical zero-offset permutation belongs to the original source.
All other original lifts and offsets remain arbitrary. -/
theorem affinePermutation_zero_mem_of_derived_top
    (htriv : ∀ (t : F.top.range) a, F.affineQuotientRepresentation t a = a)
    (t : F.top.range) (ht : t ∈ commutator F.top.range) :
    F.affinePermutation t.val 0 ∈ U := by
  have hc := F.affineClass_eq_zero_of_derived_top htriv t ht
  obtain ⟨u,hu,hzero⟩ := (F.affine_graph_fibre t 0).mpr (by rw [map_zero,hc])
  have hp : F.top u = t.val := congrArg Subtype.val hu
  have he := F.affinePermutation_original u
  rw [hp,hzero] at he
  exact he.symm ▸ u.property

end SymmetricSubgroupAsymptotics.BinaryPairFrame
