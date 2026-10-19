import SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates

/-! The cubic-fixed part of the actual two-head permutation module is
fixed by the WHOLE three-point top. This is a property of the physical
constant vectors, not a centrality assumption on a target quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates

@[simp] theorem coordinates_scalar
    (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) (j : Fin 2) (v : Vector) :
    (coordinates T hrotation).scalar j v=
      (v (j,1)+v (j,2),v (j,0)+v (j,1)) := rfl

private theorem binary_add_zero : ∀ a b : ZMod 2,a+b=0 → a=b := by decide +kernel

/-- Vanishing of the two scalar coordinates makes each original head
constant on the three physical coarse labels. -/
theorem scalar_zero_constant
    (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) (v : Vector)
    (h : ∀ j,(coordinates T hrotation).scalar j v=0) :
    ∀ j i,v (j,i)=v (j,0) := by
  intro j i
  have hj := h j
  rw [coordinates_scalar] at hj
  have h12 : v (j,1)=v (j,2) :=
    binary_add_zero _ _ (congrArg Prod.fst hj)
  have h01 : v (j,0)=v (j,1) :=
    binary_add_zero _ _ (congrArg Prod.snd hj)
  fin_cases i
  · rfl
  · exact h01.symm
  · exact h12.symm.trans h01.symm

/-- Every element of the retained top fixes the cubic-fixed head part,
including reflections when the actual top is S3. -/
theorem scalar_zero_fixed
    (T : Subgroup (Equiv.Perm (Fin 3)))
    (hrotation : OddMarkerTernaryChart.rotation∈T) (v : Vector)
    (h : ∀ j,(coordinates T hrotation).scalar j v=0) (t : T) :
    representation T t v=v := by
  funext x
  change v (x.1,((t⁻¹ : T) : Equiv.Perm (Fin 3)) x.2)=v (x.1,x.2)
  exact (scalar_zero_constant T hrotation v h x.1 _).trans
    (scalar_zero_constant T hrotation v h x.1 x.2).symm

end SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates
