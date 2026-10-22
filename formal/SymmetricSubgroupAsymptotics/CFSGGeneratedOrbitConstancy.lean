import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Constancy along translated generator steps implies constancy on
the generated group. This retains every left translate; checking steps
only at the identity would not suffice. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGGeneratedOrbitConstancy
variable {G Y : Type*} [Group G]

theorem constant_of_generating_right_steps (S : Set G) (hgen : Subgroup.closure S=⊤)
    (F : G→Y) (hstep : ∀a s,s∈S → F (a*s)=F a) : ∀g,F g=F 1 := by
  have hall : ∀g,g∈Subgroup.closure S → ∀a,F (a*g)=F a := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact fun a=>hstep a g hg
    | one => exact fun a=>by rw [mul_one]
    | mul g h hg hh ihg ihh =>
      intro a
      rw [←mul_assoc,ihh,ihg]
    | inv g hg ihg =>
      intro a
      have hh := ihg (a*g⁻¹)
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm
  intro g
  have hg : g∈Subgroup.closure S := by rw [hgen];trivial
  simpa only [one_mul] using hall g hg 1

end SymmetricSubgroupAsymptotics.CFSGGeneratedOrbitConstancy
