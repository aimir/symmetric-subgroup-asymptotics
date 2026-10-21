import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-! A finite field is generated as a subring by one actual unit. This
uses cyclicity of the unit group and includes all prime-field constants. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldScalars
variable (F : Type*) [Field F] [Finite F]

/-- An actual multiplicative generator also generates the whole finite
field as a subring; no unspecified field-presentation identification is
needed. -/
theorem exists_unit_subring_generator :
    ∃ g : Fˣ,Subring.closure ({(g : F)} : Set F)=⊤ := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Fˣ)
  refine ⟨g,?_⟩
  apply top_unique
  intro a _
  by_cases ha : a=0
  · rw [ha]
    exact (Subring.closure _).zero_mem
  let u : Fˣ := Units.mk0 a ha
  obtain ⟨k,hk⟩ : u∈Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg u)
  have hval : (g : F)^k=a := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_mk0,u] using congrArg (fun v : Fˣ => (v : F)) hk
  rw [←hval]
  exact (Subring.closure _).pow_mem (Subring.subset_closure (by simp)) k

end SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldScalars
