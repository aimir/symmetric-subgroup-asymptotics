import Mathlib.LinearAlgebra.StdBasis

/-! Literal coordinate support characterizes spans of coordinate vectors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem mem_span_single_image (I : Set n) (v : n→F) :
    v∈Submodule.span F ((fun i : n => (Pi.single i 1 : n→F)) '' I)↔
      ∀i∉I,v i=0 := by
  let b := Pi.basisFun F n
  have hb : (fun i : n => (Pi.single i 1 : n→F))=b := by
    funext i
    exact (Pi.basisFun_apply F n i).symm
  rw [hb,b.mem_span_image]
  constructor
  · intro hv i hi
    by_contra hne
    exact hi (hv (Finsupp.mem_support_iff.mpr (by simpa only [Pi.basisFun_repr] using hne)))
  · intro hv i hi
    by_contra hni
    exact (Finsupp.mem_support_iff.mp hi) (by simpa only [Pi.basisFun_repr] using hv i hni)

end SymmetricSubgroupAsymptotics
