import Mathlib.Algebra.Lie.Basis

/-! An elementwise form of the checked triangular decomposition of a
LieAlgebra.Basis. The negative and positive summands remain in their
actual generated Lie spans. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGLieBasisTriangularDecomposition
variable {I R L : Type*} [Finite I] [CommRing R] [LieRing L] [LieAlgebra R L]

theorem decompose (b : LieAlgebra.Basis I R L) (x : L) :
    ∃h∈b.cartan,∃f∈LieSubalgebra.lieSpan R L (Set.range b.f),
      ∃e∈LieSubalgebra.lieSpan R L (Set.range b.e),h+f+e=x := by
  have ht : b.cartan.toLieSubmodule⊔b.borelLower⊔b.borelUpper=⊤ := by
    simpa using b.iSup_cartan_borelLower_borelUpper_eq_top
  have hx : x∈b.cartan.toLieSubmodule⊔b.borelLower⊔b.borelUpper := by
    rw [ht]
    trivial
  obtain ⟨u,hu,e,he,hue⟩ := (LieSubmodule.mem_sup _ _ _).mp hx
  obtain ⟨h,hh,f,hf,hhf⟩ := (LieSubmodule.mem_sup _ _ _).mp hu
  refine ⟨h,hh,f,hf,e,he,?_⟩
  rw [hhf,hue]

end SymmetricSubgroupAsymptotics.CFSGLieBasisTriangularDecomposition
