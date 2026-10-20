import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators

/-! Reindex only the fibre of an actual block frame. The original group,
permutation domain and top homomorphism are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {X I F F' : Type*} {U : Subgroup (Equiv.Perm X)}

def reindexFibre (C : ProductBlockFrame U I F) (e : F' ≃ F) :
    ProductBlockFrame U I F' where
  frame := (Equiv.prodCongr (Equiv.refl I) e).trans C.frame
  top := C.top
  intertwine u p := by
    simpa only [Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.refl_apply]
      using C.intertwine u (p.1, e p.2)

end SymmetricSubgroupAsymptotics.ProductBlockFrame
