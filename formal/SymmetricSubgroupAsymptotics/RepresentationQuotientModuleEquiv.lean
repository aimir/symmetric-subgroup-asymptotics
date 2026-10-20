import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads
import Mathlib.RepresentationTheory.Intertwining

/-! Identity coordinates between the actual group-algebra module quotient
and the module of its actual quotient representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

local instance (rho : Representation k G V) : AddCommGroup rho.asModule :=
  inferInstanceAs (AddCommGroup V)

local instance (rho : Representation k G V) : Module k[G] rho.asModule :=
  Representation.instModuleMonoidAlgebraAsModule rho

def quotientRepresentationModuleEquiv (rho : Representation k G V) (T : Subrepresentation rho) :
    (rho.asModule ⧸ T.asSubmodule) ≃ₗ[k[G]]
      (rho.quotient T.toSubmodule (fun g => T.apply_mem_toSubmodule g)).asModule where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    simp only [RingHom.id_apply]
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_smul]; exact congrArg₂ (·+·) ha hb
    | single g a =>
      obtain ⟨v,rfl⟩ := T.asSubmodule.mkQ_surjective x
      simp only [Representation.single_smul,Submodule.mkQ_apply]
      rw [← Submodule.Quotient.mk_smul, Representation.single_smul]
      change (Submodule.Quotient.mk (a • rho g v) : V ⧸ T.toSubmodule) =
        a • (Submodule.Quotient.mk (rho g v) : V ⧸ T.toSubmodule)
      exact Submodule.Quotient.mk_smul T.toSubmodule a (rho g v)

end SymmetricSubgroupAsymptotics
end
