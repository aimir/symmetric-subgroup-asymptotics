import Mathlib.RepresentationTheory.Irreducible

/-! A commuting operator with an actual eigenvector is scalar on an
irreducible representation. The field need not be algebraically closed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IrreducibleCommutingEigenvalue

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V)

def eigenspace (f : Module.End k V) (a : k)
    (hcomm : ∀ (g : G) (v : V),f (rho g v)=rho g (f v)) : Subrepresentation rho where
  toSubmodule := {
    carrier := {v | f v=a • v}
    zero_mem' := by simp
    add_mem' := by
      intro v w hv hw
      change f v=a • v at hv
      change f w=a • w at hw
      change f (v+w)=a • (v+w)
      rw [map_add,hv,hw,smul_add]
    smul_mem' := by
      intro c v hv
      change f v=a • v at hv
      change f (c • v)=a • (c • v)
      rw [map_smul,hv,smul_smul,smul_smul,mul_comm] }
  apply_mem_toSubmodule g v hv := by
    change f (rho g v)=a • rho g v
    rw [hcomm,hv,map_smul]

theorem apply_eq_smul_of_eigenvector
    (hrho : Representation.IsIrreducible rho)
    (f : Module.End k V) (a : k)
    (hcomm : ∀ (g : G) (v : V),f (rho g v)=rho g (f v))
    (v : V) (hv : v≠0) (heigen : f v=a • v) :
    ∀ w : V,f w=a • w := by
  letI : Representation.IsIrreducible rho := hrho
  have htop : eigenspace rho f a hcomm=⊤ := by
    rcases eq_bot_or_eq_top (eigenspace rho f a hcomm) with hb|ht
    · have hm : v∈eigenspace rho f a hcomm := heigen
      have hz : v∈(⊥ : Subrepresentation rho) := hb ▸ hm
      exact (hv hz).elim
    · exact ht
  intro w
  have hm : w∈eigenspace rho f a hcomm := by rw [htop]; trivial
  exact hm

theorem operator_eq_smul_of_eigenvector
    (hrho : Representation.IsIrreducible rho)
    (f : Module.End k V) (a : k)
    (hcomm : ∀ (g : G) (v : V),f (rho g v)=rho g (f v))
    (v : V) (hv : v≠0) (heigen : f v=a • v) :
    f=a • (1 : Module.End k V) := by
  ext w
  exact apply_eq_smul_of_eigenvector rho hrho f a hcomm v hv heigen w

end SymmetricSubgroupAsymptotics.IrreducibleCommutingEigenvalue
