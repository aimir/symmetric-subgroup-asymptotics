import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! A genuine quadratic Witt-dimension ceiling of three prevents two
disjoint singular two-planes from being mutually perpendicular. This
uses Q-singularity, including in characteristic two, and does not infer
a Witt ceiling from the ambient dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticWittThreeAxisBound
open CFSGOrthogonalDIndexQuadraticCorrection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem cross_axis_finrank_le_one (A : QuadraticForm K V)
    (hceiling : ∀ S : Submodule K V, (∀ x ∈ S, A x = 0) → Module.finrank K S ≤ 3)
    (P Q : Submodule K V) (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hd : Disjoint P Q) (hPs : ∀ x ∈ P, A x = 0) (hQs : ∀ x ∈ Q, A x = 0) :
    Module.finrank K (P ⊓ (LinearMap.BilinForm.orthogonal A.polarBilin Q) : Submodule K V) ≤ 1 := by
  let C : Submodule K V := P ⊓ (LinearMap.BilinForm.orthogonal A.polarBilin Q)
  by_contra hn
  change ¬Module.finrank K C ≤ 1 at hn
  have hlarge : 2 ≤ Module.finrank K C := by omega
  have he : C = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hP]; exact hlarge)
  have hPo : P ≤ (LinearMap.BilinForm.orthogonal A.polarBilin Q) := he.ge.trans inf_le_right
  have hc (p : V) (hp : p ∈ P) (q : V) (hq : q ∈ Q) : A.polarBilin p q = 0 :=
    (QuadraticMap.polar_comm (A : V → K) p q).trans (hPo hp q hq)
  have hs : ∀ x ∈ P ⊔ Q, A x = 0 := singular_sup A P Q hPs hQs hc
  have hb := hceiling (P ⊔ Q) hs
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hd.eq_bot, finrank_bot, hP, hQ, add_zero] at hdim
  omega

end SymmetricSubgroupAsymptotics.CFSGQuadraticWittThreeAxisBound
