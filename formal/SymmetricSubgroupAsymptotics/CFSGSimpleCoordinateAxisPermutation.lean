import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxes
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.Perm.Basic

/-! A coordinate automorphism sending each literal axis onto an axis
induces a genuine permutation of the finite coordinate labels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisPermutation
open CFSGSimpleCoordinateAxes
variable {J K : Type*} [Finite J] [DecidableEq J] [AddCommGroup K] [Nontrivial K]

theorem exists_axis_permutation (F : MulAut (Multiplicative (J→K)))
    (hF : ∀i : J,∃j : J,(axis (K:=K) i).map F.toMonoidHom=axis (K:=K) j) :
    ∃σ : Equiv.Perm J,∀i : J,(axis (K:=K) i).map F.toMonoidHom=axis (K:=K) (σ i) := by
  classical
  choose φ hφ using hF
  have hinj : Function.Injective φ := by
    intro i j hij
    apply (axis_injective (K:=K) (J:=J))
    apply Subgroup.map_injective (f := F.toMonoidHom) F.injective
    rw [hφ i,hφ j,hij]
  let σ : Equiv.Perm J := Equiv.ofBijective φ ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨σ,hφ⟩

theorem axis_permutation_unique (F : MulAut (Multiplicative (J→K)))
    (σ τ : Equiv.Perm J)
    (hσ : ∀i : J,(axis (K:=K) i).map F.toMonoidHom=axis (K:=K) (σ i))
    (hτ : ∀i : J,(axis (K:=K) i).map F.toMonoidHom=axis (K:=K) (τ i)) : σ=τ := by
  apply Equiv.ext
  intro i
  exact (axis_injective (K:=K) (J:=J)) ((hσ i).symm.trans (hτ i))

end SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisPermutation
