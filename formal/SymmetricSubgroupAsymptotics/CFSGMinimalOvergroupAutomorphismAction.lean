import SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.Perm.Basic

/-! An automorphism preserving a subgroup permutes every finite,
distinct, exhaustive labelled family of its minimal strict overgroups.
The permutation is constructed from actual subgroup images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction
open CFSGSurjectiveMinimalOvergroups
variable {G : Type*} [Group G] {I : Type*} [Finite I]

theorem exists_family_permutation (f : MulAut G) (P : I → Subgroup G)
    (hinj : Function.Injective P)
    (himages : ∀ i, ∃ j, (P i).map f.toMonoidHom = P j) :
    ∃ sigma : Equiv.Perm I, ∀ i, (P i).map f.toMonoidHom = P (sigma i) := by
  classical
  choose phi hphi using himages
  have hphi_inj : Function.Injective phi := by
    intro i j hij
    apply hinj
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [hphi i, hphi j, hij]
  exact ⟨Equiv.ofBijective phi ⟨hphi_inj, Finite.surjective_of_injective hphi_inj⟩, hphi⟩

theorem family_permutation_unique (f : MulAut G) (P : I → Subgroup G)
    (hinj : Function.Injective P) (sigma tau : Equiv.Perm I)
    (hsigma : ∀ i, (P i).map f.toMonoidHom = P (sigma i))
    (htau : ∀ i, (P i).map f.toMonoidHom = P (tau i)) : sigma = tau := by
  apply Equiv.ext
  intro i
  exact hinj ((hsigma i).symm.trans (htau i))

theorem exists_minimal_overgroup_permutation (B : Subgroup G) (P : I → Subgroup G)
    (hBP : ∀ i, B < P i)
    (hmin : ∀ i, ∀ H : Subgroup G, B < H → H ≤ P i → H = P i)
    (hcover : ∀ H : Subgroup G, B < H →
      (∀ M : Subgroup G, B < M → M ≤ H → M = H) → ∃ i, H = P i)
    (hinj : Function.Injective P) (f : MulAut G) (hB : B.map f.toMonoidHom = B) :
    ∃ sigma : Equiv.Perm I, ∀ i, (P i).map f.toMonoidHom = P (sigma i) := by
  have hker : f.toMonoidHom.ker ≤ B := by
    rw [(MonoidHom.ker_eq_bot_iff f.toMonoidHom).mpr f.injective]
    exact bot_le
  apply exists_family_permutation f P hinj
  intro i
  have hstrict := map_lt_map_of_kernel_le f.toMonoidHom hker (hBP i)
  have hminimal := map_minimal_overgroup f.toMonoidHom f.surjective hker (hBP i) (hmin i)
  rw [hB] at hstrict hminimal
  exact hcover _ hstrict hminimal

end SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction
