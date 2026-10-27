import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

/-! Carrier-independent comparison for the ACTUAL derived subgroup modulo
its own full centre.  A perfect kernel of an abelian-valued homomorphism
is precisely the derived subgroup; no finiteness or classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DerivedCenterSandwichEquivalence

variable {G H : Type*} [Group G] [Group H]

abbrev DerivedCenter (G : Type*) [Group G] :=
  (commutator G) ⧸ Subgroup.center (commutator G)

theorem map_commutator (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def]

def derivedEquiv (e : G ≃* H) : commutator G ≃* commutator H :=
  (e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr (map_commutator e))

def congr (e : G ≃* H) : DerivedCenter G ≃* DerivedCenter H :=
  CFSGCenterQuotientEquiv.equiv (derivedEquiv e)

def derivedEquivSelf (G : Type*) [Group G] [Group.IsPerfect G] :
    commutator G ≃* G :=
  (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv

def ofPerfectTarget (e : G ≃* H) [Group.IsPerfect H] :
    DerivedCenter G ≃* H ⧸ Subgroup.center H :=
  (congr e).trans (CFSGCenterQuotientEquiv.equiv (derivedEquivSelf H))

theorem commutator_eq_kernel {A : Type*} [CommGroup A] (f : G →* A)
    [Group.IsPerfect f.ker] : commutator G = f.ker := by
  apply le_antisymm
  · exact Abelianization.commutator_subset_ker f
  · calc
      f.ker = ⁅f.ker,f.ker⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup G),⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := rfl

def ofPerfectKernel {A : Type*} [CommGroup A] (f : G →* A)
    [Group.IsPerfect f.ker] :
    DerivedCenter G ≃* f.ker ⧸ Subgroup.center f.ker :=
  CFSGCenterQuotientEquiv.equiv (MulEquiv.subgroupCongr (commutator_eq_kernel f))

end SymmetricSubgroupAsymptotics.DerivedCenterSandwichEquivalence
