import SymmetricSubgroupAsymptotics.MarkedC4ActualOrderedSubdirectTransport
import SymmetricSubgroupAsymptotics.MarkedC4ActualHistoryPriority
import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessHistoryPartition

/-! Original-factor history transport under an ACTUAL physical order.
The marker is unchanged, and every isolated normal remains in the SAME
original group F(e j); no quotient is assigned a transitive action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryOrderTransport
open ActualPeelNormalChains ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)]
  (M : Type) [Group M] (e : Equiv.Perm (Fin t))
abbrev Reordered := fun j => F (e j)

def ambientEquiv : ((∀ i,F i) × M) ≃* ((∀ j,Reordered F e j) × M) :=
  MulEquiv.prodCongr (ActualOrderedSubdirectTransport.physicalEquiv e F) (MulEquiv.refl M)

def image (J : Subgroup ((∀ i,F i) × M)) := J.map (ambientEquiv F M e).toMonoidHom

def code (J : Family F M) : Family (Reordered F e) M := by
  refine ⟨image F M e J.val,?_⟩
  intro j g
  obtain ⟨h,hh⟩ := J.property (e j) g
  exact ⟨⟨ambientEquiv F M e h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩

theorem code_injective : Function.Injective (code F M e) := by
  intro J K he
  apply Subtype.ext
  exact Subgroup.map_injective (f := (ambientEquiv F M e).toMonoidHom)
    (ambientEquiv F M e).injective (congrArg Subtype.val he)

private theorem mem_remaining_iff (a : Equiv.Perm (Fin t)) (m : ℕ) (i : Fin t) :
    i∈remaining a m ↔ m ≤ (a.symm i).val := by
  simp only [remaining,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Exact original normal-factor transport for every retained tail. -/
theorem factor_transport (J : Subgroup ((∀ i,F i) × M)) (m : ℕ) (j : Fin t) :
    factor (Reordered F e) (image F M e J) (remaining 1 m) j=
      factor F J (remaining e m) (e j) := by
  ext g
  constructor
  · rintro ⟨h,hh,heg⟩
    obtain ⟨z,hz,hzh⟩ := h.property
    let x : J := ⟨z,hz⟩
    refine ⟨x,⟨?_,?_⟩,?_⟩
    · exact (congrArg (fun w : (∀ k,Reordered F e k) × M => w.2) hzh).trans hh.1
    · apply Subgroup.mem_iInf.mpr
      intro k
      rcases k with ⟨k,hkm,hkne⟩
      obtain ⟨k',rfl⟩ := e.surjective k
      have hm : m ≤ k'.val := by
        have ht := (mem_remaining_iff e m (e k')).mp hkm
        simpa only [e.symm_apply_apply] using ht
      have hne : k'≠j := by intro heq; exact hkne (congrArg e heq)
      have hmem : k'∈remaining (1 : Equiv.Perm (Fin t)) m := by
        apply (mem_remaining_iff 1 m k').mpr
        exact hm
      have hk := (Subgroup.mem_iInf.mp hh.2) ⟨k',hmem,hne⟩
      exact (congrArg (fun w : (∀ k,Reordered F e k) × M => w.1 k') hzh).trans hk
    · exact (congrArg (fun w : (∀ k,Reordered F e k) × M => w.1 j) hzh).trans heg
  · rintro ⟨h,hh,heg⟩
    let x : image F M e J := ⟨ambientEquiv F M e h.val,⟨h.val,h.property,rfl⟩⟩
    refine ⟨x,⟨hh.1,?_⟩,heg⟩
    apply Subgroup.mem_iInf.mpr
    intro k
    have hm : m ≤ k.val.val := (mem_remaining_iff 1 m k.val).mp k.property.1
    have hmem : e k.val∈remaining e m := by
      apply (mem_remaining_iff e m (e k.val)).mpr
      simpa only [e.symm_apply_apply] using hm
    have hne : e k.val≠e j := fun heq => k.property.2 (e.injective heq)
    exact (Subgroup.mem_iInf.mp hh.2) ⟨e k.val,hmem,hne⟩

def rowsReindex [∀ i,Finite (F i)] (R : ActualQuotientTableauMenus.RowMenu F) :
    ActualQuotientTableauMenus.RowMenu (Reordered F e) := fun j => R (e j)

theorem chains_transport [∀ i,Finite (F i)] (J : Subgroup ((∀ i,F i) × M)) :
    normalChains (Reordered F e) (image F M e J) 1=
      rowsReindex F e (normalChains F J e) := by
  funext j
  apply Subtype.ext
  funext m
  exact factor_transport F M e J m.val j

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryOrderTransport
