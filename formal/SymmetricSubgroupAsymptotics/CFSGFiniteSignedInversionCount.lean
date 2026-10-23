import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! A finite signed-set inversion count decreases under a simple
reflection. All roots other than the distinguished positive root are
reindexed by the actual involution; no Coxeter enumeration is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteSignedInversionCount
variable {R : Type*} [Fintype R] [DecidableEq R]

def inversionCount (Positive : R→Prop) (w : Equiv.Perm R) : ℕ :=
  ∑ k ∈ Finset.univ.filter Positive,if Positive (w k) then 0 else 1

theorem reflection_drop (Positive : R→Prop) (s w : Equiv.Perm R) (a : R)
    (ha : Positive a) (hs : Function.Involutive s)
    (hsa : ¬Positive (s a))
    (hpres : ∀k,Positive k→k≠a→Positive (s k))
    (hwa : ¬Positive (w a)) (hwsa : Positive (w (s a))) :
    inversionCount Positive (w*s)+1=inversionCount Positive w := by
  let P := Finset.univ.filter Positive
  let f : R→ℕ := fun k=>if Positive (w k) then 0 else 1
  have haP : a∈P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  have hclosed (k : R) (hk : k∈P.erase a) : s k∈P.erase a := by
    have hkP : k∈P := Finset.mem_of_mem_erase hk
    have hkp : Positive k := (Finset.mem_filter.mp hkP).2
    have hka : k≠a := by
      intro he
      subst k
      simpa only [Finset.notMem_erase] using hk
    have hska : s k≠a := by
      intro he
      have he' : k=s a := by simpa only [hs k] using congrArg s he
      exact hsa (he' ▸ hkp)
    exact Finset.mem_erase.mpr ⟨hska,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hpres k hkp hka⟩⟩
  have hreindex : (∑k∈P.erase a,f (s k))=∑k∈P.erase a,f k := by
    apply Finset.sum_bij (fun k _=>s k)
    · exact hclosed
    · intro k hk l hl hkl
      exact s.injective hkl
    · intro k hk
      exact ⟨s k,hclosed k hk,hs k⟩
    · intro k hk
      rfl
  have hw : inversionCount Positive w=(∑k∈P.erase a,f k)+1 := by
    calc
      inversionCount Positive w=(∑k∈P.erase a,f k)+f a :=
        (Finset.sum_erase_add P f haP).symm
      _=(∑k∈P.erase a,f k)+1 := by simp only [f,hwa,if_false]
  have hws : inversionCount Positive (w*s)=∑k∈P.erase a,f (s k) := by
    calc
      inversionCount Positive (w*s)=(∑k∈P.erase a,f (s k))+f (s a) :=
        (Finset.sum_erase_add P (fun k=>f (s k)) haP).symm
      _=∑k∈P.erase a,f (s k) := by simp only [f,hwsa,if_pos,add_zero]
  rw [hws,hreindex,hw]

end SymmetricSubgroupAsymptotics.CFSGFiniteSignedInversionCount
