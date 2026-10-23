import SymmetricSubgroupAsymptotics.BlockOrbitCentralizerCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-! Any nonidentity permutation of three actual block labels has an
orbit transversal of size at most two. This discharges the varying
two-fibre detector needed for an S3-top transposition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ThreeBlockOrbitRepresentatives
open OriginalBlockClassBound PrimeIndexAbelianCentralizers BlockOrbitCentralizerCard

private theorem third_point (i j : Fin 3) : ∃k : Fin 3,k≠i∧k≠j := by
  fin_cases i <;> fin_cases j <;> decide

theorem permutation_orbit_representatives (s:Equiv.Perm (Fin 3)) (hs:s≠1) :
    ∃r:Fin 2→Fin 3,∀x:Fin 3,∃j:ℤ,∃i:Fin 2,(s^j) x=r i := by
  have hmove : ∃i,s i≠i := by
    by_contra hn
    apply hs
    apply Equiv.ext
    intro i
    change s i=i
    exact not_not.mp (fun hi=>hn ⟨i,hi⟩)
  obtain ⟨i,hi⟩ := hmove
  obtain ⟨k,hki,hks⟩ := third_point i (s i)
  let r : Fin 2→Fin 3 := Fin.cases i (fun _=>k)
  refine ⟨r,fun x=>?_⟩
  have huniv : ({i,s i,k}:Finset (Fin 3))=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hi,Ne.symm hi,hki,hks,Ne.symm hki,Ne.symm hks]
  have hx : x=i∨x=s i∨x=k := by
    have hx' : x∈({i,s i,k}:Finset (Fin 3)) := huniv.symm ▸ Finset.mem_univ x
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hx'
  rcases hx with rfl|rfl|rfl
  · exact ⟨0,0,rfl⟩
  · refine ⟨-1,0,?_⟩
    change s⁻¹ (s i)=i
    exact s.symm_apply_apply i
  · exact ⟨0,1,rfl⟩

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction A (Fin 3)]
    (b:Ω→Fin 3) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem outside_two_fibre_representatives (g:A) (hg:g∉Kernel (A:=A) (X:=Fin 3)) :
    ∃r:Fin 2→Fin 3,∀ω:Ω,∃j:ℤ,∃i:Fin 2,b ((g^j)•ω)=r i := by
  let f : A→*Equiv.Perm (Fin 3) := topMap (A:=A) (X:=Fin 3)
  obtain ⟨r,hr⟩ := permutation_orbit_representatives (f g) hg
  refine ⟨r,fun ω=>?_⟩
  obtain ⟨j,i,hi⟩ := hr (b ω)
  have he : f (g^j) (b ω)=r i := by rwa [map_zpow]
  exact ⟨j,i,(hb (g^j) ω).trans he⟩

include hb in
theorem outside_fixedKernel_card_le_square [Finite Ω] [FaithfulSMul A Ω]
    (a:ℕ) (hsize:∀x,Nat.card (originalBlockFibre b x)≤a)
    (g:A) (hg:g∉Kernel (A:=A) (X:=Fin 3)) :
    Nat.card (fixedKernel (Kernel (A:=A) (X:=Fin 3)) g)≤a.factorial^2 := by
  obtain ⟨r,hr⟩ := outside_two_fibre_representatives b hb g hg
  apply (fixedKernel_card_le_orbit_product b hb g r hr).trans
  calc
    (∏i:Fin 2,(Nat.card (originalBlockFibre b (r i))).factorial)≤∏_i:Fin 2,a.factorial :=
      Finset.prod_le_prod' (fun i _=>Nat.factorial_le (hsize (r i)))
    _=a.factorial^2 := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end SymmetricSubgroupAsymptotics.ThreeBlockOrbitRepresentatives
