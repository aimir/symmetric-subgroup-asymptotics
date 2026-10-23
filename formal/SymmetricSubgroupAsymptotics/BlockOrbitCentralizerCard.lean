import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import SymmetricSubgroupAsymptotics.PrimeIndexAbelianCentralizers
import Mathlib.Data.Finite.Perm

/-! Outside centralizers are detected on a transversal of the original
block orbits of the outside element. The transversal may depend on that
element. No independence of the block coordinates is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BlockOrbitCentralizerCard
open OriginalBlockClassBound PrimeIndexAbelianCentralizers

variable {A Ω X ι : Type} [Group A] [MulAction A Ω] [MulAction A X]
    (b : Ω→X) (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω)
    (g:A) (r:ι→X)

def orbitCoordinates (c:fixedKernel (Kernel (A:=A) (X:=X)) g) :
    ∀i,Equiv.Perm (originalBlockFibre b (r i)) :=
  fun i=>coordinate b hb (r i) c.val

include hb in
theorem orbitCoordinates_injective [FaithfulSMul A Ω]
    (hreach : ∀ω:Ω,∃j:ℤ,∃i:ι,b ((g^j)•ω)=r i) :
    Function.Injective (orbitCoordinates b hb g r) := by
  intro a c he
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α:=Ω)
  intro ω
  obtain ⟨j,i,hi⟩ := hreach ω
  let v : originalBlockFibre b (r i) := ⟨(g^j)•ω,hi⟩
  have hev := congrArg (fun t : Equiv.Perm (originalBlockFibre b (r i))=>(t v:Ω))
    (congrFun he i)
  change (a.val:A)•((g^j)•ω)=(c.val:A)•((g^j)•ω) at hev
  have ha : Commute g (a.val:A) :=
    (Subgroup.mem_centralizer_singleton_iff.mp a.property).symm
  have hc : Commute g (c.val:A) :=
    (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm
  apply MulAction.injective (g^j)
  calc
    (g^j)•((a.val:A)•ω)=(a.val:A)•((g^j)•ω) := by
      simp only [←mul_smul,(ha.zpow_left j).eq]
    _=(c.val:A)•((g^j)•ω) := hev
    _=(g^j)•((c.val:A)•ω) := by
      simp only [←mul_smul,(hc.zpow_left j).eq]

include hb in
theorem fixedKernel_card_le_orbit_product [Finite Ω] [Fintype ι] [FaithfulSMul A Ω]
    (hreach : ∀ω:Ω,∃j:ℤ,∃i:ι,b ((g^j)•ω)=r i) :
    Nat.card (fixedKernel (Kernel (A:=A) (X:=X)) g)≤
      ∏i:ι,(Nat.card (originalBlockFibre b (r i))).factorial := by
  have h := Nat.card_le_card_of_injective (orbitCoordinates b hb g r)
    (orbitCoordinates_injective b hb g r hreach)
  simpa only [Nat.card_pi,Nat.card_perm] using h

end SymmetricSubgroupAsymptotics.BlockOrbitCentralizerCard
