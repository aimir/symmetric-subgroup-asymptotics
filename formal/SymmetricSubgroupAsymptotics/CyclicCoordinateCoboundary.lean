import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A cyclic coordinate labeling has product one exactly when it is an
actual coboundary. The potential is the explicit product of preceding
coordinates. This is the cycle-product kernel in wreath conjugacy. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CyclicCoordinateCoboundary

variable {D : Type*} [CommGroup D] {n : ℕ}

theorem partialProd_last (f : Fin n → D) :
    Fin.partialProd f (Fin.last n)=∏i,f i := by
  have ht : (List.ofFn f).take n=List.ofFn f :=
    List.take_of_length_le (by simp)
  simp only [Fin.partialProd,Fin.val_last,ht,Fin.prod_ofFn]

theorem product_coboundary (v : Fin (n+1) → D) :
    (∏i,(v i)⁻¹*v (finRotate (n+1) i))=1 := by
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,
    Equiv.prod_comp (finRotate (n+1)) v,inv_mul_cancel]

theorem exists_coboundary_of_product_one (f : Fin (n+1) → D)
    (hf : (∏i,f i)=1) :
    ∃ v : Fin (n+1) → D,∀i,f i=(v i)⁻¹*v (finRotate (n+1) i) := by
  refine ⟨Fin.partialProd (Fin.init f),?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last,Fin.partialProd_zero,partialProd_last,mul_one]
    have hp : (∏j : Fin n,f j.castSucc)*f (Fin.last n)=1 := by
      simpa only [Fin.prod_univ_castSucc] using hf
    have hh := congrArg (fun t : D => (∏j : Fin n,f j.castSucc)⁻¹*t) hp
    simpa only [Fin.init,← mul_assoc,inv_mul_cancel,one_mul,mul_one] using hh
  · have hrot : finRotate (n+1) j.castSucc=j.succ :=
      finRotate_of_lt j.isLt
    rw [hrot,Fin.partialProd_succ,inv_mul_cancel_left]
    rfl

theorem product_one_iff_exists_coboundary (f : Fin (n+1) → D) :
    (∏i,f i)=1 ↔
      ∃ v : Fin (n+1) → D,∀i,f i=(v i)⁻¹*v (finRotate (n+1) i) := by
  constructor
  · exact exists_coboundary_of_product_one f
  · rintro ⟨v,hv⟩
    have he : f=(fun i => (v i)⁻¹*v (finRotate (n+1) i)) := funext hv
    rw [he]
    exact product_coboundary v

end SymmetricSubgroupAsymptotics.CyclicCoordinateCoboundary
