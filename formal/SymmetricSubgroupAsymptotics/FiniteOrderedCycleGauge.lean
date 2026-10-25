import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-! Ordered cycle products construct literal gauges over any group.
Products are list products in the given cyclic order; coefficients are
never commuted. This is the general finite-cycle leaf for wreath codes. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteOrderedCycleGauge
variable {C : Type*} [Group C]

def product {n : ℕ} (f : Fin n → C) : C := (List.ofFn f).prod

theorem product_succ {n : ℕ} (f : Fin (n+1) → C) :
    product f = product (Fin.init f) * f (Fin.last n) := by
  simp only [product,List.ofFn_succ',List.prod_concat]
  rfl

theorem partialProd_last {n : ℕ} (f : Fin n → C) :
    Fin.partialProd f (Fin.last n) = product f := by
  have ht : (List.ofFn f).take n = List.ofFn f :=
    List.take_of_length_le (by simp)
  simp only [Fin.partialProd,Fin.val_last,ht,product]

theorem exists_gauge_of_product_isConj (n : ℕ) (f g : Fin n → C)
    (h : IsConj (product f) (product g)) :
    ∃ v : Fin n → C, ∀ i, g i = v i * f i * (v (finRotate n i))⁻¹ := by
  cases n with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n =>
    obtain ⟨u,hu⟩ := isConj_iff.mp h
    let v : Fin (n+1) → C := fun i =>
      (Fin.partialProd (Fin.init g) i)⁻¹ * u * Fin.partialProd (Fin.init f) i
    refine ⟨v,fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [finRotate_last]
      dsimp only [v]
      rw [Fin.partialProd_zero,Fin.partialProd_zero,
        partialProd_last,partialProd_last]
      simp only [inv_one,one_mul,mul_one]
      have hp : u * (product (Fin.init f) * f (Fin.last n)) * u⁻¹ =
          product (Fin.init g) * g (Fin.last n) := by
        simpa only [product_succ] using hu
      calc
        g (Fin.last n) = (product (Fin.init g))⁻¹ *
            (product (Fin.init g) * g (Fin.last n)) := by group
        _ = (product (Fin.init g))⁻¹ *
            (u * (product (Fin.init f) * f (Fin.last n)) * u⁻¹) := by rw [hp]
        _ = _ := by group
    · have hrot : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [hrot]
      dsimp only [v]
      rw [Fin.partialProd_succ,Fin.partialProd_succ]
      simp only [Fin.init]
      group

theorem product_finCongr {m n : ℕ} (h : m = n)
    (f : Fin m → C) (g : Fin n → C)
    (he : ∀ i, g (finCongr h i) = f i) : product g = product f := by
  subst n
  have hgf : g = f := funext he
  rw [hgf]

end SymmetricSubgroupAsymptotics.FiniteOrderedCycleGauge
