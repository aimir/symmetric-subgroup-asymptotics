import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import Mathlib.Data.Finset.Lattice.Fold

/-! A fixed actual finite simple type pays primitive class cubes eventually,
without any model class/order table. All subgroup sources are retained;
subnormality is unnecessary for this order envelope. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassTail
open PrimitiveSocleRawStructure CFSGReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem order_le_degree_log_square (D : NonaffineData G X)
    (hsize : Nat.card D.Simple*Nat.card (Outer D.Simple)≤Nat.card X)
    (hn : 2≤Nat.card X) :
    Nat.card G≤(Nat.card X)^(4*Nat.log 2 (Nat.card X)+2) := by
  have hk := FiniteModelPrimitiveOrdinaryBudget.factorCount_le_log D
  have hkn : D.factorCount≤Nat.card X := hk.trans (Nat.log_le_self 2 _)
  have hfac : D.factorCount.factorial≤(Nat.card X)^D.factorCount :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hkn _)
  calc
    Nat.card G≤(Nat.card D.Simple*Nat.card (Outer D.Simple))^D.factorCount*
        D.factorCount.factorial := D.card_le_simple_outer_wreath
    _≤(Nat.card X)^D.factorCount*(Nat.card X)^D.factorCount :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hsize _) hfac
    _=(Nat.card X)^(2*D.factorCount) := by rw [←pow_add]; congr 1; omega
    _≤(Nat.card X)^(4*Nat.log 2 (Nat.card X)+2) :=
      Nat.pow_le_pow_right (by omega) (by omega)

def PaysModel (M : Type) [Group M] (N : ℕ) : Prop :=
  ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X), (D.Simple ≃* M) → N≤Nat.card X →
      ∀ H : Subgroup G,Nat.card (ConjClasses H)^3≤5^(Nat.card X-1)

theorem pays_of_finite (M : Type) [Group M] [Finite M] :
    PaysModel M (max 1024 (Nat.card M*Nat.card (Outer M))) := by
  intro G X _ _ _ _ D e hn H
  apply LogSquareOrderSubgroupClassBound.subgroup_class_cube_le _
    ((le_max_left _ _).trans hn) _ H
  apply order_le_degree_log_square D
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact (le_max_right _ _).trans hn
  · omega

theorem exists_threshold (M : Type) [Group M] : ∃ N,PaysModel M N := by
  by_cases h : Finite M
  · letI := h
    exact ⟨_,pays_of_finite M⟩
  · refine ⟨0,?_⟩
    intro G X _ _ _ _ D e hn H
    exact (h (Finite.of_equiv D.Simple e.toEquiv)).elim

theorem pays_mono {M : Type} [Group M] {N N' : ℕ}
    (h : PaysModel M N) (hNN : N≤N') : PaysModel M N' := by
  intro G X _ _ _ _ D e hn H
  exact h D e (hNN.trans hn) H

theorem finite_family_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] : ∃ N,∀ i,PaysModel (M i) N := by
  letI := Fintype.ofFinite ι
  choose N hN using fun i => exists_threshold (M i)
  refine ⟨Finset.univ.sup N,?_⟩
  intro i
  exact pays_mono (hN i) (Finset.le_sup (Finset.mem_univ i))

end SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassTail
