import SymmetricSubgroupAsymptotics.LinearMapMonicPrimaryDecomposition
import SymmetricSubgroupAsymptotics.LinearMapPositiveCyclicDecomposition

/-! Actual positive cyclic coordinates retain their actual monic
irreducible labels and positive exponents. Zero-power summands are
removed by an explicit quotient-product equivalence. Their weighted
degrees, and hence their exponent mass, are controlled by the original
operator dimension. No canonical-form uniqueness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators DirectSum

namespace SymmetricSubgroupAsymptotics.LinearMapPositivePrimaryDecomposition
open Polynomial
universe u v
variable {K : Type u} [Field K]

private def restrictPositive {ι : Type u} [Fintype ι]
    (p : ι → K[X]) (e : ι → ℕ) :
    ((i : ι) → K[X] ⧸ K[X] ∙ (p i)^(e i)) ≃ₗ[K[X]]
      ((i : {i : ι // 0 < e i}) → K[X] ⧸ K[X] ∙ (p i.val)^(e i.val)) where
  toFun x i := x i.val
  invFun x i := if h : 0 < e i then x ⟨i,h⟩ else 0
  left_inv x := by
    funext i
    by_cases hi : 0 < e i
    · simp only [dif_pos hi]
    · simp only [dif_neg hi]
      have he : e i = 0 := Nat.eq_zero_of_not_pos hi
      have ht : (K[X] ∙ (p i)^(e i)) = ⊤ := by simp [he]
      letI : Subsingleton (K[X] ⧸ K[X] ∙ (p i)^(e i)) :=
        Submodule.Quotient.subsingleton_iff.mpr ht
      exact Subsingleton.elim _ _
  right_inv x := by
    funext i
    simp only [dif_pos i.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V]

structure Chart (A : Module.End K V) where
  cyclic : LinearMapPositiveCyclicDecomposition.Chart A
  prime : cyclic.ι → K[X]
  irreducible : ∀ i, Irreducible (prime i)
  monic : ∀ i, (prime i).Monic
  exponent : cyclic.ι → ℕ
  positive : ∀ i, 0 < exponent i
  power_eq : ∀ i, cyclic.polynomial i = (prime i)^(exponent i)

theorem exists_chart (A : Module.End K V) : Nonempty (Chart A) := by
  letI : Module K[X] (Module.AEval' A) :=
    Module.AEval.instModulePolynomial (R := K) (M := V) A
  obtain ⟨ι,fι,p,hp,e,⟨E⟩⟩ :=
    LinearMapMonicPrimaryDecomposition.exists_monic_primePower_decomposition A
  letI : Fintype ι := fι
  let C : LinearMapPositiveCyclicDecomposition.Chart A := {
    ι := {i : ι // 0 < e i}
    polynomial i := (p i.val)^(e i.val)
    monic i := (hp i.val).2.pow (e i.val)
    positive i := by
      rw [Polynomial.natDegree_pow]
      exact Nat.mul_pos i.property
        (Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible (hp i.val).1))
    equiv := E.trans (DFinsupp.linearEquivFunOnFintype.trans (restrictPositive p e)) }
  exact ⟨⟨C,(fun i => p i.val),(fun i => (hp i.val).1),
    (fun i => (hp i.val).2),(fun i => e i.val),(fun i => i.property),(fun _ => rfl)⟩⟩

def chart (A : Module.End K V) : Chart A := Classical.choice (exists_chart A)

theorem Chart.degree_sum {A : Module.End K V} (C : Chart A) :
    (∑ i : C.cyclic.ι, C.exponent i * (C.prime i).natDegree) = Module.finrank K V := by
  calc
    _ = ∑ i : C.cyclic.ι, (C.cyclic.polynomial i).natDegree :=
      Finset.sum_congr rfl (fun i _ => by rw [C.power_eq,Polynomial.natDegree_pow])
    _ = _ := C.cyclic.degree_sum

theorem Chart.exponent_sum_le_dimension {A : Module.End K V} (C : Chart A) :
    (∑ i : C.cyclic.ι, C.exponent i) ≤ Module.finrank K V := by
  rw [← C.degree_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (C.exponent i)
    (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible (C.irreducible i))))

theorem Chart.mul_exponent_sum_le_dimension {A : Module.End K V} (C : Chart A)
    (d : ℕ) (hd : ∀ i, d ≤ (C.prime i).natDegree) :
    d * (∑ i : C.cyclic.ι, C.exponent i) ≤ Module.finrank K V := by
  rw [Finset.mul_sum,← C.degree_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (C.exponent i) (hd i))

end SymmetricSubgroupAsymptotics.LinearMapPositivePrimaryDecomposition
