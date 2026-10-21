import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPrimitiveRootSaturation
import SymmetricSubgroupAsymptotics.CFSGTwoRootExtraction
import SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldScalars
import Lean.Elab.Tactic.Omega

/-! Primitive scalar filtering for the nonbinary D candidate. Unlike
the C long-root filter, the retained parameter scales by g itself; the
only exclusion is q=2. This includes the three-element field uniformly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationScalarFilter
open CFSGOrthogonalDGenerationPrimitiveRootSaturation
variable {K G : Type*} [Field K] [Finite K] [Group G]

theorem primitive_ne_one (hcard : 3 ≤ Nat.card K) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g) : (g : K) ≠ 1 := by
  intro h
  have hu : g ^ 1 = 1 := by simpa only [pow_one] using (Units.ext h : g = 1)
  have hd := orderOf_dvd_of_pow_eq_one hu
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units] at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 1) hd
  omega

theorem second_line_of_pair
    (hcard : 3 ≤ Nat.card K) (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (A B : K → G)
    (hA : ∀ a b, A (a + b) = A a * A b) (hA0 : A 0 = 1)
    (hB : ∀ a b, B (a + b) = B a * B b) (hB0 : B 0 = 1)
    (hAB : ∀ a b, Commute (A a) (B b)) (T W : G) (l : K)
    (hScaleA : ∀ a, T * A a * T⁻¹ = A a)
    (hScaleB : ∀ b, T * B b * T⁻¹ = B ((g : K) * b))
    (hScaleA' : ∀ a, (W * T * W⁻¹) * A a * (W * T * W⁻¹)⁻¹ = A (l * a))
    (hScaleB' : ∀ b, (W * T * W⁻¹) * B b * (W * T * W⁻¹)⁻¹ = B ((g : K) * b))
    (hComm : Commute (W * T * W⁻¹) T)
    (H : Subgroup G) (hT : T ∈ H) (hy : A 1 * B 1 * W ∈ H) : ∀ a, B a ∈ H := by
  have hm : (1 - (g : K)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (primitive_ne_one hcard g hg)))
  have hp := CFSGTwoRootExtraction.pure_second_root_mem A B hA hA0 hB hB0 hAB
    T W (g : K) l hScaleA hScaleB hScaleA' hScaleB' hComm H hT hy
  exact all_parameters_of_primitive_scaling B hB0 hB H T hT g hg hScaleB _ hm hp

theorem cleaned_word_mem (A B : K → G) (hAB : Commute (A 1) (B 1))
    (W : G) (H : Subgroup G) (hB : B 1 ∈ H) (hy : A 1 * B 1 * W ∈ H) : A 1 * W ∈ H := by
  have hp := H.mul_mem (H.inv_mem hB) hy
  have he : (B 1)⁻¹ * (A 1 * B 1 * W) = A 1 * W := by
    rw [hAB.eq]
    group
  rw [he] at hp
  exact hp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationScalarFilter
