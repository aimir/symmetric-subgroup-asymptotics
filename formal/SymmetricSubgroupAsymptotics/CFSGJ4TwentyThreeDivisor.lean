import SymmetricSubgroupAsymptotics.CFSGJ4Generation
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A literal order23 witness in the pinned three-generator J4 presentation.
The first two generators have orders dividing2 and3. Their product cannot
be trivial in a noncommutative model: otherwise both are trivial and the
remaining single generator makes the whole presentation cyclic. Thus the
actual product has order23, excluding faithful actions and actual simple
socle factors on fewer than23 points. No known model order or action list
is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGJ4TwentyThreeDivisor
open CFSGGeneration PrimitiveSocleRawStructure CFSGReduction

theorem j4y_cube : j4y ^ 3 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ CFSG.Models.Presentations.J4.relators})
    (x := (FreeGroup.of (1 : Fin 3)) ^ 3)
    (by change _ ∈ CFSG.Models.Presentations.J4.relators
        exact List.mem_cons_of_mem _ List.mem_cons_self)
  simpa only [map_pow, PresentedGroup.of] using h

theorem product_ne_one
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J4.Model) :
    j4x * j4y ≠ 1 := by
  intro hxy
  have hyx : j4y = j4x⁻¹ := by
    calc j4y = j4x⁻¹ * (j4x * j4y) := (inv_mul_cancel_left _ _).symm
         _ = j4x⁻¹ := by rw [hxy,mul_one]
  have hy2 : j4y ^ 2 = 1 := by rw [hyx,inv_pow,j4x_sq,inv_one]
  have hy : j4y = 1 := by
    calc j4y = j4y ^ 2 * j4y := by rw [hy2,one_mul]
         _ = j4y ^ 3 := (pow_succ j4y 2).symm
         _ = 1 := j4y_cube
  have hx : j4x = 1 := by simpa only [hy,mul_one] using hxy
  have htop : Subgroup.zpowers j4t = ⊤ := by
    apply top_unique
    intro g _
    exact PresentedGroup.generated_by _ (Subgroup.zpowers j4t) (fun i => by
      fin_cases i
      · change j4x ∈ _
        rw [hx]
        exact Subgroup.one_mem _
      · change j4y ∈ _
        rw [hy]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _) g
  letI : IsCyclic CFSG.Models.Presentations.J4.Model :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨j4t,htop⟩
  exact hn inferInstance

theorem twenty_three_dvd_order
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J4.Model) :
    23 ∣ Nat.card CFSG.Models.Presentations.J4.Model := by
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  have ho : orderOf (j4x*j4y) = 23 :=
    orderOf_eq_prime j4xy_pow_twenty_three (product_ne_one hn)
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem degree_twenty_three_le_of_injective
    {X : Type} [Finite X]
    (f : CFSG.Models.Presentations.J4.Model →* Equiv.Perm X)
    (hf : Function.Injective f)
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J4.Model) :
    23 ≤ Nat.card X := by
  letI : Finite CFSG.Models.Presentations.J4.Model := Finite.of_injective f hf
  have hd : Nat.card CFSG.Models.Presentations.J4.Model ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective f hf
  by_contra hsmall
  have h23 : 23 ∣ Nat.factorial 22 :=
    (twenty_three_dvd_order hn).trans (hd.trans (Nat.factorial_dvd_factorial (by omega)))
  exact (by decide : ¬ 23 ∣ Nat.factorial 22) h23

theorem not_j4_of_degree_le_twentyTwo
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hn : Nat.card X ≤ 22)
    (e : D.Simple ≃* CFSG.Models.Presentations.J4.Model) : False := by
  have hnc : ¬ IsMulCommutative CFSG.Models.Presentations.J4.Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  have h23 : 23 ∣ Nat.factorial 22 :=
    (twenty_three_dvd_order hnc).trans (hd.trans (Nat.factorial_dvd_factorial hn))
  exact (by decide : ¬ 23 ∣ Nat.factorial 22) h23

end SymmetricSubgroupAsymptotics.CFSGJ4TwentyThreeDivisor
