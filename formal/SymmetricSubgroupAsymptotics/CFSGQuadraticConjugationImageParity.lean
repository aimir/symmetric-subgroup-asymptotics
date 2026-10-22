import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootFixed
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! A selected actual root/Weyl action proves parity for the same action
range modulo its centre. It does not require any statement about other
roots or any recognition/faithfulness assertion for the source group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticConjugationImageParity
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (K : Type) [Field K] {G : Type*} [Group G]
    (f : G→*((baseChange D K).range≃ₗ[K](baseChange D K).range))
    (u v : G) (i : Fin n)
    (hu : ∀y : (baseChange D K).range,(f u y).val=
      (canonicalWeyl D K i : Matrix I I K)*y.val*(↑((canonicalWeyl D K i)⁻¹):Matrix I I K))
    (hv : ∀y : (baseChange D K).range,(f v y).val=
      (canonicalRoot D K false i 1 : Matrix I I K)*y.val*
        (↑((canonicalRoot D K false i 1)⁻¹):Matrix I I K))
    (hfour : (canonicalWeyl D K i)^4=1)
    (hne : (canonicalRoot D K false i 1 : Matrix I I K)*
      ((canonicalWeyl D K i : Matrix I I K)*fieldRoot D K false i*
        (↑((canonicalWeyl D K i)⁻¹):Matrix I I K))*
      (↑((canonicalRoot D K false i 1)⁻¹):Matrix I I K)≠
      (canonicalWeyl D K i : Matrix I I K)*fieldRoot D K false i*
        (↑((canonicalWeyl D K i)⁻¹):Matrix I I K))
include hu hv hfour hne

private theorem action_power (k : ℕ) (y : (baseChange D K).range) :
    (((f u)^k) y).val=CFSGAlgebraConjugationAction.action K (Matrix I I K)
      ((canonicalWeyl D K i)^k) y.val := by
  induction k with
  | zero=>simp only [pow_zero,map_one];rfl
  | succ k ih=>
    rw [pow_succ',LinearEquiv.mul_apply,hu,ih]
    rw [pow_succ',map_mul,LinearEquiv.mul_apply]
    rfl

theorem image_word_four : (f.rangeRestrict u)^4=1 := by
  apply Subtype.ext
  change (f u)^4=1
  apply LinearEquiv.ext
  intro y
  apply Subtype.ext
  have hh := action_power D K f u v i hu hv hfour hne 4 y
  simpa only [hfour,map_one] using hh

theorem image_word_not_center : f.rangeRestrict u∉Subgroup.center f.range := by
  intro hc
  let y : (baseChange D K).range := (baseChange D K).rangeRestrict
    (1⊗ₜ[ℤ]CFSGSerreDiagram.latticeGenerator A (CartanMatrix.Generators.E i))
  have hy : y.val=fieldRoot D K false i := by
    change baseChange D K (1⊗ₜ[ℤ]CFSGSerreDiagram.latticeGenerator A (CartanMatrix.Generators.E i))=_
    rw [baseChange_generator]
    rfl
  have hfix : f v y=y := by
    apply Subtype.ext
    rw [hv,hy]
    exact canonicalRoot_fixes_root D K false i 1
  have hcomm := (Subgroup.mem_center_iff.mp hc) (f.rangeRestrict v)
  have hh := congrArg Subtype.val hcomm
  change f v*f u=f u*f v at hh
  have he := DFunLike.congr_fun hh y
  change f v (f u y)=f u (f v y) at he
  rw [hfix] at he
  have hh' := congrArg Subtype.val he
  rw [hv,hu,hy] at hh'
  exact hne hh'

theorem image_projective_even_card : Even (Nat.card (f.range⧸Subgroup.center f.range)) := by
  let q := QuotientGroup.mk' (Subgroup.center f.range)
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root (q (f.rangeRestrict u))
  · intro h
    exact image_word_not_center D K f u v i hu hv hfour hne ((QuotientGroup.eq_one_iff _).mp h)
  · exact (map_pow q (f.rangeRestrict u) 4).symm.trans
      ((congrArg q (image_word_four D K f u v i hu hv hfour hne)).trans (map_one q))

end SymmetricSubgroupAsymptotics.CFSGQuadraticConjugationImageParity
