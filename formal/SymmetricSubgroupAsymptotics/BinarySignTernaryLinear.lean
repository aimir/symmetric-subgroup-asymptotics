import SymmetricSubgroupAsymptotics.CyclicOrbitBinarySignNormalGenerators
import SymmetricSubgroupAsymptotics.AffineIrreducibleQuotientSocles
import SymmetricSubgroupAsymptotics.TernaryFourScalarDiagonalQuotient

/-! The actual ternary monomial representation of a binary sign module.
Two overlapping even sign flips isolate one coordinate. A cyclic point
orbit then proves irreducibility without enumerating vectors or subspaces. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinarySignTernaryLinear

open SemidirectProduct

variable {R : Type} [Group R] [MulAction R (Fin 4)]
variable (E : Subrepresentation
  (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)))

abbrev SignModel := CyclicOrbitBinarySignNormalGenerators.Model E
abbrev Vector := Fin 4 → ZMod 3
abbrev BinaryVector := Fin 4 → ZMod 2

def coefficient (z : ZMod 2) : ZMod 3 :=
  (TernaryFourScalarDiagonalQuotient.bitScalar (Multiplicative.ofAdd z) : ZMod 3)

theorem coefficient_zero : coefficient 0 = 1 := rfl

theorem coefficient_add (x y : ZMod 2) : coefficient (x+y) = coefficient x * coefficient y := by
  exact congrArg (fun z : (ZMod 3)ˣ => (z : ZMod 3))
    (TernaryFourScalarDiagonalQuotient.bitScalar.map_mul
      (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

def representation : Representation (ZMod 3) (SignModel E) Vector where
  toFun g :=
    { toFun v i := coefficient (g.left.toAdd.1 i) * v (g.right⁻¹ • i)
      map_add' := by intro v w; funext i; exact mul_add _ _ _
      map_smul' := by
        intro a v
        funext i
        change coefficient (g.left.toAdd.1 i) * (a * v (g.right⁻¹ • i)) =
          a * (coefficient (g.left.toAdd.1 i) * v (g.right⁻¹ • i))
        ring }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change coefficient 0 * v ((1 : R)⁻¹ • i) = v i
    simp only [coefficient_zero,inv_one,one_smul,one_mul]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    change coefficient (g.left.toAdd.1 i + h.left.toAdd.1 (g.right⁻¹ • i)) *
      v ((g.right*h.right)⁻¹ • i) =
      coefficient (g.left.toAdd.1 i) *
        (coefficient (h.left.toAdd.1 (g.right⁻¹ • i)) * v (h.right⁻¹ • (g.right⁻¹ • i)))
    rw [coefficient_add,mul_inv_rev,mul_smul,mul_assoc]

def linearHom : SignModel E →* AffineModel.GLV 3 4 where
  toFun g :=
    { toFun := representation E g
      invFun := representation E g⁻¹
      left_inv := by
        intro v
        change (representation E g⁻¹ * representation E g) v = v
        rw [← map_mul,inv_mul_cancel,map_one]
        rfl
      right_inv := by
        intro v
        change (representation E g * representation E g⁻¹) v = v
        rw [← map_mul,mul_inv_cancel,map_one]
        rfl
      map_add' := (representation E g).map_add
      map_smul' := (representation E g).map_smul }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun (representation E).map_one v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun ((representation E).map_mul g h) v

theorem linearHom_inl (z : E.toSubmodule) (v : Vector) :
    linearHom E (inl (Multiplicative.ofAdd z)) v = fun i => coefficient (z.1 i) * v i := by
  funext i
  change coefficient (z.1 i) * v ((1 : R)⁻¹ • i) = _
  rw [inv_one,one_smul]

theorem linearHom_inr (r : R) (v : Vector) :
    linearHom E (inr r) v = fun i => v (r⁻¹ • i) := by
  funext i
  change coefficient 0 * v (r⁻¹ • i) = _
  rw [coefficient_zero,one_mul]

theorem linearHom_injective [FaithfulSMul R (Fin 4)] : Function.Injective (linearHom E) := by
  intro g h he
  have hlabels : Function.Injective (fun z : ZMod 2 × Fin 4 =>
      fun j : Fin 4 => coefficient z.1 * (Pi.single j 1 : Vector) z.2) := by
    decide +kernel
  have hp (i : Fin 4) : (g.left.toAdd.1 i,g.right⁻¹ • i) =
      (h.left.toAdd.1 i,h.right⁻¹ • i) := by
    apply hlabels
    funext j
    exact congrArg (fun f : AffineModel.GLV 3 4 => f (Pi.single j 1) i) he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact congrArg Prod.fst (hp i)
  · apply inv_injective
    exact eq_of_smul_eq_smul (fun i => congrArg Prod.snd (hp i))

def pair (i j : Fin 4) : BinaryVector := Pi.single i 1 + Pi.single j 1

theorem isolate_zero
    (h01 : pair 0 1 ∈ E.toSubmodule) (h02 : pair 0 2 ∈ E.toSubmodule) (v : Vector) :
    linearHom E (inl (Multiplicative.ofAdd ⟨pair 0 2,h02⟩))
        (linearHom E (inl (Multiplicative.ofAdd ⟨pair 0 1,h01⟩)) v-v) -
      (linearHom E (inl (Multiplicative.ofAdd ⟨pair 0 1,h01⟩)) v-v) =
        Pi.single 0 (v 0) := by
  rw [linearHom_inl,linearHom_inl]
  funext i
  have hc01 (j : Fin 4) : coefficient (pair 0 1 j) = ![-1,-1,1,1] j := by
    fin_cases j <;> decide +kernel
  have hc02 (j : Fin 4) : coefficient (pair 0 2 j) = ![-1,1,-1,1] j := by
    fin_cases j <;> decide +kernel
  change coefficient (pair 0 2 i) * (coefficient (pair 0 1 i) * v i-v i) -
    (coefficient (pair 0 1 i) * v i-v i) = (Pi.single 0 (v 0) : Vector) i
  rw [hc01,hc02]
  fin_cases i <;> norm_num [Pi.single_apply] <;> ring_nf <;> norm_num
  simp only [show (4 : ZMod 3) = 1 by decide +kernel, mul_one]

theorem single_inr (r : R) (i : Fin 4) (a : ZMod 3) :
    linearHom E (inr r) (Pi.single i a) = Pi.single (r • i) a := by
  rw [linearHom_inr]
  funext j
  by_cases hj : j = r • i
  · subst j
    rw [← mul_smul,inv_mul_cancel,one_smul]
    simp only [Pi.single_eq_same]
  · have hn : r⁻¹ • j ≠ i := by
      intro hi
      apply hj
      calc
        j = r • (r⁻¹ • j) := (smul_inv_smul r j).symm
        _ = r • i := congrArg (fun z => r • z) hi
    simp only [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hn]

theorem irreducible (c : R) (hcycle : ∀ i : Fin 4, ∃ n : ℕ, c^n • 0 = i)
    (h01 : pair 0 1 ∈ E.toSubmodule) (h02 : pair 0 2 ∈ E.toSubmodule) :
    AffineModel.Irreducible (linearHom E).range := by
  intro S hS
  by_cases hb : S = ⊥
  · exact Or.inl hb
  right
  have hex : ∃ v ∈ S, v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hb
    apply bot_unique
    intro v hv
    exact AddSubgroup.mem_bot.mpr (hn v hv)
  obtain ⟨v,hv,hv0⟩ := hex
  have hi : ∃ i : Fin 4, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv0 (funext hn)
  obtain ⟨i,hi⟩ := hi
  obtain ⟨n,hn⟩ := hcycle i
  let w := linearHom E (inr ((c^n)⁻¹)) v
  have hw : w ∈ S := hS _ ⟨inr ((c^n)⁻¹),rfl⟩ v hv
  have hw0 : w 0 ≠ 0 := by
    change (linearHom E (inr ((c^n)⁻¹)) v) 0 ≠ 0
    rw [linearHom_inr]
    simpa only [inv_inv,hn] using hi
  have hp : (Pi.single 0 (w 0) : Vector) ∈ S := by
    rw [← isolate_zero E h01 h02 w]
    have hfirst := S.sub_mem (hS _ ⟨inl (Multiplicative.ofAdd ⟨pair 0 1,h01⟩),rfl⟩ w hw) hw
    exact S.sub_mem (hS _ ⟨inl (Multiplicative.ofAdd ⟨pair 0 2,h02⟩),rfl⟩ _ hfirst) hfirst
  have hzero : (Pi.single 0 1 : Vector) ∈ S := by
    have hs := S.nsmul_mem hp ((w 0)⁻¹).val
    have he : ((w 0)⁻¹).val • (Pi.single 0 (w 0) : Vector) = Pi.single 0 1 := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp only [Pi.smul_apply,Pi.single_eq_same,nsmul_eq_mul,ZMod.natCast_zmod_val]
        exact inv_mul_cancel₀ hw0
      · simp only [Pi.smul_apply,Pi.single_eq_of_ne hj,nsmul_zero]
    rwa [he] at hs
  have hsingle (j : Fin 4) : (Pi.single j 1 : Vector) ∈ S := by
    obtain ⟨m,hm⟩ := hcycle j
    have hs := hS _ ⟨inr (c^m),rfl⟩ (Pi.single 0 1) hzero
    rwa [single_inr,hm] at hs
  apply top_unique
  intro x _
  have he : (∑ j : Fin 4, (x j).val • (Pi.single j 1 : Vector)) = x := by
    have hscalar (j : Fin 4) :
        (x j).val • (Pi.single j 1 : Vector) = (x j : ZMod 3) • Pi.single j 1 := by
      funext k
      simp only [Pi.smul_apply,nsmul_eq_mul,ZMod.natCast_zmod_val,smul_eq_mul]
    simp_rw [hscalar]
    funext i
    simp [Pi.single_apply]
  rw [← he]
  exact S.sum_mem fun j _ => S.nsmul_mem (hsingle j) _

end SymmetricSubgroupAsymptotics.BinarySignTernaryLinear

end
