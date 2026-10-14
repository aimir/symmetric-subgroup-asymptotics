import SymmetricSubgroupAsymptotics.BinaryPermutationSemidirectNormalGenerators

/-! One actual sign flip and a swapping base element generate the full
two-sign kernel. This is coordinate decomposition, without a group table. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPermutationSemidirectGeneration

open BinaryPermutationSemidirectNormalGenerators
open SemidirectProduct

def delta (i : Fin 2) : Multiplicative Vector :=
  Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))

theorem translation_decomposition (w : Multiplicative Vector) :
    delta 0 ^ (w.toAdd 0).val * delta 1 ^ (w.toAdd 1).val = w := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_pow, delta, toAdd_ofAdd]
  funext i
  change (w.toAdd 0).val • ((Pi.single (0 : Fin 2) (1 : ZMod 2) : Vector) i) +
    (w.toAdd 1).val • ((Pi.single (1 : Fin 2) (1 : ZMod 2) : Vector) i) = w.toAdd i
  fin_cases i <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem delta_action {R : Type} [Group R] (p : R →* Equiv.Perm (Fin 2))
    (g : R) (hg : p g 0 = 1) :
    LinearSemidirectCoprimeSocleBounds.linearAction (linearAction p) g (delta 0) = delta 1 := by
  apply Multiplicative.toAdd.injective
  letI : MulAction R (Fin 2) := MulAction.compHom (Fin 2) p
  change permutationFunctionRepresentation (ZMod 2) R (Fin 2) g (Pi.single 0 1) = Pi.single 1 1
  rw [permutationFunctionRepresentation_single]
  change (Pi.single (p g 0) 1 : Vector) = Pi.single 1 1
  rw [hg]

theorem mem_of_delta_and_base {R : Type} [Group R] (p : R →* Equiv.Perm (Fin 2))
    (g : R) (hg : p g 0 = 1) (D : Subgroup (Model p))
    (hdelta : (inl (delta 0) : Model p) ∈ D)
    (hbase : ∀ r : R, (inr r : Model p) ∈ D) (x : Model p) : x ∈ D := by
  have hdelta1 : (inl (delta 1) : Model p) ∈ D := by
    rw [← delta_action p g hg, inl_aut]
    exact D.mul_mem (D.mul_mem (hbase g) hdelta)
      (by simpa only [map_inv] using D.inv_mem (hbase g))
  have hleft (w : Multiplicative Vector) : (inl w : Model p) ∈ D := by
    rw [← translation_decomposition w, map_mul, map_pow, map_pow]
    exact D.mul_mem (D.pow_mem hdelta _) (D.pow_mem hdelta1 _)
  rw [← inl_left_mul_inr_right x]
  exact D.mul_mem (hleft x.left) (hbase x.right)

theorem image_mem_of_delta_and_base {R G : Type} [Group R] [Group G]
    (p : R →* Equiv.Perm (Fin 2)) (g : R) (hg : p g 0 = 1)
    (f : Model p →* G) (D : Subgroup G)
    (hdelta : f (inl (delta 0)) ∈ D)
    (hbase : ∀ r : R, f (inr r) ∈ D) (x : Model p) : f x ∈ D :=
  mem_of_delta_and_base p g hg (D.comap f) hdelta hbase x

end BinaryPermutationSemidirectGeneration
end SymmetricSubgroupAsymptotics

end
