import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalEndFields
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMixedA2
import SymmetricSubgroupAsymptotics.CFSGA2SemilinearRigidity

/-! The same field map and reciprocal scalar act on both signs of each
native F4 end A2. This is a theorem about the actual label-fixing
subgroup, not a claim that arbitrary F4 automorphisms preserve lengths. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedEndFields
open CFSGFFourE6OriginalEndFields CFSGFFourE6OriginalA2 CFSGFFourE6OriginalMixedA2
open CFSGFFourE6OriginalSimpleParameters CFSGA2SemilinearRigidity CFSG.Models.Chevalley

private theorem parameter_image {K G : Type*} [Field K] [Group G]
    (n : Multiplicative K→*G) (f : G→*G) (hf : n.range.map f=n.range) (a : K) :
    ∃b : K,f (n (Multiplicative.ofAdd a))=n (Multiplicative.ofAdd b) := by
  have hm : f (n (Multiplicative.ofAdd a))∈n.range := by
    rw [←hf]
    exact ⟨_,⟨Multiplicative.ofAdd a,rfl⟩,rfl⟩
  obtain ⟨b,hb⟩ := hm
  exact ⟨b.toAdd,hb.symm⟩

private theorem negative_of_positive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K)) (i j : Fin 4)
    (hp : ∀a b : K,⁅originalSimpleHom K false i (Multiplicative.ofAdd a),
      originalSimpleHom K false j (Multiplicative.ofAdd b)⁆=sumOriginalHom K i j (Multiplicative.ofAdd (a*b)))
    (hm : ∀a b : K,⁅originalSimpleHom K true i (Multiplicative.ofAdd a),
      sumOriginalHom K i j (Multiplicative.ofAdd b)⁆=originalSimpleHom K false j (Multiplicative.ofAdd (a*b)))
    (hneg : (originalSimpleHom K true i).range.map f.toMonoidHom=(originalSimpleHom K true i).range)
    (tau : RingAut K) (c d : K) (hc : c≠0) (hd : d≠0)
    (hi : ∀a,f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      originalSimpleHom K false i (Multiplicative.ofAdd (c*tau a)))
    (hj : ∀a,f (originalSimpleHom K false j (Multiplicative.ofAdd a))=
      originalSimpleHom K false j (Multiplicative.ofAdd (d*tau a))) (a : K) :
    f (originalSimpleHom K true i (Multiplicative.ofAdd a))=
      originalSimpleHom K true i (Multiplicative.ofAdd (c⁻¹*tau a)) := by
  let u (t : K) := originalSimpleHom K false i (Multiplicative.ofAdd t)
  let v (t : K) := originalSimpleHom K false j (Multiplicative.ofAdd t)
  let n (t : K) := originalSimpleHom K true i (Multiplicative.ofAdd t)
  let w (t : K) := sumOriginalHom K i j (Multiplicative.ofAdd t)
  have hw : ∀b,f (w b)=w ((c*d)*tau b) :=
    third_parameter_semilinear u v w hp f.toMonoidHom tau c d hi hj
  exact opposite_parameter_semilinear v n w
    ((originalSimpleHom_injective K p false j).comp Multiplicative.ofAdd.injective)
    hm f.toMonoidHom tau c d hc hd hj hw
    (parameter_image (originalSimpleHom K true i) f.toMonoidHom hneg) a

theorem paired_signed_parameters_common_field (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hfix : ∀neg i,(originalSimpleHom K neg i).range.map f.toMonoidHom=(originalSimpleHom K neg i).range) :
    ∃(tau : RingAut K) (c d : K),c≠0 ∧ d≠0 ∧ ∀a,
      f (originalSimpleHom K false 0 (Multiplicative.ofAdd a))=originalSimpleHom K false 0 (Multiplicative.ofAdd (c*tau a)) ∧
      f (originalSimpleHom K false 1 (Multiplicative.ofAdd a))=originalSimpleHom K false 1 (Multiplicative.ofAdd (d*tau a)) ∧
      f (originalSimpleHom K true 0 (Multiplicative.ofAdd a))=originalSimpleHom K true 0 (Multiplicative.ofAdd (c⁻¹*tau a)) ∧
      f (originalSimpleHom K true 1 (Multiplicative.ofAdd a))=originalSimpleHom K true 1 (Multiplicative.ofAdd (d⁻¹*tau a)) := by
  obtain ⟨tau,c,d,hc,hd,hp⟩ := paired_parameters_common_field K p f (hfix false)
  refine ⟨tau,c,d,hc,hd,fun a=>⟨(hp a).1,(hp a).2,?_,?_⟩⟩
  · exact negative_of_positive K p f 0 1 (original_paired_commutator K 0 1 (by decide))
      (original_paired_mixed_commutator K 0 1 (by decide)) (hfix true 0) tau c d hc hd
      (fun t=>(hp t).1) (fun t=>(hp t).2) a
  · exact negative_of_positive K p f 1 0 (original_paired_commutator K 1 0 (by decide))
      (original_paired_mixed_commutator K 1 0 (by decide)) (hfix true 1) tau d c hd hc
      (fun t=>(hp t).2) (fun t=>(hp t).1) a

theorem singleton_signed_parameters_common_field (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hfix : ∀neg i,(originalSimpleHom K neg i).range.map f.toMonoidHom=(originalSimpleHom K neg i).range) :
    ∃(tau : RingAut K) (c d : K),c≠0 ∧ d≠0 ∧ ∀a,
      f (originalSimpleHom K false 2 (Multiplicative.ofAdd a))=originalSimpleHom K false 2 (Multiplicative.ofAdd (c*tau a)) ∧
      f (originalSimpleHom K false 3 (Multiplicative.ofAdd a))=originalSimpleHom K false 3 (Multiplicative.ofAdd (d*tau a)) ∧
      f (originalSimpleHom K true 2 (Multiplicative.ofAdd a))=originalSimpleHom K true 2 (Multiplicative.ofAdd (c⁻¹*tau a)) ∧
      f (originalSimpleHom K true 3 (Multiplicative.ofAdd a))=originalSimpleHom K true 3 (Multiplicative.ofAdd (d⁻¹*tau a)) := by
  obtain ⟨tau,c,d,hc,hd,hp⟩ := singleton_parameters_common_field K p f (hfix false)
  refine ⟨tau,c,d,hc,hd,fun a=>⟨(hp a).1,(hp a).2,?_,?_⟩⟩
  · exact negative_of_positive K p f 2 3 (original_singleton_commutator K 1 0 (by decide))
      (original_singleton_mixed_commutator K 1 0 (by decide)) (hfix true 2) tau c d hc hd
      (fun t=>(hp t).1) (fun t=>(hp t).2) a
  · exact negative_of_positive K p f 3 2 (original_singleton_commutator K 0 1 (by decide))
      (original_singleton_mixed_commutator K 0 1 (by decide)) (hfix true 3) tau d c hd hc
      (fun t=>(hp t).2) (fun t=>(hp t).1) a

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedEndFields
