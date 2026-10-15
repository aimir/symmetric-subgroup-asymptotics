import SymmetricSubgroupAsymptotics.BinarySignTernaryAffineSocles
import SymmetricSubgroupAsymptotics.NaturalBinaryAlternatingCyclic

/-! Signed ternary affine bounds from a supplied uniform binary-module
bound. The irreducible branch needs only point transitivity, while the
coprime branch also covers reducible ternary monomial modules. The sign
space, complement, and surjective quotient map remain the actual ones. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.UniformBinarySignTernarySocles

open SemidirectProduct BinarySignTernaryLinear

variable {R : Type} [Group R] [MulAction R (Fin 4)]
  (E : Subrepresentation
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)))

theorem uniform_sign (u : ℕ)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u) :
    UniformSubrepresentationGeneratorBound
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation
        (CyclicOrbitBinarySignNormalGenerators.linearAction E)) u := by
  let inclusion : E.toRepresentation.IntertwiningMap
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) :=
    { toLinearMap := E.toSubmodule.subtype
      isIntertwining' _ := rfl }
  change UniformSubrepresentationGeneratorBound E.toRepresentation u
  exact hu.of_injective inclusion (fun _ _ he => Subtype.ext he)

theorem normalGen_sign [Finite R] (u a : ℕ)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (SignModel E)) [N.Normal] : MarkedC4.normalGen N ≤ u+a :=
  LinearSemidirectUniformNormalGenerators.normalGen_le
    (CyclicOrbitBinarySignNormalGenerators.linearAction E) u a (uniform_sign E u hu) ha N

theorem sign_quotientSocle [Finite R] (u a : ℕ)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (SignModel E)) [N.Normal] : SocleNormalGeneratorBound (SignModel E ⧸ N) (u+a) := by
  apply quotientSocleNormalGeneratorBound_of_normal_generating_tuples ?_ N
  intro K hK
  letI := hK
  exact exists_normal_generating_tuple_of_normalGen_le K (normalGen_sign E u a hu ha K)

theorem irreducible_transitive
    (htrans : ∀ i : Fin 4, ∃ r : R, r • 0 = i)
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
  obtain ⟨r,hr⟩ := htrans i
  let w := linearHom E (inr r⁻¹) v
  have hw : w ∈ S := hS _ ⟨inr r⁻¹,rfl⟩ v hv
  have hw0 : w 0 ≠ 0 := by
    change (linearHom E (inr r⁻¹) v) 0 ≠ 0
    rw [linearHom_inr]
    simpa only [inv_inv,hr] using hi
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
    obtain ⟨g,hg⟩ := htrans j
    have hs := hS _ ⟨inr g,rfl⟩ (Pi.single 0 1) hzero
    rwa [single_inr,hg] at hs
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

theorem socle_of_irreducible [Finite R] [FaithfulSMul R (Fin 4)]
    (hirr : AffineModel.Irreducible (linearHom E).range)
    (u a : ℕ) (hpos : 1 ≤ u+a)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    {Q : Type} [Group Q] (pi : BinarySignTernaryAffineSocles.Model E →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q (u+a) := by
  apply AffineModel.socle_of_surjective_of_irreducible_complement_quotients
    (linearHom E).range hirr (Pi.single 0 1) (by decide +kernel) hpos _
    (pi.comp (BinarySignTernaryAffineSocles.affineEquiv E).symm.toMonoidHom)
    (hpi.comp (BinarySignTernaryAffineSocles.affineEquiv E).symm.surjective)
  intro N hN
  letI := hN
  let q := (QuotientGroup.mk' N).comp
    (BinarySignTernaryAffineSocles.complementEquiv E).toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective N).comp
    (BinarySignTernaryAffineSocles.complementEquiv E).surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective q hq) (sign_quotientSocle E u a hu ha q.ker)

theorem socle_of_coprime [Finite R]
    (hcop : Nat.Coprime 3 (Nat.card (SignModel E)))
    (t u a : ℕ)
    (hgen : RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearHom E)) t)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    {Q : Type} [Group Q] (pi : BinarySignTernaryAffineSocles.Model E →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q (max t (u+a)) := by
  apply LinearSemidirectCoprimeQuotientSocles.socle_of_surjective
    (linearHom E) hcop t (u+a) hgen ?_ pi hpi
  intro K hK
  letI := hK
  exact normalGen_sign E u a hu ha K

theorem alternating_uniform : UniformSubrepresentationGeneratorBound
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation
      (R := alternatingGroup (Fin 4)) (X := Fin 4)) 1 :=
  NaturalBinaryAlternating.uniform_one (alternatingGroup (Fin 4)) le_rfl
    (by simp) (by simpa using (show Even (4 : ℕ) from ⟨2,rfl⟩))

end SymmetricSubgroupAsymptotics.UniformBinarySignTernarySocles

end
