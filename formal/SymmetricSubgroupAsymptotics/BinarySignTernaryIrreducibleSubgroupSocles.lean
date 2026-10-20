import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup
import SymmetricSubgroupAsymptotics.BinarySignTernarySubgroupSocles
import SymmetricSubgroupAsymptotics.UniformBinarySignTernarySocles

/-! A transitive actual sign image containing two overlapping even sign
flips acts irreducibly on the ternary coordinates. Block lifts may carry
signs. This removes the coprimality requirement from the corresponding
arbitrary affine-subgroup bound while retaining both actual images and
the original quotient map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinarySignTernaryIrreducibleSubgroupSocles

open SemidirectProduct BinarySignTernaryLinear
open BinarySignTernarySubgroupSocles

variable {R : Type} [Group R] [MulAction R (Fin 4)]
  (E : Subrepresentation
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)))

theorem single_normalize (S : AddSubgroup Vector) {i : Fin 4} {a : ZMod 3}
    (ha : a ≠ 0) (h : (Pi.single i a : Vector) ∈ S) :
    (Pi.single i 1 : Vector) ∈ S := by
  have hs := S.nsmul_mem h (a⁻¹).val
  have he : (a⁻¹).val • (Pi.single i a : Vector) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.smul_apply,Pi.single_eq_same,nsmul_eq_mul,ZMod.natCast_zmod_val]
      exact inv_mul_cancel₀ ha
    · simp only [Pi.smul_apply,Pi.single_eq_of_ne hj,nsmul_zero]
  rwa [he] at hs

theorem irreducible (S : Subgroup (SignModel E))
    (htrans : ∀ i : Fin 4, ∃ g : S, (g : SignModel E).right • 0 = i)
    (h01 : pair 0 1 ∈ E.toSubmodule) (h02 : pair 0 2 ∈ E.toSubmodule)
    (hs01 : (inl (Multiplicative.ofAdd ⟨pair 0 1,h01⟩) : SignModel E) ∈ S)
    (hs02 : (inl (Multiplicative.ofAdd ⟨pair 0 2,h02⟩) : SignModel E) ∈ S) :
    AffineModel.Irreducible ((linearHom E).comp S.subtype).range := by
  intro W hW
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  have hex : ∃ v ∈ W, v ≠ 0 := by
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
  obtain ⟨g,hg⟩ := htrans i
  let w : Vector := linearHom E (g⁻¹ : S) v
  have hw : w ∈ W := hW _ ⟨g⁻¹,rfl⟩ v hv
  have hw0 : w 0 ≠ 0 := by
    change coefficient (((g : SignModel E)⁻¹).left.toAdd.1 0) *
      v (((g : SignModel E).right⁻¹)⁻¹ • 0) ≠ 0
    rw [inv_inv,hg]
    exact mul_ne_zero (coefficient_ne_zero _) hi
  have hp : (Pi.single 0 (w 0) : Vector) ∈ W := by
    rw [← isolate_zero E h01 h02 w]
    have hfirst := W.sub_mem
      (hW _ ⟨⟨inl (Multiplicative.ofAdd ⟨pair 0 1,h01⟩),hs01⟩,rfl⟩ w hw) hw
    exact W.sub_mem
      (hW _ ⟨⟨inl (Multiplicative.ofAdd ⟨pair 0 2,h02⟩),hs02⟩,rfl⟩ _ hfirst) hfirst
  have hzero : (Pi.single 0 1 : Vector) ∈ W := single_normalize W hw0 hp
  have hsingle (j : Fin 4) : (Pi.single j 1 : Vector) ∈ W := by
    obtain ⟨g,hg⟩ := htrans j
    have hs := hW _ ⟨g,rfl⟩ (Pi.single 0 1) hzero
    change linearHom E g (Pi.single 0 1) ∈ W at hs
    rw [linearHom_single,hg,mul_one] at hs
    exact single_normalize W (coefficient_ne_zero _) hs
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
  exact W.sum_mem fun j _ => W.nsmul_mem (hsingle j) _

theorem multiplicative_irreducible (S : Subgroup (SignModel E))
    (hirr : AffineModel.Irreducible ((linearHom E).comp S.subtype).range) :
    IrreducibleAbelianSemidirect.Irreducible
      ((LinearSemidirectCoprimeSocleBounds.linearAction (linearHom E)).comp S.subtype) := by
  intro W hW
  have hinv : ∀ g ∈ ((linearHom E).comp S.subtype).range,
      ∀ v, v ∈ W.toAddSubgroup' → g v ∈ W.toAddSubgroup' := by
    rintro _ ⟨g,rfl⟩ v hv
    exact hW g (Multiplicative.ofAdd v) hv
  rcases hirr W.toAddSubgroup' hinv with hb | ht
  · left
    apply bot_unique
    intro v hv
    have hv' : v.toAdd ∈ W.toAddSubgroup' := hv
    rw [hb] at hv'
    exact Subgroup.mem_bot.mpr (Multiplicative.toAdd.injective (AddSubgroup.mem_bot.mp hv'))
  · right
    apply top_unique
    intro v _
    change v.toAdd ∈ W.toAddSubgroup'
    rw [ht]
    exact AddSubgroup.mem_top _

theorem action_injective [FaithfulSMul R (Fin 4)] (S : Subgroup (SignModel E)) :
    Function.Injective
      ((LinearSemidirectCoprimeSocleBounds.linearAction (linearHom E)).comp S.subtype) := by
  intro g h he
  apply Subtype.ext
  apply linearHom_injective E
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun a : MulAut (Multiplicative Vector) =>
    (a (Multiplicative.ofAdd v)).toAdd) he

variable [Finite R] [FaithfulSMul R (Fin 4)]
  (K : Subgroup (BinarySignTernaryAffineSocles.Model E))

theorem socle_of_surjective
    (hblocks : Function.Surjective (blocks E K))
    (htrans : ∀ i : Fin 4, ∃ r : R, r • 0 = i)
    (h01 : pair 0 1 ∈ E.toSubmodule) (h02 : pair 0 2 ∈ E.toSubmodule)
    (hs01 : (inl (Multiplicative.ofAdd ⟨pair 0 1,h01⟩) : SignModel E) ∈ signImage E K)
    (hs02 : (inl (Multiplicative.ofAdd ⟨pair 0 2,h02⟩) : SignModel E) ∈ signImage E K)
    (u a : ℕ) (hpos : 0 < u+a)
    (hu : UniformSubrepresentationGeneratorBound
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)) u)
    (ha : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (u+a) := by
  have hactual : ∀ i : Fin 4, ∃ g : signImage E K, (g : SignModel E).right • 0 = i := by
    intro i
    obtain ⟨r,hr⟩ := htrans i
    obtain ⟨g,hg⟩ := hblocks r
    exact ⟨g,by change (blocks E K g) • 0 = i; rw [hg,hr]⟩
  have hirr := multiplicative_irreducible E (signImage E K)
    (irreducible E (signImage E K) hactual h01 h02 hs01 hs02)
  have hgen : ∀ L : Subgroup (signImage E K), L.Normal →
      ∃ x : Fin (u+a) → signImage E K, Subgroup.normalClosure (Set.range x) = L := by
    intro L hL
    letI := hL
    apply exists_normal_generating_tuple_of_normalGen_le L
    exact LinearSemidirectSubgroupFullProjection.normalGen_le
      (CyclicOrbitBinarySignNormalGenerators.linearAction E) (signImage E K)
      hblocks u a (UniformBinarySignTernarySocles.uniform_sign E u hu) ha L
  have hK := IrreducibleAbelianSemidirectSubgroup.normal_generating_tuples
    (LinearSemidirectCoprimeSocleBounds.linearAction (linearHom E)) K
    (action_injective E (signImage E K)) hirr hpos hgen
  exact normal_generating_tuples_of_surjective pi hpi hK
    (finiteGroupSocle Q) inferInstance

end SymmetricSubgroupAsymptotics.BinarySignTernaryIrreducibleSubgroupSocles

end
