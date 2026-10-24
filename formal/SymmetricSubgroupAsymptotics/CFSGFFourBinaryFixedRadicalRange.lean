import SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalEmbedding

/-! The displayed radical chart covers every actual diagram-fixed
Heisenberg coordinate. This is a literal ten-coordinate reconstruction;
no fixed-quotient lifting or dimension-count surjectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalRange
open CFSGFFourBinaryRadicalCoordinates CFSGFFourBinaryFixedRadicalEmbedding
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGCommutingParameterTwist CFSGHeisenbergCoordinateGroup

theorem assemble_of_partner_fixed {K : Type*} (v : Fin 10 → K)
    (hv : ∀ i, v (partner i)=v i) :
    assemble (singleCoordinates v) (pairCoordinates v)=v := by
  have h2 : v 4=v 2 := hv 2
  have h3 : v 9=v 3 := hv 3
  have h6 : v 8=v 6 := hv 6
  funext i
  fin_cases i <;> first | rfl | exact h2.symm | exact h3.symm | exact h6.symm

private theorem sign_cast_one {K : Type} [CommRing K] [CharP K 2]
    (w : ℤ) (hw : w=1 ∨ w= -1) : (w : K)=1 := by
  rcases hw with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]

private theorem partner_fixed_of_coefficient_fixed (K : Type) [CommRing K] [CharP K 2]
    (w : Fin 10 → ℤ) (hw : ∀ i,w i=1 ∨ w i= -1) (v : Fin 10 → K)
    (hv : coefficientMap (RingEquiv.refl K) partner w v=v) :
    ∀ i,v (partner i)=v i := by
  intro i
  have he := congrFun hv (partner i)
  change (w (partner.symm (partner i)) : K)*v (partner.symm (partner i)) = v (partner i) at he
  rw [partner.symm_apply_apply,sign_cast_one _ (hw i),one_mul] at he
  exact he.symm

theorem mem_coordinateHom_range_iff_fixed (K : Type) [CommRing K] [CharP K 2]
    (g : Element K 10) :
    g ∈ (coordinateHom K).range ↔ coordinateTwist K (RingEquiv.refl K) g=g := by
  constructor
  · rintro ⟨x,rfl⟩
    exact coordinateHom_fixed K x
  · intro hg
    have ha : coefficientMap (RingEquiv.refl K) partner firstWeight g.a=g.a :=
      congrArg (fun z : Element K 10 => z.a) hg
    have hb : coefficientMap (RingEquiv.refl K) partner secondWeight g.b=g.b :=
      congrArg (fun z : Element K 10 => z.b) hg
    have hfa := partner_fixed_of_coefficient_fixed K firstWeight firstWeight_unit g.a ha
    have hfb := partner_fixed_of_coefficient_fixed K secondWeight secondWeight_unit g.b hb
    refine ⟨(⟨singleCoordinates g.a,singleCoordinates g.b,g.c⟩,
      Multiplicative.ofAdd (pairCoordinates g.a,pairCoordinates g.b)),?_⟩
    apply Element.ext
    · change assemble (singleCoordinates g.a) (pairCoordinates g.a)=g.a
      exact assemble_of_partner_fixed g.a hfa
    · change assemble (singleCoordinates g.b) (pairCoordinates g.b)=g.b
      exact assemble_of_partner_fixed g.b hfb
    · rfl

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalRange
