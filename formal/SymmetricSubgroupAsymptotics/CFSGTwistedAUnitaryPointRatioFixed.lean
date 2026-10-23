import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinateRectangle
import SymmetricSubgroupAsymptotics.CFSGHermitianRectangleRatioFixed
import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals

/-! Any common strong-mixed-ray ratio of the SAME actual unitary
point permutation is fixed by the defining involution. The literal
four-axis rectangle works in every rank at least three, including q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem unitary_point_common_ratio_fixed (q : CFSG.PrimePower) (s : ℕ)
    (f : Equiv.Perm (SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (t : q.Extension 2)
    (hratio : ∀ (x y : Fin (s+4) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (s+3) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (s+3) → y ≠ 0 →
      unitaryNaturalPair q (s+3) y x = 0 → ∀ (hn : x+y ≠ 0)
        (hsing : unitaryNaturalPair q (s+3) (x+y) (x+y) = 0),
      (f (singularRay (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
        (x+y) hn hsing)).val = (q.Extension 2) ∙ (x+t • y)) :
    definingFieldAutomorphism q 2 t = t := by
  obtain ⟨x,u,y,z,hx,hu,hy,hz,hx0,hu0,hy0,hz0,hyx,hzu,hxz,hsource⟩ :=
    exists_unitary_coordinate_rectangle q s
  have hsum0 (a b : Fin (s+4) → q.Extension 2)
      (ha : a ∈ unitaryStandardSingularSpace q (s+3))
      (hb : b ∈ unitaryOppositeSingularSpace q (s+3)) (ha0 : a ≠ 0) : a+b ≠ 0 := by
    intro he
    have haZ : a ∈ unitaryOppositeSingularSpace q (s+3) :=
      (add_eq_zero_iff_eq_neg.mp he) ▸ (unitaryOppositeSingularSpace q (s+3)).neg_mem hb
    exact ha0 ((Submodule.disjoint_def.mp (unitaryStandard_opposite_disjoint q (s+3))) a ha haZ)
  have hsing (a b : Fin (s+4) → q.Extension 2)
      (ha : a ∈ unitaryStandardSingularSpace q (s+3))
      (hb : b ∈ unitaryOppositeSingularSpace q (s+3))
      (hba : unitaryNaturalPair q (s+3) b a = 0) :
      unitaryNaturalPair q (s+3) (a+b) (a+b) = 0 := by
    have haa := unitaryStandardSingularSpace_pair_zero q (s+3) a ha a ha
    have hbb := unitaryOppositeSingularSpace_pair_zero q (s+3) b b hb hb
    have hab := (unitaryNaturalPair_zero_swap q (s+3) b a).mp hba
    change hermitianPair _ _ (a+b) (a+b) = 0
    rw [hermitianPair_add_left,hermitianPair_add_right,hermitianPair_add_right]
    change unitaryNaturalPair q (s+3) a a + unitaryNaturalPair q (s+3) a b +
      (unitaryNaturalPair q (s+3) b a + unitaryNaturalPair q (s+3) b b) = 0
    rw [haa,hbb,hab,hba]
    simp only [zero_add]
  let A := singularRay (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
    (x+y) (hsum0 x y hx hy hx0) (hsing x y hx hy hyx)
  let B := singularRay (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
    (u+z) (hsum0 u z hu hz hu0) (hsing u z hu hz hzu)
  have hAB : Orthogonal (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) A.val B.val :=
    (orthogonal_iff_singular_representatives _ _ A B _ _
      (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)
      (hsum0 x y hx hy hx0) (hsum0 u z hu hz hu0)).mpr hsource
  have hA : (f A).val = (q.Extension 2) ∙ (x+t • y) :=
    hratio x y hx hx0 hy hy0 hyx _ _
  have hB : (f B).val = (q.Extension 2) ∙ (u+t • z) :=
    hratio u z hu hu0 hz hz0 hzu _ _
  have himage := (hf A B).mpr hAB
  have hAmem : x+t • y ∈ (f A).val := hA.symm ▸ Submodule.mem_span_singleton_self _
  have hBmem : u+t • z ∈ (f B).val := hB.symm ▸ Submodule.mem_span_singleton_self _
  exact hermitian_rectangle_mixed_ratio_fixed _ _ x u y z t
    (unitaryStandardSingularSpace_pair_zero q (s+3) x hx u hu)
    (unitaryOppositeSingularSpace_pair_zero q (s+3) y z hy hz)
    hxz hsource (himage _ hAmem _ hBmem)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
