import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPlaneOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveRootFamily

/-! An actual fixed-field two-plane determines its whole relative
highest-root subgroup, through the SAME quadratic pair operator.
There is no ambient extension-field plane substitution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneRootLine
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeHighestRoot
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDHighestPairOperator CFSGTwistedDSingularPlaneOrbit
open CFSGTwistedDProjectiveRootFamily CFSGTwistedA2FixedField CFSGAlternatingPairOperator

def highestRoot (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q) :
    relativeRootGroup (s + 2) q := (highestInRelativeU s q a).val

def conjugateRootLine (s : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup (s + 2) q) :
    Subgroup (relativeRootGroup (s + 2) q) :=
  (highestRootLine s q).map (MulAut.conj g).toMonoidHom

theorem fixedLinearHom_preserves_polar (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v w : fixedSpace n q) :
    (fixedQuadraticForm n q).polarBilin (fixedLinearHom n q g v) (fixedLinearHom n q g w) =
      (fixedQuadraticForm n q).polarBilin v w := by
  change fixedQuadraticForm n q (fixedLinearHom n q g v + fixedLinearHom n q g w) -
      fixedQuadraticForm n q (fixedLinearHom n q g v) -
        fixedQuadraticForm n q (fixedLinearHom n q g w) = _
  rw [← map_add, fixedLinearHom_preserves_Q, fixedLinearHom_preserves_Q,
    fixedLinearHom_preserves_Q]
  rfl

theorem conjugate_highest_action (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (a : fixedField q) (v : fixedSpace (s + 2) q) :
    fixedLinearHom (s + 2) q (g * highestRoot s q a * g⁻¹) v =
      v + a • pairOperator (fixedQuadraticForm (s + 2) q).polarBilin
        (fixedLinearHom (s + 2) q g (firstVector s q))
        (fixedLinearHom (s + 2) q g (secondVector s q)) v := by
  let L := fixedLinearHom (s + 2) q g
  have hLR (x : fixedSpace (s + 2) q) :
      L (fixedLinearHom (s + 2) q g⁻¹ x) = x := by
    rw [map_inv]
    exact L.apply_symm_apply x
  have hi := pairOperator_intertwines (fixedQuadraticForm (s + 2) q).polarBilin
    L.toLinearMap (fixedLinearHom_preserves_polar (s + 2) q g)
    (firstVector s q) (secondVector s q) (fixedLinearHom (s + 2) q g⁻¹ v)
  change L (pairOperator (fixedQuadraticForm (s + 2) q).polarBilin
      (firstVector s q) (secondVector s q) (fixedLinearHom (s + 2) q g⁻¹ v)) =
    pairOperator (fixedQuadraticForm (s + 2) q).polarBilin
      (L (firstVector s q)) (L (secondVector s q))
      (L (fixedLinearHom (s + 2) q g⁻¹ v)) at hi
  rw [hLR] at hi
  rw [map_mul, map_mul]
  change L (fixedLinearHom (s + 2) q (highestRoot s q a)
    (fixedLinearHom (s + 2) q g⁻¹ v)) = _
  rw [show highestRoot s q a = (highestInRelativeU s q a).val from rfl,
    highest_action, map_add, map_smul, hLR, hi]

theorem conjugateRootPlane_eq_span (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    conjugateRootPlane s q g = Submodule.span (fixedField q)
      {fixedLinearHom (s + 2) q g (firstVector s q),
        fixedLinearHom (s + 2) q g (secondVector s q)} := by
  rw [conjugateRootPlane, standardRootPlane, Submodule.map_span, Set.image_pair]
  rfl

theorem conjugate_root_element_of_plane_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hp : conjugateRootPlane s q g = conjugateRootPlane s q h) (a : fixedField q) :
    ∃ b : fixedField q,
      g * highestRoot s q a * g⁻¹ = h * highestRoot s q b * h⁻¹ := by
  have hu : fixedLinearHom (s + 2) q g (firstVector s q) ∈
      Submodule.span (fixedField q) {fixedLinearHom (s + 2) q h (firstVector s q),
        fixedLinearHom (s + 2) q h (secondVector s q)} := by
    rw [← conjugateRootPlane_eq_span, ← hp, conjugateRootPlane_eq_span]
    exact Submodule.subset_span (Or.inl rfl)
  have hv : fixedLinearHom (s + 2) q g (secondVector s q) ∈
      Submodule.span (fixedField q) {fixedLinearHom (s + 2) q h (firstVector s q),
        fixedLinearHom (s + 2) q h (secondVector s q)} := by
    rw [← conjugateRootPlane_eq_span, ← hp, conjugateRootPlane_eq_span]
    exact Submodule.subset_span (Or.inr rfl)
  obtain ⟨d, hd⟩ := pairOperator_mem_span (fixedQuadraticForm (s + 2) q).polarBilin
    (fixedLinearHom (s + 2) q h (firstVector s q))
    (fixedLinearHom (s + 2) q h (secondVector s q))
    (fixedLinearHom (s + 2) q g (firstVector s q))
    (fixedLinearHom (s + 2) q g (secondVector s q)) hu hv
  refine ⟨a * d, ?_⟩
  apply fixedLinearHom_injective (s + 2) q
  apply LinearEquiv.ext
  intro v
  have hdv := LinearMap.congr_fun hd v
  simp only [LinearMap.smul_apply] at hdv
  rw [conjugate_highest_action, conjugate_highest_action, hdv, smul_smul]

private theorem conjugateRootLine_le_of_plane_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hp : conjugateRootPlane s q g = conjugateRootPlane s q h) :
    conjugateRootLine s q g ≤ conjugateRootLine s q h := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := (mem_highestRootLine_iff s q y).mp hy
  obtain ⟨b, hb⟩ := conjugate_root_element_of_plane_eq s q g h hp a
  refine ⟨highestRoot s q b, (mem_highestRootLine_iff s q _).mpr ⟨b, rfl⟩, ?_⟩
  change h * highestRoot s q b * h⁻¹ = g * highestRoot s q a * g⁻¹
  exact hb.symm

theorem conjugateRootLine_eq_of_plane_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hp : conjugateRootPlane s q g = conjugateRootPlane s q h) :
    conjugateRootLine s q g = conjugateRootLine s q h :=
  le_antisymm (conjugateRootLine_le_of_plane_eq s q g h hp)
    (conjugateRootLine_le_of_plane_eq s q h g hp.symm)

end SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneRootLine
