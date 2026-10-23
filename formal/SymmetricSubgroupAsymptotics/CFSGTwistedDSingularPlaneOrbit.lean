import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPairOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedDHighestPairOperator
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearBasis
import SymmetricSubgroupAsymptotics.CFSGSingularPairSpan
import Mathlib.LinearAlgebra.Span.Basic

/-! Every Q-singular two-plane in the actual fixed-field space is an
actual relative highest-root plane. This retains Q in characteristic
two and uses literal relative words for both basis vectors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPlaneOrbit
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDHighestPairOperator CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexFlagVectors

def standardRootPlane (s : ℕ) (q : CFSG.PrimePower) :
    Submodule (fixedField q) (fixedSpace (s + 2) q) :=
  Submodule.span (fixedField q)
    {CFSGTwistedDHighestPairOperator.firstVector s q,
      CFSGTwistedDHighestPairOperator.secondVector s q}

def conjugateRootPlane (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    Submodule (fixedField q) (fixedSpace (s + 2) q) :=
  (standardRootPlane s q).map (fixedLinearHom (s + 2) q g).toLinearMap

theorem standardRootPlane_finrank (s : ℕ) (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (standardRootPlane s q) = 2 := by
  have h0 : CFSGTwistedDHighestPairOperator.firstVector s q ≠ 0 := by
    intro h
    have he := congrArg (fun x : fixedSpace (s + 2) q => x.val (Sum.inl 0)) h
    simp only [firstVector_val, CFSGOrthogonalDIndexFlagVectors.firstVector,
      Pi.single_eq_same] at he
    change (1 : q.Extension 2) = 0 at he
    exact one_ne_zero he
  have hi (c : fixedField q) :
      CFSGTwistedDHighestPairOperator.secondVector s q ≠
        c • CFSGTwistedDHighestPairOperator.firstVector s q := by
    intro h
    have he := congrArg
      (fun x : fixedSpace (s + 2) q => x.val (Sum.inl (secondIndex s))) h
    simp only [Submodule.coe_smul, Pi.smul_apply, firstVector_val, secondVector_val,
      CFSGOrthogonalDIndexFlagVectors.firstVector, CFSGOrthogonalDIndexFlagVectors.secondVector,
      Pi.single_apply, Sum.inl.injEq, Ne.symm (zero_ne_second s),
      if_true, if_false, smul_zero, one_ne_zero] at he
  exact CFSGSingularPairSpan.finrank_pair _ _ h0 hi

theorem standardRootPlane_singular (s : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (s + 2) q) (hv : v ∈ standardRootPlane s q) :
    fixedQuadraticForm (s + 2) q v = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, splitQuadraticForm_apply]
  let x : Index (s + 4) → q.Extension 2 :=
    (a : q.Extension 2) • Pi.single (Sum.inl 0) 1 +
      (b : q.Extension 2) • Pi.single (Sum.inl (secondIndex s)) 1
  change dotProduct (leftPart (q.Extension 2) x) (rightPart (q.Extension 2) x) = 0
  have hr : rightPart (q.Extension 2) x = 0 := by
    funext i
    simp [x, rightPart, Pi.single_apply]
  rw [hr, dotProduct_zero]

theorem conjugateRootPlane_finrank (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    Module.finrank (fixedField q) (conjugateRootPlane s q g) = 2 :=
  ((fixedLinearHom (s + 2) q g).finrank_map_eq (standardRootPlane s q)).trans
    (standardRootPlane_finrank s q)

theorem conjugateRootPlane_singular (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (v : fixedSpace (s + 2) q)
    (hv : v ∈ conjugateRootPlane s q g) : fixedQuadraticForm (s + 2) q v = 0 := by
  obtain ⟨w, hw, rfl⟩ := hv
  exact (fixedLinearHom_preserves_Q (s + 2) q g w).trans (standardRootPlane_singular s q w hw)

theorem exists_conjugateRootPlane_of_singular (s : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace (s + 2) q))
    (hdim : Module.finrank (fixedField q) P = 2)
    (hs : ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0) :
    ∃ g : relativeRootGroup (s + 2) q, P = conjugateRootPlane s q g := by
  letI : Module.Finite (fixedField q) (fixedSpace (s + 2) q) := Module.Finite.of_finite
  obtain ⟨v, hv, w, hw, hv0, hnot, hspan⟩ := CFSGTwoDimensionalLinearBasis.exists_pair P hdim
  have rawQ (x : fixedSpace (s + 2) q) (hx : x ∈ P) :
      splitQ (q.Extension 2) x.val = 0 := by
    have he := congrArg (fun a : fixedField q => (a : q.Extension 2)) (hs x hx)
    dsimp only at he
    simpa only [fixedQuadraticForm_apply, splitQuadraticForm_apply] using he
  have hp : CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2) v.val w.val = 0 := by
    have he := rawQ (v + w) (P.add_mem hv hw)
    change splitQ (q.Extension 2) (v.val + w.val) = 0 at he
    rw [CFSGOrthogonalDIndexPolarForm.splitQ_add, rawQ v hv, rawQ w hw,
      zero_add, zero_add] at he
    exact he
  have hn (c : fixedField q) : w.val ≠ (c : q.Extension 2) • v.val := by
    intro he
    exact hnot c (Subtype.ext he)
  obtain ⟨a, hav, haw⟩ := CFSGTwistedDSingularPairOrbit.exists_singular_pair_frame s q
    v.val w.val v.property w.property (fun he => hv0 (Subtype.ext he))
    ((splitQuadraticForm_apply _ _ _).trans (rawQ v hv))
    ((splitQuadraticForm_apply _ _ _).trans (rawQ w hw)) hp hn
  have havF : fixedLinearHom (s + 2) q a v = CFSGTwistedDHighestPairOperator.firstVector s q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply, firstVector_val]
    exact hav
  have hawF : fixedLinearHom (s + 2) q a w = CFSGTwistedDHighestPairOperator.secondVector s q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply, secondVector_val]
    exact haw
  have hmap : P.map (fixedLinearHom (s + 2) q a).toLinearMap = standardRootPlane s q := by
    rw [← hspan, Submodule.map_span, Set.image_pair]
    change Submodule.span (fixedField q) {fixedLinearHom (s + 2) q a v,
      fixedLinearHom (s + 2) q a w} = standardRootPlane s q
    rw [havF, hawF]
    rfl
  refine ⟨a⁻¹, ?_⟩
  change P = (standardRootPlane s q).map (fixedLinearHom (s + 2) q a⁻¹).toLinearMap
  rw [← hmap, ← Submodule.map_comp]
  have hi : (fixedLinearHom (s + 2) q a⁻¹).toLinearMap.comp
      (fixedLinearHom (s + 2) q a).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change fixedLinearHom (s + 2) q a⁻¹ (fixedLinearHom (s + 2) q a x) = x
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hi, Submodule.map_id]

theorem singular_two_plane_iff_conjugateRootPlane (s : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace (s + 2) q)) :
    (Module.finrank (fixedField q) P = 2 ∧ ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0) ↔
      ∃ g : relativeRootGroup (s + 2) q, P = conjugateRootPlane s q g := by
  constructor
  · rintro ⟨hd, hs⟩
    exact exists_conjugateRootPlane_of_singular s q P hd hs
  · rintro ⟨g, rfl⟩
    exact ⟨conjugateRootPlane_finrank s q g, conjugateRootPlane_singular s q g⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPlaneOrbit
