import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-!
# Induced generators with a top action which need not be faithful

A quotient can retain other original orbits while acting on one selected
orbit's block set.  Faithfulness on that selected block set is unnecessary:
faithfulness of the original wreath embedding and transitivity suffice for
the elementary kernel's induced-module embedding.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences

/-- Only the actual data needed for one selected block orbit.  The top may
retain additional actions, so its action on `I` is allowed a kernel. -/
structure WreathState
    (Q I : Type) [Group Q] [Fintype I] [Nonempty I] [MulAction Q I] where
  A : Type
  D : Type
  [groupA : Group A]
  [finiteA : Finite A]
  [groupD : Group D]
  [finiteD : Finite D]
  rho : A →* PermutationalWreathProduct D Q I
  rho_injective : Function.Injective rho
  top_surjective : Function.Surjective
    (PermutationalWreathProduct.rightHom.comp rho)
  top_pretransitive : MulAction.IsPretransitive Q I

attribute [instance] WreathState.groupA WreathState.finiteA
  WreathState.groupD WreathState.finiteD

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I] [MulAction Q I]

namespace WreathState

def topPointStabilizer (S : WreathState Q I) (i : I) : Subgroup S.A :=
  (MulAction.stabilizer Q i).comap
    (PermutationalWreathProduct.rightHom.comp S.rho)

theorem topPointStabilizer_index (S : WreathState Q I) (i : I) :
    (S.topPointStabilizer i).index = Fintype.card I := by
  rw [topPointStabilizer, Subgroup.index_comap_of_surjective _ S.top_surjective]
  letI : MulAction.IsPretransitive Q I := S.top_pretransitive
  simpa only [Fintype.card_eq_nat_card] using
    MulAction.index_stabilizer_of_transitive Q i

end WreathState

variable (S : WreathState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

abbrev K : Subgroup S.A :=
  PermutationalWreathProduct.Compression.kernel S.rho phi

abbrev E :=
  PermutationalWreathProduct.Compression.kernelElementaryChart
    (p := C.p) S.rho phi C.equiv.symm S.rho_injective

/-- The local component seen by the stabilizer of one displayed block. -/
def stabilizerComponent (i : I) : S.topPointStabilizer i →* S.D where
  toFun h := (S.rho h.1).left i
  map_one' := by simp
  map_mul' x y := by
    change (S.rho (x.1 * y.1)).left i =
      (S.rho x.1).left i * (S.rho y.1).left i
    rw [map_mul, PermutationalWreathProduct.mul_left]
    have hx : (S.rho x.1).right⁻¹ • i = i := by
      have hx0 : (S.rho x.1).right • i = i := x.2
      calc
        (S.rho x.1).right⁻¹ • i =
            (S.rho x.1).right⁻¹ • ((S.rho x.1).right • i) :=
              congrArg ((S.rho x.1).right⁻¹ • ·) hx0.symm
        _ = i := inv_smul_smul _ _
    simp only [Pi.mul_apply, hx]

/-- Conjugation on the local elementary chief factor, restricted to the
actual block stabilizer. -/
def localRepresentation (i : I) :
    Representation (ZMod C.p) (S.topPointStabilizer i) C.V :=
  C.quotientRepresentation.ρ.comp
    ((QuotientGroup.mk' phi.ker).comp (stabilizerComponent S i))

/-- One literal coordinate of the correlated elementary kernel. -/
abbrev localCoordinate (i : I) :
    K S phi →* Multiplicative C.V :=
  PermutationalWreathProduct.Compression.elementaryCoordinate
    S.rho phi C.equiv.symm i

omit [Finite D'] in
/-- The local coordinate is equivariant for the actual stabilizer action. -/
theorem localCoordinate_equivariant (i : I)
    (h : S.topPointStabilizer i) (n : K S phi) :
    (localCoordinate S phi C i (MulAut.conjNormal h.1 n)).toAdd =
      localRepresentation S phi C i h
        (localCoordinate S phi C i n).toAdd := by
  change (localCoordinate S phi C i (MulAut.conjNormal h.1 n)).toAdd =
    C.quotientRepresentation.ρ
      (QuotientGroup.mk' phi.ker ((S.rho h.1).left i))
      (localCoordinate S phi C i n).toAdd
  change
    (C.equiv
      (PermutationalWreathProduct.Compression.kernelCoordinate
        S.rho phi i (MulAut.conjNormal h.1 n))).toAdd =
    C.quotientRepresentation.ρ
      (QuotientGroup.mk' phi.ker ((S.rho h.1).left i))
      (C.equiv
        (PermutationalWreathProduct.Compression.kernelCoordinate
          S.rho phi i n)).toAdd
  rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
  apply congrArg (fun z : Multiplicative C.V ↦ z.toAdd)
  apply congrArg C.equiv
  apply Subtype.ext
  change
    (S.rho (h.1 * n.1 * h.1⁻¹)).left i =
      (S.rho h.1).left i * (S.rho n.1).left i * ((S.rho h.1).left i)⁻¹
  rw [map_mul, map_mul, map_inv]
  exact PermutationalWreathProduct.conj_left_of_fixed
    (S.rho h.1) (S.rho n.1) i h.2
      ((PermutationalWreathProduct.mem_mapBase_ker_iff phi (S.rho n.1)).mp n.2).1

/-- The correlated elementary kernel representation, inflated from the
literal quotient to the current ambient group. -/
def ambientRepresentation : Representation (ZMod C.p) S.A
    (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) :=
  (E S phi C).quotientRepresentation.ρ.comp
    (QuotientGroup.mk' (K S phi))

/-- The induced representation attached to one block coordinate. -/
def inducedRepresentation (i : I) : Representation (ZMod C.p) S.A
    (Representation.IndV (S.topPointStabilizer i).subtype
      (localRepresentation S phi C i)) :=
  Representation.ind (S.topPointStabilizer i).subtype
    (localRepresentation S phi C i)

/-- Additive form of the actual orbit-evaluation map. -/
def inducedAddMap (i : I) :
    PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm →+
      Representation.IndV (S.topPointStabilizer i).subtype
        (localRepresentation S phi C i) :=
  (localChiefInducedEvaluation (S.topPointStabilizer i)
      (MulAut.conjNormal (H := K S phi))
      (localRepresentation S phi C i)
      (localCoordinate S phi C i)
      (localCoordinate_equivariant S phi C i)).comp
    (PermutationalWreathProduct.Compression.elementaryAddEquiv
      (p := C.p) S.rho phi C.equiv.symm S.rho_injective).symm.toAddMonoidHom

/-- Linear form of the orbit-evaluation map. -/
def inducedLinearMap (i : I) :
    PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm →ₗ[ZMod C.p]
      Representation.IndV (S.topPointStabilizer i).subtype
        (localRepresentation S phi C i) :=
  (inducedAddMap S phi C i).toZModLinearMap C.p

@[simp] theorem inducedLinearMap_apply (i : I)
    (v : PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) :
    inducedLinearMap S phi C i v = inducedAddMap S phi C i v := rfl

omit [Finite D'] in
private theorem elementaryAddEquiv_symm_chart (n : K S phi) :
    (PermutationalWreathProduct.Compression.elementaryAddEquiv
      (p := C.p) S.rho phi C.equiv.symm S.rho_injective).symm
        ((E S phi C).equiv n).toAdd = Additive.ofMul n := by
  let e := PermutationalWreathProduct.Compression.elementaryAddEquiv
    (p := C.p) S.rho phi C.equiv.symm S.rho_injective
  change e.symm (e (Additive.ofMul n)) = Additive.ofMul n
  exact e.symm_apply_apply _

@[simp] theorem inducedAddMap_chart (i : I) (n : K S phi) :
    inducedAddMap S phi C i ((E S phi C).equiv n).toAdd =
      localChiefInducedEvaluation (S.topPointStabilizer i)
        (MulAut.conjNormal (H := K S phi))
        (localRepresentation S phi C i)
        (localCoordinate S phi C i)
        (localCoordinate_equivariant S phi C i) (Additive.ofMul n) := by
  unfold inducedAddMap
  rw [AddMonoidHom.comp_apply]
  apply congrArg
  exact elementaryAddEquiv_symm_chart S phi C n

omit [Finite D'] in
@[simp] theorem ambientRepresentation_chart (a : S.A) (n : K S phi) :
    ambientRepresentation S phi C a ((E S phi C).equiv n).toAdd =
      ((E S phi C).equiv (MulAut.conjNormal a n)).toAdd := by
  exact ElementaryMinimalNormalChart.quotientRepresentation_apply
    (E S phi C) a n

theorem inducedLinearMap_equivariant (i : I) (a : S.A)
    (v : PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) :
    inducedLinearMap S phi C i (ambientRepresentation S phi C a v) =
      inducedRepresentation S phi C i a (inducedLinearMap S phi C i v) := by
  obtain ⟨n, hn⟩ := (E S phi C).equiv.surjective
    (Multiplicative.ofAdd v)
  have hv : ((E S phi C).equiv n).toAdd = v :=
    congrArg Multiplicative.toAdd hn
  rw [← hv]
  rw [inducedLinearMap_apply, ambientRepresentation_chart,
    inducedAddMap_chart, inducedLinearMap_apply, inducedAddMap_chart]
  exact localChiefInducedEvaluation_equivariant
    (S.topPointStabilizer i)
    (MulAut.conjNormal (H := K S phi))
    (localRepresentation S phi C i)
    (localCoordinate S phi C i)
    (localCoordinate_equivariant S phi C i) a n

/-- The ambient elementary representation, inflated to the original group,
maps to the induced representation obtained from one block coordinate. -/
def inducedIntertwiner (i : I) :
    (ambientRepresentation S phi C).IntertwiningMap
      (inducedRepresentation S phi C i) where
  toLinearMap := inducedLinearMap S phi C i
  isIntertwining' a := by
    apply LinearMap.ext
    exact inducedLinearMap_equivariant S phi C i a

/-- Transitivity of the actual top makes one induced orbit evaluation see
every coordinate of the correlated kernel. -/
theorem inducedIntertwiner_injective (i₀ : I) :
    Function.Injective (inducedIntertwiner S phi C i₀) := by
  intro v w hvw
  change inducedLinearMap S phi C i₀ v =
    inducedLinearMap S phi C i₀ w at hvw
  have hzero : inducedLinearMap S phi C i₀ (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  obtain ⟨n, hn⟩ := (E S phi C).equiv.surjective
    (Multiplicative.ofAdd (v - w))
  have hnval : ((E S phi C).equiv n).toAdd = v - w :=
    congrArg Multiplicative.toAdd hn
  have heval : localChiefInducedEvaluation (S.topPointStabilizer i₀)
      (MulAut.conjNormal (H := K S phi))
      (localRepresentation S phi C i₀)
      (localCoordinate S phi C i₀)
      (localCoordinate_equivariant S phi C i₀) (Additive.ofMul n) = 0 := by
    rw [← inducedAddMap_chart S phi C i₀ n,
      ← inducedLinearMap_apply S phi C i₀, hnval]
    exact hzero
  have hall := (localChiefInducedEvaluation_eq_zero_iff
    (S.topPointStabilizer i₀)
    (MulAut.conjNormal (H := K S phi))
    (localRepresentation S phi C i₀)
    (localCoordinate S phi C i₀)
    (localCoordinate_equivariant S phi C i₀) n).mp heval
  have hcoord : ∀ i : I,
      PermutationalWreathProduct.Compression.kernelCoordinate
        S.rho phi i n = 1 := by
    intro i
    letI : MulAction.IsPretransitive Q I := S.top_pretransitive
    obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q i i₀
    obtain ⟨a, ha⟩ := S.top_surjective q
    have ha' : (S.rho a).right = q := ha
    have hqi : q⁻¹ • i₀ = i := by
      calc
        q⁻¹ • i₀ = q⁻¹ • (q • i) := congrArg (q⁻¹ • ·) hq.symm
        _ = i := inv_smul_smul q i
    have hlocal : localCoordinate S phi C i₀
        (MulAut.conjNormal a n) = 1 := hall a
    have hraw : PermutationalWreathProduct.Compression.kernelCoordinate
        S.rho phi i₀ (MulAut.conjNormal a n) = 1 := by
      apply C.equiv.injective
      simpa only [map_one] using hlocal
    have hleft := congrArg Subtype.val hraw
    have hnright : (S.rho n.1).right = 1 :=
      ((PermutationalWreathProduct.mem_mapBase_ker_iff
        phi (S.rho n.1)).mp n.2).1
    have hformula :
        (S.rho (a * n.1 * a⁻¹)).left i₀ =
          (S.rho a).left i₀ * (S.rho n.1).left i * ((S.rho a).left i₀)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      simp [PermutationalWreathProduct.mul_left,
        PermutationalWreathProduct.mul_right,
        PermutationalWreathProduct.inv_left, hnright, ha', hqi, smul_smul]
    have hconj :
        (S.rho a).left i₀ * (S.rho n.1).left i * ((S.rho a).left i₀)⁻¹ = 1 := by
      rw [← hformula]
      exact hleft
    apply Subtype.ext
    change (S.rho n.1).left i = 1
    calc
      (S.rho n.1).left i =
          ((S.rho a).left i₀)⁻¹ *
            ((S.rho a).left i₀ * (S.rho n.1).left i *
              ((S.rho a).left i₀)⁻¹) * (S.rho a).left i₀ := by
            simp [mul_assoc]
      _ = 1 := by rw [hconj]; simp
  have hn1 : n = 1 := by
    apply PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
      S.rho phi S.rho_injective
    funext i
    simpa only [map_one] using hcoord i
  have hvw0 : v - w = 0 := by
    rw [← hnval, hn1, map_one]
    rfl
  exact sub_eq_zero.mp hvw0

/-- A retained refined Tracey input supplies an actual ambient normal
kernel bound while preserving the simultaneous numerical bounds.  This
uses only the selected orbit's block count, regardless of the other actions
retained in the top. -/
theorem exists_kernel_normalGen_bound
    (hTracey : TraceyRefinedInducedModuleInput)
    (hs : 2 ≤ Fintype.card I) (i : I) :
    ∃ H : ℕ,
      TraceyRefinedInducedCapacityBounds C.p
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I) H ∧
      MarkedC4.normalGen (K S phi) ≤ H := by
  letI : Fact C.p.Prime := ⟨C.p_prime⟩
  have hi : 2 ≤ (S.topPointStabilizer i).index := by
    rw [S.topPointStabilizer_index i]
    exact hs
  obtain ⟨H, hbounds, hgen⟩ := hTracey C.p S.A
    (S.topPointStabilizer i) hi C.V (localRepresentation S phi C i)
  have hambient : RepresentationGeneratedBy (ambientRepresentation S phi C) H :=
    representationGeneratedBy_of_injective_of_uniform hgen
      (inducedIntertwiner S phi C i) (inducedIntertwiner_injective S phi C i)
  have hquot : RepresentationGeneratedBy
      (E S phi C).quotientRepresentation.ρ H :=
    RepresentationGeneratedBy.of_comp (E S phi C).quotientRepresentation.ρ
      (QuotientGroup.mk' (K S phi)) hambient
  refine ⟨H, ?_, ?_⟩
  · simpa only [S.topPointStabilizer_index i] using hbounds
  · exact normalGen_le_of_elementaryQuotientRepresentation_generated
      (K S phi) (E S phi C) H hquot

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
