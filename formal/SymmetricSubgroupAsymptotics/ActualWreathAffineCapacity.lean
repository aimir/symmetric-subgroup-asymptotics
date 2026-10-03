import SymmetricSubgroupAsymptotics.ActualWreathCompressionTowerExistence
import SymmetricSubgroupAsymptotics.AffineJointElementaryCapacity
import SymmetricSubgroupAsymptotics.ChiefOrbitEvaluation
import SymmetricSubgroupAsymptotics.InducedSubquotientGenerators
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity

/-!
# Affine capacity for every actual wreath-compression state

The elementary kernel in an actual wreath state is a correlated submodule
of the product of its local chief factors.  Evaluation at one block embeds
that literal module into the representation induced from the actual block
stabilizer.  Tracey's published generator theorem can therefore be applied
without replacing the correlated kernel by the full coordinate product.

This file turns that induced-module theorem into the complete joint capacity
required by `ActualWreathCompressionTower`.  Both invariant intersections
and normal-complement graphs are charged in the resulting capacity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace ActualWreathAffineCapacity

/-- The simultaneous ceiling used by the actual affine carrier.  Tracey's
half-dimension theorem gives the sharp linear exponent, while his logarithmic
induced-module theorem makes the finite carrier coefficient subquadratic.
Keeping their minimum retains both conclusions in one literal capacity. -/
noncomputable def inducedCapacityCeiling (a s : ℕ) : ℕ :=
  min (a * s / 2) (traceyInducedGeneratorCeiling a s)

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

variable (S : ActualWreathCompressionState Q I)
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

/-- A subrepresentation of a quotient-group action is literally a
subrepresentation after inflation along the quotient map. -/
def subrepresentationComp
    {k G B V : Type} [Field k] [Group G] [Group B]
    [AddCommGroup V] [Module k V]
    (gamma : G →* B) (rho : Representation k B V)
    (M : Subrepresentation rho) : Subrepresentation (rho.comp gamma) where
  toSubmodule := M.toSubmodule
  apply_mem_toSubmodule g := M.apply_mem_toSubmodule (gamma g)

theorem subrepresentationComp_injective
    {k G B V : Type} [Field k] [Group G] [Group B]
    [AddCommGroup V] [Module k V]
    (gamma : G →* B) (rho : Representation k B V) :
    Function.Injective (subrepresentationComp gamma rho) := by
  intro M N h
  apply Subrepresentation.toSubmodule_injective
  exact congrArg
    (fun X : Subrepresentation (rho.comp gamma) ↦ X.toSubmodule) h

/-- One common refined tuple length for the induced representation and its
dual.  The two applications of Tracey's theorem are padded to their maximum;
every retained numerical ceiling survives that maximum. -/
structure RefinedCapacityData (i : I) where
  H : ℕ
  bounds : TraceyRefinedInducedCapacityBounds C.p
    (Module.finrank (ZMod C.p) C.V) (Fintype.card I) H
  primal : UniformSubrepresentationGeneratorBound
    (inducedRepresentation S phi C i) H
  dual : UniformSubrepresentationGeneratorBound
    (inducedRepresentation S phi C i).dual H

/-- Construct the common primal/dual refined capacity at one literal block. -/
noncomputable def refinedCapacityData
    (hTracey : TraceyRefinedInducedModuleInput)
    (hI : 2 ≤ Fintype.card I) (i : I) :
    RefinedCapacityData S phi C i := by
  have hindex : 2 ≤ (S.topPointStabilizer i).index := by
    rw [S.topPointStabilizer_index i]
    exact hI
  let hp := hTracey C.p S.A (S.topPointStabilizer i) hindex C.V
    (localRepresentation S phi C i)
  let hd := hTracey.dual S.A (S.topPointStabilizer i) hindex C.V
    (localRepresentation S phi C i)
  have hH' : TraceyRefinedInducedCapacityBounds C.p
      (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
        ((Classical.choose hp : ℕ) : ℝ) := by
    simpa only [S.topPointStabilizer_index] using
      (Classical.choose_spec hp).1
  have hK' : TraceyRefinedInducedCapacityBounds C.p
      (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
        ((Classical.choose hd : ℕ) : ℝ) := by
    simpa only [S.topPointStabilizer_index] using
      (Classical.choose_spec hd).1
  have hprimal : UniformSubrepresentationGeneratorBound
      (inducedRepresentation S phi C i) (Classical.choose hp) :=
    (Classical.choose_spec hp).2
  have hdual : UniformSubrepresentationGeneratorBound
      (inducedRepresentation S phi C i).dual (Classical.choose hd) :=
    (Classical.choose_spec hd).2
  refine
    { H := max (Classical.choose hp) (Classical.choose hd)
      bounds := by
        simpa only [Nat.cast_max] using hH'.max hK'
      primal := uniformSubrepresentationGeneratorBound_mono _ hprimal
        (le_max_left (Classical.choose hp) (Classical.choose hd))
      dual := uniformSubrepresentationGeneratorBound_mono _ hdual
        (le_max_right (Classical.choose hp) (Classical.choose hd)) }

/-- Refined induced generators bound the invariant intersections in the
literal correlated elementary kernel. -/
theorem invariant_count_le_refined
    (i₀ : I) (D : RefinedCapacityData S phi C i₀) :
    Nat.card (Subrepresentation (E S phi C).quotientRepresentation.ρ) ≤
      Nat.card (E S phi C).V ^ D.H := by
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  have hambient : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C) D.H := by
    exact D.primal.of_injective (inducedIntertwiner S phi C i₀)
      (inducedIntertwiner_injective S phi C i₀)
  calc
    Nat.card (Subrepresentation (E S phi C).quotientRepresentation.ρ) ≤
        Nat.card (Subrepresentation (ambientRepresentation S phi C)) :=
      Nat.card_le_card_of_injective
        (subrepresentationComp
          (QuotientGroup.mk' (K S phi))
          (E S phi C).quotientRepresentation.ρ)
        (subrepresentationComp_injective
          (QuotientGroup.mk' (K S phi))
          (E S phi C).quotientRepresentation.ρ)
    _ ≤ Nat.card (E S phi C).V ^ D.H :=
      hambient.card_subrepresentation_le

/-- Tracey's induced-module theorem bounds the invariant intersections in
the literal correlated elementary kernel. -/
theorem invariant_count_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hI : 2 ≤ Fintype.card I) (i₀ : I) :
    Nat.card (Subrepresentation (E S phi C).quotientRepresentation.ρ) ≤
      Nat.card (E S phi C).V ^
        inducedCapacityCeiling
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I) := by
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  have hindex : 2 ≤ (S.topPointStabilizer i₀).index := by
    rw [S.topPointStabilizer_index i₀]
    exact hI
  let Hhalf := Module.finrank (ZMod C.p) C.V * Fintype.card I / 2
  let Hlog := traceyInducedGeneratorCeiling
    (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
  let H := inducedCapacityCeiling
    (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
  have huniformHalf := hTraceyHalf C.p S.A (S.topPointStabilizer i₀)
    hindex C.V (localRepresentation S phi C i₀)
  have huniformLog := hTraceyLog.uniform C.p S.A (S.topPointStabilizer i₀)
    hindex C.V (localRepresentation S phi C i₀)
  have huniform : UniformSubrepresentationGeneratorBound
      (inducedRepresentation S phi C i₀) H := by
    rcases le_total Hhalf Hlog with h | h
    · simpa only [inducedRepresentation, H, Hhalf, Hlog,
        inducedCapacityCeiling, S.topPointStabilizer_index i₀,
        min_eq_left h] using huniformHalf
    · simpa only [inducedRepresentation, H, Hhalf, Hlog,
        inducedCapacityCeiling, S.topPointStabilizer_index i₀,
        min_eq_right h] using huniformLog
  have hambient : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C)
      H := by
    have h := huniform.of_injective (inducedIntertwiner S phi C i₀)
      (inducedIntertwiner_injective S phi C i₀)
    exact h
  calc
    Nat.card (Subrepresentation (E S phi C).quotientRepresentation.ρ) ≤
        Nat.card (Subrepresentation (ambientRepresentation S phi C)) :=
      Nat.card_le_card_of_injective
        (subrepresentationComp
          (QuotientGroup.mk' (K S phi))
          (E S phi C).quotientRepresentation.ρ)
        (subrepresentationComp_injective
          (QuotientGroup.mk' (K S phi))
          (E S phi C).quotientRepresentation.ρ)
    _ ≤ Nat.card (E S phi C).V ^
        inducedCapacityCeiling
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I) :=
      hambient.card_subrepresentation_le

section NormalSection

variable (N : Subgroup S.A) [N.Normal]

abbrev pi : S.A →* S.A ⧸ K S phi := QuotientGroup.mk' (K S phi)

abbrev originalChart : OriginalKernelModuleChart
    (pi S phi) (E S phi C).quotientRepresentation :=
  (E S phi C).originalKernelChart

abbrev normalSpace : Submodule (ZMod C.p)
    (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) :=
  (originalChart S phi C).normalSpace
    (pi S phi) (E S phi C).quotientRepresentation N

/-- The literal normal section, inflated from its exact quotient top back to
the current ambient group. -/
def inflatedSectionRepresentation : Representation (ZMod C.p) S.A
    ((PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
      S.rho phi C.equiv.symm) ⧸ normalSpace S phi C N) :=
  ((originalChart S phi C).sectionRepresentation
      (pi S phi) (E S phi C).quotientRepresentation N).ρ.comp
    (QuotientGroup.mk' ((pi S phi).ker ⊔ N))

/-- The ordinary module quotient is an intertwiner from the correlated
kernel representation to the inflated exact normal section. -/
def sectionQuotientIntertwiner :
    (ambientRepresentation S phi C).IntertwiningMap
      (inflatedSectionRepresentation S phi C N) where
  toLinearMap := (normalSpace S phi C N).mkQ
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    let k : (pi S phi).ker :=
      (originalChart S phi C).equiv (Multiplicative.ofAdd x)
    change (normalSpace S phi C N).mkQ
        ((E S phi C).quotientRepresentation.ρ
          (pi S phi g) x) =
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N).ρ
          (QuotientGroup.mk' ((pi S phi).ker ⊔ N) g)
          ((normalSpace S phi C N).mkQ x)
    have hk : ((originalChart S phi C).kernelCoordinates
        (pi S phi) (E S phi C).quotientRepresentation k).toAdd = x := by
      exact congrArg Multiplicative.toAdd
        ((originalChart S phi C).equiv.symm_apply_apply
          (Multiplicative.ofAdd x))
    have hsection : ((originalChart S phi C).sectionMap
        (pi S phi) (E S phi C).quotientRepresentation N k).toAdd =
        (normalSpace S phi C N).mkQ x := by
      change (normalSpace S phi C N).mkQ
        (((originalChart S phi C).kernelCoordinates
          (pi S phi) (E S phi C).quotientRepresentation k).toAdd) = _
      rw [hk]
    rw [← hsection]
    rw [OriginalKernelModuleChart.sectionRepresentation_apply]
    change (normalSpace S phi C N).mkQ
        ((E S phi C).quotientRepresentation.ρ
          (pi S phi g) x) =
      (normalSpace S phi C N).mkQ
        (((originalChart S phi C).kernelCoordinates
          (pi S phi) (E S phi C).quotientRepresentation
          (MulAut.conjNormal g k)).toAdd)
    apply congrArg (normalSpace S phi C N).mkQ
    apply Multiplicative.ofAdd.injective
    apply (originalChart S phi C).equiv.injective
    change (originalChart S phi C).equiv
        (Multiplicative.ofAdd
          ((E S phi C).quotientRepresentation.ρ (pi S phi g) x)) =
      (originalChart S phi C).equiv
        ((originalChart S phi C).equiv.symm (MulAut.conjNormal g k))
    rw [(originalChart S phi C).equiv.apply_symm_apply]
    apply Subtype.ext
    exact (originalChart S phi C).conjugate g x

theorem sectionQuotientIntertwiner_surjective :
    Function.Surjective (sectionQuotientIntertwiner S phi C N) :=
  (normalSpace S phi C N).mkQ_surjective

/-- Every literal normal section has Schur capacity bounded by the same
induced-module generator ceiling. -/
theorem sharpSectionCapacity_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hI : 2 ≤ Fintype.card I) (i₀ : I) :
    representationSchurCapacity
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N).ρ ≤
      (inducedCapacityCeiling
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I) : ℕ) := by
  letI : FiniteDimensional (ZMod C.p)
      (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm) := inferInstance
  letI : FiniteDimensional (ZMod (E S phi C).p) (E S phi C).V :=
    (E S phi C).finiteDimensional
  letI : FiniteDimensional (ZMod (E S phi C).p)
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N) := by
    change FiniteDimensional (ZMod (E S phi C).p)
      ((E S phi C).V ⧸
        (originalChart S phi C).normalSpace
          (pi S phi) (E S phi C).quotientRepresentation N)
    infer_instance
  let Hhalf := Module.finrank (ZMod C.p) C.V * Fintype.card I / 2
  let Hlog := traceyInducedGeneratorCeiling
    (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
  let H := inducedCapacityCeiling
    (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
  have hindex : 2 ≤ (S.topPointStabilizer i₀).index := by
    rw [S.topPointStabilizer_index i₀]
    exact hI
  have hdual : UniformSubrepresentationGeneratorBound
      (inducedRepresentation S phi C i₀).dual H := by
    have hhalf := InducedSubquotientGenerators.dualInduced_uniform_half
      (S.topPointStabilizer i₀) (localRepresentation S phi C i₀)
      hTraceyHalf hindex
    have hlog := InducedSubquotientGenerators.dualInduced_uniform
      (S.topPointStabilizer i₀) (localRepresentation S phi C i₀)
      hTraceyLog hindex
    rcases le_total Hhalf Hlog with h | h
    · simpa only [inducedRepresentation, H, Hhalf, Hlog,
        inducedCapacityCeiling, S.topPointStabilizer_index i₀,
        min_eq_left h] using hhalf
    · simpa only [inducedRepresentation, H, Hhalf, Hlog,
        inducedCapacityCeiling, S.topPointStabilizer_index i₀,
        min_eq_right h] using hlog
  have hgen : RepresentationGeneratedBy
      (inflatedSectionRepresentation S phi C N).dual H :=
    representationDual_generated_of_subquotient
      hdual
      (inducedIntertwiner S phi C i₀)
      (inducedIntertwiner_injective S phi C i₀)
      (sectionQuotientIntertwiner S phi C N)
      (sectionQuotientIntertwiner_surjective S phi C N)
  have hinflated : representationSchurCapacity
      (inflatedSectionRepresentation S phi C N) ≤ H :=
    representationSchurCapacity_le_of_dual_generated
      (inflatedSectionRepresentation S phi C N) H hgen
  have heq := representationSchurCapacity_comp
    (QuotientGroup.mk' ((pi S phi).ker ⊔ N))
    (QuotientGroup.mk'_surjective ((pi S phi).ker ⊔ N))
    ((originalChart S phi C).sectionRepresentation
      (pi S phi) (E S phi C).quotientRepresentation N).ρ
  rw [← heq]
  exact hinflated

/-- The dual half of the common refined datum controls every literal normal
section of the correlated elementary kernel. -/
theorem sharpSectionCapacity_le_refined
    (i₀ : I) (D : RefinedCapacityData S phi C i₀) :
    representationSchurCapacity
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N).ρ ≤ D.H := by
  letI : FiniteDimensional (ZMod C.p)
      (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm) := inferInstance
  letI : FiniteDimensional (ZMod (E S phi C).p) (E S phi C).V :=
    (E S phi C).finiteDimensional
  letI : FiniteDimensional (ZMod (E S phi C).p)
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N) := by
    change FiniteDimensional (ZMod (E S phi C).p)
      ((E S phi C).V ⧸
        (originalChart S phi C).normalSpace
          (pi S phi) (E S phi C).quotientRepresentation N)
    infer_instance
  have hgen : RepresentationGeneratedBy
      (inflatedSectionRepresentation S phi C N).dual D.H :=
    representationDual_generated_of_subquotient
      D.dual
      (inducedIntertwiner S phi C i₀)
      (inducedIntertwiner_injective S phi C i₀)
      (sectionQuotientIntertwiner S phi C N)
      (sectionQuotientIntertwiner_surjective S phi C N)
  have hinflated : representationSchurCapacity
      (inflatedSectionRepresentation S phi C N) ≤ D.H :=
    representationSchurCapacity_le_of_dual_generated
      (inflatedSectionRepresentation S phi C N) D.H hgen
  have heq := representationSchurCapacity_comp
    (QuotientGroup.mk' ((pi S phi).ker ⊔ N))
    (QuotientGroup.mk'_surjective ((pi S phi).ker ⊔ N))
    ((originalChart S phi C).sectionRepresentation
      (pi S phi) (E S phi C).quotientRepresentation N).ρ
  rw [← heq]
  exact hinflated

end NormalSection

/-- The literal correlated elementary kernel is a submodule of the full
product of the local chief factor over the actual block set. -/
theorem elementaryModule_card_le :
    Nat.card (E S phi C).V ≤
      C.p ^ (Module.finrank (ZMod C.p) C.V * Fintype.card I) := by
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  letI : FiniteDimensional (ZMod C.p)
      (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm) := inferInstance
  letI : FiniteDimensional (ZMod (E S phi C).p) (E S phi C).V :=
    (E S phi C).finiteDimensional
  change Nat.card
      (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
        S.rho phi C.equiv.symm) ≤ _
  rw [Module.natCard_eq_pow_finrank (K := ZMod C.p)]
  simp only [Nat.card_zmod]
  apply Nat.pow_le_pow_right C.p_prime.one_le
  calc
    Module.finrank (ZMod C.p)
        (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
          S.rho phi C.equiv.symm) ≤
        Module.finrank (ZMod C.p) (I → C.V) :=
      Submodule.finrank_le
        (PermutationalWreathProduct.Compression.ElementarySubmodule (p := C.p)
          S.rho phi C.equiv.symm)
    _ = Fintype.card I * Module.finrank (ZMod C.p) C.V := by
      rw [Module.finrank_pi_fintype]
      simp
    _ = Module.finrank (ZMod C.p) C.V * Fintype.card I :=
      Nat.mul_comm _ _

private theorem affineCoefficient_le_primePower
    (p a s H Hlog g v A : ℕ) (hp : 1 ≤ p)
    (hA : A ≤ p ^ (a * s)) (hH : H ≤ Hlog) :
    (A : ℝ) ^ H * (p : ℝ) ^ (H * (v / p)) *
        (A : ℝ) ^ (g + 1) ≤
      (p : ℝ) ^ traceyAffineCoefficientExponent a s Hlog g v p := by
  have hAR : (A : ℝ) ≤ (p : ℝ) ^ (a * s) := by
    exact_mod_cast hA
  have hbase : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hexp : traceyAffineCoefficientExponent a s H g v p ≤
      traceyAffineCoefficientExponent a s Hlog g v p := by
    unfold traceyAffineCoefficientExponent
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.mul_le_mul_left (a * s) hH)
        (Nat.mul_le_mul_right (v / p) hH))
      (le_refl _)
  calc
    (A : ℝ) ^ H * (p : ℝ) ^ (H * (v / p)) *
          (A : ℝ) ^ (g + 1) ≤
        (((p : ℝ) ^ (a * s)) ^ H) *
          (p : ℝ) ^ (H * (v / p)) *
          (((p : ℝ) ^ (a * s)) ^ (g + 1)) := by
      gcongr
    _ = (p : ℝ) ^ traceyAffineCoefficientExponent a s H g v p := by
      unfold traceyAffineCoefficientExponent
      simp only [← pow_mul]
      rw [← pow_add, ← pow_add]
    _ ≤ (p : ℝ) ^ traceyAffineCoefficientExponent a s Hlog g v p :=
      pow_le_pow_right₀ hbase hexp

/-- The concrete joint-capacity input for one literal elementary step of an
actual wreath-compression state.  The same induced-module ceiling controls
both invariant intersections and every normal quotient section. -/
noncomputable def jointCapacityInput
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hI : 2 ≤ Fintype.card I) (i₀ : I) :
    AffineJointElementaryCapacityInput C.p
      (pi S phi) (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart where
  H := inducedCapacityCeiling
    (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
  g := S.generatorCount
  v := S.sourceDegree
  invariantCount := invariant_count_le S phi C hTraceyHalf hTraceyLog hI i₀
  sectionGenerators := by
    intro N
    refine ⟨fun j => QuotientGroup.mk' ((pi S phi).ker ⊔ N.1)
      (S.generators j), ?_⟩
    exact quotient_generators_full ((pi S phi).ker ⊔ N.1)
      S.generators S.generators_full
  sharpSectionCapacity := by
    intro N
    letI : N.1.Normal := N.2
    exact sharpSectionCapacity_le S phi C N.1 hTraceyHalf hTraceyLog hI i₀
  sectionalRank := S.sectionalRank C.p

/-- Joint elementary incidence using the common refined primal/dual tuple
length. -/
noncomputable def jointCapacityInputRefined
    (i₀ : I) (D : RefinedCapacityData S phi C i₀) :
    AffineJointElementaryCapacityInput C.p
      (pi S phi) (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart where
  H := D.H
  g := S.generatorCount
  v := S.sourceDegree
  invariantCount := invariant_count_le_refined S phi C i₀ D
  sectionGenerators := by
    intro N
    refine ⟨fun j => QuotientGroup.mk' ((pi S phi).ker ⊔ N.1)
      (S.generators j), ?_⟩
    exact quotient_generators_full ((pi S phi).ker ⊔ N.1)
      S.generators S.generators_full
  sharpSectionCapacity := by
    intro N
    letI : N.1.Normal := N.2
    exact sharpSectionCapacity_le_refined S phi C N.1 i₀ D
  sectionalRank := S.sectionalRank C.p

/-- The concrete joint capacity carries a uniform prime-power coefficient
bound with Tracey's logarithmic induced-module ceiling. -/
theorem jointCapacity_coefficient_le
    [Finite (E S phi C).quotientRepresentation]
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hI : 2 ≤ Fintype.card I) (i₀ : I) :
    ((jointCapacityInput S phi C hTraceyHalf hTraceyLog hI i₀).toJointCapacity
      (hpi := QuotientGroup.mk'_surjective (K S phi))).coefficient ≤
      (C.p : ℝ) ^ traceyAffineCoefficientExponent
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
        (traceyInducedGeneratorCeiling
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
        S.generatorCount S.sourceDegree C.p := by
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  dsimp only [AffineJointElementaryCapacityInput.toJointCapacity,
    AffineJointElementaryCapacityInput.coefficient, jointCapacityInput]
  apply affineCoefficient_le_primePower
  · exact C.p_prime.one_le
  · exact elementaryModule_card_le S phi C
  · exact min_le_right _ _

/-- The refined joint capacity keeps the same logarithmic coefficient
ceiling, because the common refined tuple length is still below Tracey's
uniform logarithmic ceiling. -/
theorem jointCapacityRefined_coefficient_le
    [Finite (E S phi C).quotientRepresentation]
    (i₀ : I) (D : RefinedCapacityData S phi C i₀) :
    ((jointCapacityInputRefined S phi C i₀ D).toJointCapacity
      (hpi := QuotientGroup.mk'_surjective (K S phi))).coefficient ≤
      (C.p : ℝ) ^ traceyAffineCoefficientExponent
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
        (traceyInducedGeneratorCeiling
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
        S.generatorCount S.sourceDegree C.p := by
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  dsimp only [AffineJointElementaryCapacityInput.toJointCapacity,
    AffineJointElementaryCapacityInput.coefficient, jointCapacityInputRefined]
  apply affineCoefficient_le_primePower
  · exact C.p_prime.one_le
  · exact elementaryModule_card_le S phi C
  · exact_mod_cast D.bounds.logarithmic

/-- Tracey's published induced-module theorem supplies the elementary
capacity input at every quotient state of every actual block system with at
least two blocks.  This is the closed construction consumed by the tower. -/
noncomputable def elementaryCapacityInput
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hI : 2 ≤ Fintype.card I) :
    ActualWreathElementaryCapacityInput (Q := Q) (I := I) := by
  intro S D' _ _ phi hphi C
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  letI : Finite (E S phi C).V := Finite.of_injective
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype
    (PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := C.p) S.rho phi C.equiv.symm).subtype_injective
  letI : Finite (E S phi C).quotientRepresentation :=
    inferInstanceAs (Finite (E S phi C).V)
  let i₀ : I := Classical.choice inferInstance
  let D := refinedCapacityData S phi C hTraceyRefined hI i₀
  refine ⟨(jointCapacityInputRefined S phi C i₀ D).toJointCapacity
    (hpi := QuotientGroup.mk'_surjective (K S phi)), ?_, ?_, ?_, ?_⟩
  · simpa only [AffineJointElementaryCapacityInput.toJointCapacity,
      jointCapacityInputRefined] using D.bounds.half
  · simpa only [AffineJointElementaryCapacityInput.toJointCapacity,
      jointCapacityInputRefined] using D.bounds.logarithmic
  · exact D.bounds
  · exact jointCapacityRefined_coefficient_le S phi C i₀ D

end ActualWreathAffineCapacity
end SymmetricSubgroupAsymptotics

end
