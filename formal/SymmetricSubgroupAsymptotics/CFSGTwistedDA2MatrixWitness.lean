import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter

/-! A characteristic-independent two-coordinate witness in the literal
D elementary matrix group. Its Weyl word has fourth power one, and its
commutator with the positive root has off-diagonal entry minus one.
This proves noncentrality without a group-name identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDA2MatrixWitness
open Matrix CFSGTypeAElementaryMatrices CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDGenerationSLDouble
variable (K : Type) [Field K] (r : ℕ)

def slWeyl (i j : Fin r) (hij : i ≠ j) : NaturalSL K r :=
  elementary hij (-1) * elementary (Ne.symm hij) 1 * elementary hij (-1)

theorem slWeyl_val (i j : Fin r) (hij : i ≠ j) :
    (slWeyl K r i j hij).val = CFSGMatrixPairRotation.rotation K i j := by
  have hn : Matrix.single i j (-1 : K) = -Matrix.single i j 1 := by
    ext x y
    simp only [Matrix.single_apply, Matrix.neg_apply]
    split_ifs <;> ring
  change Matrix.transvection i j (-1) * Matrix.transvection j i 1 *
    Matrix.transvection i j (-1) = _
  simp only [Matrix.transvection, hn, ← sub_eq_add_neg]
  exact CFSGMatrixPairRotation.word_eq_rotation K i j hij

theorem slWeyl_four (i j : Fin r) (hij : i ≠ j) : slWeyl K r i j hij ^ 4 = 1 := by
  apply Subtype.ext
  change (slWeyl K r i j hij).val ^ 4 = 1
  rw [slWeyl_val]
  exact CFSGMatrixPairRotation.rotation_four K i j hij

theorem slWeyl_conjugates (i j : Fin r) (hij : i ≠ j) (a : K) :
    slWeyl K r i j hij * elementary hij a * (slWeyl K r i j hij)⁻¹ =
      elementary (Ne.symm hij) (-a) := by
  have hm : slWeyl K r i j hij * elementary hij a =
      elementary (Ne.symm hij) (-a) * slWeyl K r i j hij := by
    apply Subtype.ext
    change (slWeyl K r i j hij).val * (elementary hij a).val =
      (elementary (Ne.symm hij) (-a)).val * (slWeyl K r i j hij).val
    rw [slWeyl_val, elementary_coe, elementary_coe]
    simp [CFSGMatrixPairRotation.rotation, Matrix.transvection, mul_add, add_mul,
      mul_sub, sub_mul, hij, Ne.symm hij]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
    split_ifs <;> ring
  have hc := congrArg (fun X : NaturalSL K r => X * (slWeyl K r i j hij)⁻¹) hm
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hc

theorem slWeyl_commutator_entry (i j : Fin r) (hij : i ≠ j) :
    (⁅slWeyl K r i j hij, elementary hij (1 : K)⁆).val i j = -1 := by
  rw [commutatorElement_def, slWeyl_conjugates, elementary_inv]
  change ((Matrix.transvection j i (-1 : K) : Matrix (Fin r) (Fin r) K) *
    (Matrix.transvection i j (-1 : K) : Matrix (Fin r) (Fin r) K)) i j = -1
  simp [Matrix.transvection, mul_add, add_mul, hij, Ne.symm hij,
    Matrix.single_apply, Matrix.one_apply]

def chain (i j : Fin r) (hij : i ≠ j) (a : K) : elementaryRootGroup K r :=
  doubleIntoElementary K r (elementary hij a)

theorem chain_inv (i j : Fin r) (hij : i ≠ j) (a : K) :
    (chain K r i j hij a)⁻¹ = chain K r i j hij (-a) := by
  change (doubleIntoElementary K r (elementary hij a))⁻¹ =
    doubleIntoElementary K r (elementary hij (-a))
  rw [← map_inv, elementary_inv]

theorem chain_commutator (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : K) :
    ⁅chain K r i j hij a, chain K r j k hjk b⁆ = chain K r i k hik (a * b) := by
  change ⁅doubleIntoElementary K r (elementary hij a),
    doubleIntoElementary K r (elementary hjk b)⁆ =
      doubleIntoElementary K r (elementary hik (a * b))
  rw [← map_commutatorElement, elementary_commutator]

def naturalWeyl (i j : Fin r) (hij : i ≠ j) : elementaryRootGroup K r :=
  doubleIntoElementary K r (slWeyl K r i j hij)

theorem naturalWeyl_word (i j : Fin r) (hij : i ≠ j) :
    naturalWeyl K r i j hij =
      (chain K r i j hij 1)⁻¹ * chain K r j i (Ne.symm hij) 1 * (chain K r i j hij 1)⁻¹ := by
  rw [chain_inv]
  change doubleIntoElementary K r (elementary hij (-1) * elementary (Ne.symm hij) 1 *
    elementary hij (-1)) = _
  rw [map_mul, map_mul]
  rfl

theorem naturalWeyl_four (i j : Fin r) (hij : i ≠ j) : naturalWeyl K r i j hij ^ 4 = 1 := by
  change (doubleIntoElementary K r (slWeyl K r i j hij)) ^ 4 = 1
  rw [← map_pow, slWeyl_four, map_one]

theorem naturalWeyl_commutator_not_center (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) :
    ⁅naturalWeyl K (s + 4) i j hij, chain K (s + 4) i j hij 1⁆ ∉
      Subgroup.center (elementaryRootGroup K (s + 4)) := by
  intro hc
  obtain ⟨c, hscalar⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) _).mp hc
  have hz : ((⁅naturalWeyl K (s + 4) i j hij, chain K (s + 4) i j hij 1⁆).val :
      Mat K (s + 4)) (Sum.inl i) (Sum.inl j) = 0 := by
    rw [hscalar]
    simp only [Matrix.smul_apply, Matrix.one_apply, Sum.inl.injEq, if_neg hij, smul_zero]
  have he : ⁅naturalWeyl K (s + 4) i j hij, chain K (s + 4) i j hij 1⁆ =
      doubleIntoElementary K (s + 4) ⁅slWeyl K (s + 4) i j hij, elementary hij (1 : K)⁆ := by
    exact (map_commutatorElement (doubleIntoElementary K (s + 4)) _ _).symm
  have hv : ((⁅naturalWeyl K (s + 4) i j hij, chain K (s + 4) i j hij 1⁆).val :
      Mat K (s + 4)) (Sum.inl i) (Sum.inl j) = -1 := by
    rw [he]
    change (⁅slWeyl K (s + 4) i j hij, elementary hij (1 : K)⁆).val i j = -1
    exact slWeyl_commutator_entry K (s + 4) i j hij
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) (hv.symm.trans hz)

end SymmetricSubgroupAsymptotics.CFSGTwistedDA2MatrixWitness
