import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-!
# The actual imprimitive wreath embedding

An equivariant block map from a faithful transitive action determines the
literal block component and literal top action.  Choosing one transporter
from the base block to every block gives the standard faithful embedding
into their permutational wreath product.  Every local component is realized
by an element stabilizing the selected block, so the embedding satisfies the
exact-component fullness condition used by semisimple compression.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {A Omega X : Type} [Group A]
  [MulAction A Omega] [MulAction A X]
  [MulAction.IsPretransitive A X] [FaithfulSMul A Omega]
  (b : Omega → X) (hb : ∀ (a : A) (omega : Omega), b (a • omega) = a • b omega)
  (x0 : X)

namespace ActualBlockWreathEmbedding

/-- A chosen transporter from the base block to `x`. -/
def representative (x : X) : A :=
  Classical.choose (MulAction.exists_smul_eq A x0 x)

@[simp] theorem representative_smul (x : X) :
    representative (A := A) x0 x • x0 = x :=
  Classical.choose_spec (MulAction.exists_smul_eq A x0 x)

theorem representative_inv_smul (x : X) :
    (representative (A := A) x0 x)⁻¹ • x = x0 := by
  calc
    (representative (A := A) x0 x)⁻¹ • x =
        (representative (A := A) x0 x)⁻¹ •
          (representative (A := A) x0 x • x0) :=
      congrArg ((representative (A := A) x0 x)⁻¹ • ·)
        (representative_smul (A := A) x0 x).symm
    _ = x0 := inv_smul_smul (representative (A := A) x0 x) x0

abbrev Fibre : Type := originalBlockFibre b x0

abbrev Component : Subgroup (Equiv.Perm (Fibre b x0)) :=
  originalBlockComponent b hb x0

abbrev topMap : A →* Equiv.Perm X := MulAction.toPermHom A X

abbrev Top : Subgroup (Equiv.Perm X) := (topMap (A := A) (X := X)).range

/-- The element of the base-block stabilizer measuring the local action of
`a` at the destination block `x`. -/
def localStabilizer (a : A) (x : X) : MulAction.stabilizer A x0 :=
  ⟨(representative x0 x)⁻¹ * a * representative x0 (a⁻¹ • x), by
    change ((representative x0 x)⁻¹ * a * representative x0 (a⁻¹ • x)) • x0 = x0
    rw [mul_smul, mul_smul, representative_smul, smul_inv_smul,
      representative_inv_smul]⟩

@[simp] theorem localStabilizer_one (x : X) :
    localStabilizer x0 (1 : A) x = 1 := by
  apply Subtype.ext
  simp [localStabilizer]

theorem localStabilizer_mul (a c : A) (x : X) :
    localStabilizer x0 (a * c) x =
      localStabilizer x0 a x * localStabilizer x0 c (a⁻¹ • x) := by
  apply Subtype.ext
  simp only [localStabilizer, Subgroup.coe_mul, mul_inv_rev, smul_smul]
  group

/-- The literal component coordinate. -/
def localCoordinate (a : A) (x : X) : Component b hb x0 :=
  (originalBlockFibreAction b hb x0).rangeRestrict (localStabilizer x0 a x)

@[simp] theorem localCoordinate_one (x : X) :
    localCoordinate b hb x0 (1 : A) x = 1 := by
  unfold localCoordinate
  rw [localStabilizer_one]
  exact MonoidHom.map_one _

theorem localCoordinate_mul (a c : A) (x : X) :
    localCoordinate b hb x0 (a * c) x =
      localCoordinate b hb x0 a x * localCoordinate b hb x0 c (a⁻¹ • x) := by
  unfold localCoordinate
  rw [localStabilizer_mul]
  exact MonoidHom.map_mul _ _ _

@[simp] theorem top_inverse_smul (a : A) (x : X) :
    (((topMap (A := A) (X := X)).rangeRestrict a)⁻¹ : Top (A := A) (X := X)) • x =
      a⁻¹ • x := rfl

/-- The standard actual wreath embedding, retaining the literal component
and the literal top range. -/
def embedding :
    A →* PermutationalWreathProduct (Component b hb x0)
      (Top (A := A) (X := X)) X where
  toFun a := ⟨localCoordinate b hb x0 a,
    (topMap (A := A) (X := X)).rangeRestrict a⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext x
      exact localCoordinate_one b hb x0 x
    · apply Subtype.ext
      exact MonoidHom.map_one _
  map_mul' a c := by
    apply PermutationalWreathProduct.ext
    · funext x
      change localCoordinate b hb x0 (a * c) x =
        localCoordinate b hb x0 a x *
          localCoordinate b hb x0 c
            ((((topMap (A := A) (X := X)).rangeRestrict a)⁻¹ :
              Top (A := A) (X := X)) • x)
      rw [top_inverse_smul, localCoordinate_mul]
    · apply Subtype.ext
      exact MonoidHom.map_mul _ _ _

/-- Relabel the original point set as base-fibre times block set. -/
def productEquiv : Fibre b x0 × X ≃ Omega where
  toFun p := representative (A := A) x0 p.2 • p.1.1
  invFun omega :=
    ⟨⟨(representative (A := A) x0 (b omega))⁻¹ • omega, by
      rw [hb, representative_inv_smul (A := A)]⟩, b omega⟩
  left_inv := by
    rintro ⟨omega, x⟩
    have hblock : b (representative (A := A) x0 x • omega.1) = x := by
      rw [hb, omega.2, representative_smul (A := A)]
    apply Prod.ext
    · apply Subtype.ext
      change (representative (A := A) x0
          (b (representative (A := A) x0 x • omega.1)))⁻¹ •
        (representative (A := A) x0 x • omega.1) = omega.1
      rw [hblock, inv_smul_smul]
    · exact hblock
  right_inv := by
    intro omega
    exact smul_inv_smul (representative (A := A) x0 (b omega)) omega

/-- The wreath action is exactly the original action after the product
relabeling. -/
theorem productEquiv_equivariant (a : A) (p : Fibre b x0 × X) :
    productEquiv b hb x0 (embedding b hb x0 a • p) =
      a • productEquiv b hb x0 p := by
  rcases p with ⟨omega, x⟩
  change representative (A := A) x0 (a • x) •
      (((localCoordinate b hb x0 a (a • x) :
        Equiv.Perm (Fibre b x0)) omega : Fibre b x0) : Omega) =
    a • (representative (A := A) x0 x • omega.1)
  change representative (A := A) x0 (a • x) •
      (((localStabilizer x0 a (a • x) : A) • omega.1)) =
    a • (representative (A := A) x0 x • omega.1)
  change representative (A := A) x0 (a • x) •
      (((representative (A := A) x0 (a • x))⁻¹ * a *
        representative (A := A) x0 (a⁻¹ • (a • x))) • omega.1) =
    a • (representative (A := A) x0 x • omega.1)
  rw [inv_smul_smul]
  calc
    _ = representative (A := A) x0 (a • x) •
        ((representative (A := A) x0 (a • x))⁻¹ •
          (a • (representative (A := A) x0 x • omega.1))) := by
      conv_lhs => rw [mul_smul, mul_smul]
    _ = a • (representative (A := A) x0 x • omega.1) :=
      smul_inv_smul (representative (A := A) x0 (a • x)) _

/-- Faithfulness of the original action makes the standard wreath map
injective. -/
theorem embedding_injective : Function.Injective (embedding b hb x0) := by
  intro a c hac
  apply eq_of_smul_eq_smul (M := A) (α := Omega)
  intro omega
  let p := (productEquiv b hb x0).symm omega
  calc
    a • omega = a • productEquiv b hb x0 p := by
      rw [(productEquiv b hb x0).apply_symm_apply]
    _ = productEquiv b hb x0 (embedding b hb x0 a • p) :=
      (productEquiv_equivariant b hb x0 a p).symm
    _ = productEquiv b hb x0 (embedding b hb x0 c • p) := by rw [hac]
    _ = c • productEquiv b hb x0 p :=
      productEquiv_equivariant b hb x0 c p
    _ = c • omega := by rw [(productEquiv b hb x0).apply_symm_apply]

/-- Every element of the exact component occurs over every block. -/
theorem fullComponent :
    PermutationalWreathProduct.Compression.FullComponent
      (embedding b hb x0) := by
  intro x d
  obtain ⟨h, hh⟩ := d.2
  let a : A := representative (A := A) x0 x * h.1 *
    (representative (A := A) x0 x)⁻¹
  refine ⟨a, ?_, ?_⟩
  · change a • x = x
    dsimp only [a]
    calc
      (representative (A := A) x0 x * h.1 *
          (representative (A := A) x0 x)⁻¹) • x =
          representative (A := A) x0 x •
            (h.1 • ((representative (A := A) x0 x)⁻¹ • x)) := by
        conv_lhs => rw [mul_smul, mul_smul]
      _ = representative (A := A) x0 x • (h.1 • x0) := by
        rw [representative_inv_smul (A := A)]
      _ = representative (A := A) x0 x • x0 := by rw [h.2]
      _ = x := representative_smul (A := A) x0 x
  · apply Subtype.ext
    change originalBlockFibreAction b hb x0 (localStabilizer x0 a x) = d.1
    rw [← hh]
    apply congrArg
    apply Subtype.ext
    dsimp only [a]
    have ha : a⁻¹ • x = x := by
      have hinv : (h.1 : A)⁻¹ • x0 = x0 := by
        calc
          (h.1 : A)⁻¹ • x0 = (h.1 : A)⁻¹ • ((h.1 : A) • x0) :=
            congrArg ((h.1 : A)⁻¹ • ·) h.2.symm
          _ = x0 := inv_smul_smul (h.1 : A) x0
      change (representative (A := A) x0 x * h.1 *
        (representative (A := A) x0 x)⁻¹)⁻¹ • x = x
      calc
        _ = representative (A := A) x0 x •
            ((h.1 : A)⁻¹ •
              ((representative (A := A) x0 x)⁻¹ • x)) := by
          conv_lhs => rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_smul, mul_smul]
        _ = representative (A := A) x0 x • ((h.1 : A)⁻¹ • x0) := by
          rw [representative_inv_smul (A := A)]
        _ = representative (A := A) x0 x • x0 := by rw [hinv]
        _ = x := representative_smul (A := A) x0 x
    change (representative (A := A) x0 x)⁻¹ * a *
      representative (A := A) x0 (a⁻¹ • x) = h.1
    rw [ha]
    dsimp only [a]
    group

end ActualBlockWreathEmbedding
end SymmetricSubgroupAsymptotics

end
