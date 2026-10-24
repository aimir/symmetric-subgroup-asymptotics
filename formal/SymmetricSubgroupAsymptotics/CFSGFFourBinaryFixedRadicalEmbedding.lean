import SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergCoordinateTwist
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveProjection

/-! The full characteristic-two diagram-fixed radical is realized from
literal Heisenberg4 times six additive coordinates. Its actual root
products are fixed and positive, so they inject into the original F4
model through the existing fixed-positive projection. No Levi action or
quadratic-refinement orbit is supplied as a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalEmbedding
open CFSGHeisenbergCoordinateGroup CFSGFFourBinaryRadicalCoordinates
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalHeisenbergProduct
open CFSGExceptionalHeisenbergPositive CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGTwistedE6HeisenbergCoordinateTwist CFSGCommutingParameterTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckRelativeRootGenerated
open CFSGFFourE6FixedPositiveProjection
local instance fFourBinaryRadicalRootsDecidableEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

abbrev Extra (K : Type) := (Fin 3 → K) × (Fin 3 → K)
abbrev Radical (K : Type) [CommRing K] := Element K 4 × Multiplicative (Extra K)

private theorem assemble_add {K : Type} [Add K]
    (a b : Fin 4 → K) (u v : Fin 3 → K) :
    assemble (a+b) (u+v) = assemble a u + assemble b v := by
  funext i
  fin_cases i <;> rfl

def coordinateHom (K : Type) [CommRing K] [CharP K 2] : Radical K →* Element K 10 where
  toFun g := ⟨assemble g.1.a g.2.toAdd.1, assemble g.1.b g.2.toAdd.2, g.1.c⟩
  map_one' := by
    apply Element.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  map_mul' g h := by
    apply Element.ext
    · change assemble (g.1.a+h.1.a) (g.2.toAdd.1+h.2.toAdd.1) = _
      exact assemble_add _ _ _ _
    · change assemble (g.1.b+h.1.b) (g.2.toAdd.2+h.2.toAdd.2) = _
      exact assemble_add _ _ _ _
    · change g.1.c+h.1.c+dot g.1.b h.1.a =
        g.1.c+h.1.c+dot (assemble g.1.b g.2.toAdd.2) (assemble h.1.a h.2.toAdd.1)
      rw [assemble_dot]

theorem coordinateHom_injective (K : Type) [CommRing K] [CharP K 2] :
    Function.Injective (coordinateHom K) := by
  intro g h he
  have ha : (g.1.a, g.2.toAdd.1) = (h.1.a, h.2.toAdd.1) := by
    apply assemble_injective
    exact congrArg (fun z : Element K 10 => z.a) he
  have hb : (g.1.b, g.2.toAdd.2) = (h.1.b, h.2.toAdd.2) := by
    apply assemble_injective
    exact congrArg (fun z : Element K 10 => z.b) he
  have hc := congrArg (fun z : Element K 10 => z.c) he
  apply Prod.ext
  · exact Element.ext (congrArg Prod.fst ha) (congrArg Prod.fst hb) hc
  · apply Multiplicative.toAdd.injective
    have hu : g.2.toAdd.1 = h.2.toAdd.1 :=
      congrArg (fun z : (Fin 4 → K) × (Fin 3 → K) => z.2) ha
    have hv : g.2.toAdd.2 = h.2.toAdd.2 :=
      congrArg (fun z : (Fin 4 → K) × (Fin 3 → K) => z.2) hb
    exact Prod.ext hu hv

private theorem sign_cast_one {K : Type} [CommRing K] [CharP K 2]
    (w : ℤ) (hw : w=1 ∨ w= -1) : (w : K) = 1 := by
  rcases hw with rfl | rfl <;> simp only [Int.cast_one, Int.cast_neg, CharTwo.neg_eq]

private theorem coefficient_assemble_fixed (K : Type) [CommRing K] [CharP K 2]
    (w : Fin 10 → ℤ) (hw : ∀ i, w i=1 ∨ w i= -1)
    (a : Fin 4 → K) (u : Fin 3 → K) :
    coefficientMap (RingEquiv.refl K) partner w (assemble a u) = assemble a u := by
  funext i
  change (w (partner.symm i) : K) * assemble a u (partner.symm i) = assemble a u i
  rw [sign_cast_one _ (hw _), one_mul]
  have he := assemble_partner a u (partner.symm i)
  rw [partner.apply_symm_apply] at he
  exact he.symm

theorem coordinateHom_fixed (K : Type) [CommRing K] [CharP K 2] (g : Radical K) :
    coordinateTwist K (RingEquiv.refl K) (coordinateHom K g) = coordinateHom K g := by
  apply Element.ext
  · exact coefficient_assemble_fixed K firstWeight firstWeight_unit g.1.a g.2.toAdd.1
  · exact coefficient_assemble_fixed K secondWeight secondWeight_unit g.1.b g.2.toAdd.2
  · change (centralWeight : K) * g.1.c = g.1.c
    rw [sign_cast_one _ centralWeight_unit, one_mul]

def matrixHom (K : Type) [Field K] [CharP K 2] :
    Radical K →* (Matrix GeckIndex GeckIndex K)ˣ :=
  (rawHom A hd hs hp ho configuration K).comp (coordinateHom K)

theorem matrixHom_injective (K : Type) [Field K] [CharP K 2] :
    Function.Injective (matrixHom K) :=
  (rawHom_injective A hd hs hp ho configuration K).comp (coordinateHom_injective K)

theorem matrixHom_mem_positive (K : Type) [Field K] [CharP K 2] (g : Radical K) :
    matrixHom K g ∈ Positive K :=
  rawHom_mem_positive A hd hs hp ho configuration K (coordinateHom K g)

theorem matrixHom_fixed (K : Type) [Field K] [CharP K 2] (g : Radical K) :
    unitTwist K (RingEquiv.refl K) (matrixHom K g) = matrixHom K g :=
  (rawHom_fixed_iff K (RingEquiv.refl K) (coordinateHom K g)).mpr (coordinateHom_fixed K g)

def fixedPositiveHom (K : Type) [Field K] [CharP K 2] :
    Radical K →* signedFixed K (RingEquiv.refl K) false :=
  (matrixHom K).codRestrict (signedFixed K (RingEquiv.refl K) false)
    (fun g => ⟨matrixHom_mem_positive K g, matrixHom_fixed K g⟩)

theorem fixedPositiveHom_injective (K : Type) [Field K] [CharP K 2] :
    Function.Injective (fixedPositiveHom K) := by
  intro g h he
  exact matrixHom_injective K (congrArg Subtype.val he)

def originalHom (K : Type) [Field K] [Finite K] [CharP K 2]
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K)] :
    Radical K →* CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K :=
  (fixedPositiveToOriginal K 2).comp (fixedPositiveHom K)

theorem originalHom_injective (K : Type) [Field K] [Finite K] [CharP K 2]
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K)] :
    Function.Injective (originalHom K) :=
  (fixedPositiveToOriginal_injective K 2).comp (fixedPositiveHom_injective K)

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalEmbedding
