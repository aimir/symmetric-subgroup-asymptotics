import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeisenbergPilot
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPositive
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveProjection

/-! The four diagram-fixed complementary pairs give an actual standard
Heisenberg subgroup of the original F4 model. The normalized negative Y
parameters retain the integral pair signs, including in characteristic
two. Fixedness is proved for every parameter before taking products. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergEmbedding
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalHeisenbergRootRelations
open CFSGExceptionalHeisenbergProduct CFSGExceptionalHeisenbergPositive
open CFSGFiniteCommutingParameterHom CFSGHeisenbergCoordinateGroup
open CFSGFFourE6FixedHeisenbergPilot CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGFFourE6FixedPositiveProjection
local instance fFourHeisEmbeddingRootsDecidableEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem parameterHom_fixed {K G : Type*} [AddCommGroup K] [Group G] {n : ℕ}
    (f : Fin n → Multiplicative K →* G)
    (hc : Pairwise (fun i j => ∀ a b, Commute (f i a) (f j b)))
    (tau : MulAut G) (hf : ∀ i a, tau (f i a) = f i a) (v : Fin n → K) :
    tau (parameterHom f hc (Multiplicative.ofAdd v)) =
      parameterHom f hc (Multiplicative.ofAdd v) := by
  simp only [parameterHom_apply, map_list_prod, List.map_ofFn, Function.comp_def, hf]

theorem firstProduct_fixed (K : Type) [Field K] [Finite K] (v : Fin 4 → K) :
    unitTwist K (RingEquiv.refl K) (X A hd hs hp ho configuration K (Multiplicative.ofAdd v)) =
      X A hd hs hp ho configuration K (Multiplicative.ofAdd v) := by
  have hc : Pairwise (fun i j => ∀ a b,
      Commute (xHom A hd hs hp ho configuration K i a)
        (xHom A hd hs hp ho configuration K j b)) := by
    intro i j _ a b
    exact x_commute A hd hs hp ho configuration K i j a.toAdd b.toAdd
  apply parameterHom_fixed (xHom A hd hs hp ho configuration K) hc
  intro i a
  exact selected_fixed_parameter K ⟨(configuration.xRoot i).val, configuration.positive_x i⟩
    (diagram_first i) a.toAdd

theorem secondProduct_fixed (K : Type) [Field K] [Finite K] (v : Fin 4 → K) :
    unitTwist K (RingEquiv.refl K) (Y A hd hs hp ho configuration K (Multiplicative.ofAdd v)) =
      Y A hd hs hp ho configuration K (Multiplicative.ofAdd v) := by
  have hc : Pairwise (fun i j => ∀ a b,
      Commute (yNegative A hd hs hp ho configuration K i a)
        (yNegative A hd hs hp ho configuration K j b)) := by
    intro i j _ a b
    exact y_commute A hd hs hp ho configuration K i j (-a.toAdd) (-b.toAdd)
  apply parameterHom_fixed (yNegative A hd hs hp ho configuration K) hc
  intro i a
  exact selected_fixed_parameter K ⟨(configuration.yRoot i).val, configuration.positive_y i⟩
    (diagram_second i) (((pairSign A hd hs hp ho configuration i : ℤ) : K) * (-a.toAdd))

theorem centralParameter_fixed (K : Type) [Field K] [Finite K] (c : Multiplicative K) :
    unitTwist K (RingEquiv.refl K) (zHom A hd hs hp ho configuration K c) =
      zHom A hd hs hp ho configuration K c :=
  selected_fixed_parameter K ⟨configuration.zRoot.val, configuration.positive_z⟩
    diagram_central c.toAdd

def matrixHom (K : Type) [Field K] : Element K 4 →* (Matrix GeckIndex GeckIndex K)ˣ :=
  rawHom A hd hs hp ho configuration K

theorem matrixHom_injective (K : Type) [Field K] : Function.Injective (matrixHom K) :=
  rawHom_injective A hd hs hp ho configuration K

theorem matrixHom_mem_positive (K : Type) [Field K] (g : Element K 4) :
    matrixHom K g ∈ Positive K :=
  rawHom_mem_positive A hd hs hp ho configuration K g

private theorem map_three {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b c : G) : f (a * b * c) = f a * f b * f c := by
  rw [map_mul, map_mul]

theorem matrixHom_fixed (K : Type) [Field K] [Finite K] (g : Element K 4) :
    unitTwist K (RingEquiv.refl K) (matrixHom K g) = matrixHom K g := by
  have hm := map_three (unitTwist K (RingEquiv.refl K)).toMonoidHom
    (X A hd hs hp ho configuration K (Multiplicative.ofAdd g.a))
    (Y A hd hs hp ho configuration K (Multiplicative.ofAdd g.b))
    (zHom A hd hs hp ho configuration K (Multiplicative.ofAdd g.c))
  simp only [MulEquiv.coe_toMonoidHom] at hm
  change unitTwist K (RingEquiv.refl K)
      (X A hd hs hp ho configuration K (Multiplicative.ofAdd g.a) *
        Y A hd hs hp ho configuration K (Multiplicative.ofAdd g.b) *
        zHom A hd hs hp ho configuration K (Multiplicative.ofAdd g.c)) = _
  calc
    _ = unitTwist K (RingEquiv.refl K)
          (X A hd hs hp ho configuration K (Multiplicative.ofAdd g.a)) *
        unitTwist K (RingEquiv.refl K)
          (Y A hd hs hp ho configuration K (Multiplicative.ofAdd g.b)) *
        unitTwist K (RingEquiv.refl K)
          (zHom A hd hs hp ho configuration K (Multiplicative.ofAdd g.c)) := hm
    _ = matrixHom K g := congrArg₂
      (fun a b : (Matrix GeckIndex GeckIndex K)ˣ => a * b)
      (congrArg₂ (fun a b : (Matrix GeckIndex GeckIndex K)ˣ => a * b)
        (firstProduct_fixed K g.a) (secondProduct_fixed K g.b))
      (centralParameter_fixed K (Multiplicative.ofAdd g.c))

def fixedPositiveHom (K : Type) [Field K] [Finite K] :
    Element K 4 →* signedFixed K (RingEquiv.refl K) false :=
  (matrixHom K).codRestrict (signedFixed K (RingEquiv.refl K) false)
    (fun g => ⟨matrixHom_mem_positive K g, matrixHom_fixed K g⟩)

theorem fixedPositiveHom_injective (K : Type) [Field K] [Finite K] :
    Function.Injective (fixedPositiveHom K) := by
  intro g h he
  exact matrixHom_injective K (congrArg Subtype.val he)

def originalHom (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K)] :
    Element K 4 →* CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K :=
  (fixedPositiveToOriginal K p).comp (fixedPositiveHom K)

theorem originalHom_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K)] :
    Function.Injective (originalHom K p) :=
  (fixedPositiveToOriginal_injective K p).comp (fixedPositiveHom_injective K)

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergEmbedding
