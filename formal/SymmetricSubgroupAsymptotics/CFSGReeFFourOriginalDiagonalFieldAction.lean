import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalization
import SymmetricSubgroupAsymptotics.CFSGReeFFourTorusScalarCoordinates
import SymmetricSubgroupAsymptotics.CFSGSemilinearConjugationCharacters

/-! The actual original diagonal action transports its two scalar
characters by the two fields in a normalized positive-layer description.
The image torus word is obtained from intrinsic diagonal invariance. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalFieldAction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalPairDiagonal CFSGReeFFourOriginalPositiveNormalization
open CFSGReeFFourOriginalOuterSemilinear CFSGReeFFourOriginalMiddleSemilinear
open CFSGReeFFourFixedOuterTorusAction CFSGReeFFourFixedMiddleTorusAction
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourFixedDiagonalCardinality
open CFSGReeFFourOuterTorusAction
open CFSGReeFFourTorusScalarCoordinates CFSGSemilinearConjugationCharacters

private theorem first_torus (m : ℕ) (hm : 0<m) (s : (Field m)ˣ)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    CFSGSuzukiUnipotent.firstParameter m (CFSGSuzukiUnipotent.torusAutHom m s⁻¹ x)=
      (s : Field m)*CFSGSuzukiUnipotent.firstParameter m x := by
  have he := CFSGSuzukiUnipotent.firstLayerAddAut_first m hm
    (CFSGSuzukiUnipotent.torusAutHom m s⁻¹) x
  change CFSGSuzukiUnipotent.firstLayerAutHom m hm
    (CFSGSuzukiUnipotent.torusAutHom m s⁻¹) (CFSGSuzukiUnipotent.firstParameter m x)=_ at he
  rw [CFSGSuzukiUnipotent.firstLayer_torusAut,inv_inv] at he
  exact he.symm

theorem outer_character_of_torus_image (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (htau : ∀x : Field m,outerAction m hm f x=tau x)
    (a b c d : (Field m)ˣ)
    (himage : f.val (fixedToOriginal m hm (fixedTorus m a b))=
      fixedToOriginal m hm (fixedTorus m c d)) :
    outerScalar m c d=Units.map tau.toMonoidHom (outerScalar m a b) := by
  let i : Field m→CFSG.Models.ReeF4 m :=
    fun x=>originalOuterHom m hm (Multiplicative.ofAdd x)
  have hi : Function.Injective i := by
    intro x y he
    exact congrArg Multiplicative.toAdd (originalOuterHom_injective m hm he)
  apply Units.ext
  exact character_eq_of_semilinear_conjugation i hi f.val (outerAction m hm f)
    (fun x=>(outerScalar m a b : Field m)*x) (fun x=>(outerScalar m c d : Field m)*x)
    (fixedToOriginal m hm (fixedTorus m a b)) id tau.toRingHom
    (outerScalar m a b : Field m) (outerScalar m c d : Field m)
    (outerRestriction_intertwines m hm f)
    (fun x=>by simpa only [mul_comm] using (original_fixed_torus_outer_action m hm a b x).symm)
    (fun x=>by rw [himage];simpa only [mul_comm] using
      (original_fixed_torus_outer_action m hm c d x).symm)
    htau (fun _=>rfl) (fun _=>rfl) 1 rfl

theorem middle_character_of_torus_image (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (nu : Field m ≃+* Field m)
    (hnu : ∀x : CFSGSuzukiUnipotent.unipotentSubgroup m,
      CFSGSuzukiUnipotent.firstParameter m (middleAction m hm f x)=
        nu (CFSGSuzukiUnipotent.firstParameter m x))
    (a b c d : (Field m)ˣ)
    (himage : f.val (fixedToOriginal m hm (fixedTorus m a b))=
      fixedToOriginal m hm (fixedTorus m c d)) :
    middleScalar m c d=Units.map nu.toMonoidHom (middleScalar m a b) := by
  apply Units.ext
  exact character_eq_of_semilinear_conjugation (originalMiddleEmbedding m hm)
    (originalMiddleEmbedding_injective m hm) f.val (middleAction m hm f)
    (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m a b)⁻¹)
    (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m c d)⁻¹)
    (fixedToOriginal m hm (fixedTorus m a b)) (CFSGSuzukiUnipotent.firstParameter m)
    nu.toRingHom (middleScalar m a b : Field m) (middleScalar m c d : Field m)
    (middleRestriction_embedding m hm f) (original_fixed_torus_middle_action m hm a b)
    (fun x=>by rw [himage];exact original_fixed_torus_middle_action m hm c d x)
    hnu (first_torus m hm _) (first_torus m hm _)
    (CFSGSuzukiUnipotent.coordinateElement m 1 0) rfl

theorem exists_torus_image_scalarPair (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau nu : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau nu)
    (a b : (Field m)ˣ) : ∃c d : (Field m)ˣ,
      f.val (fixedToOriginal m hm (fixedTorus m a b))=fixedToOriginal m hm (fixedTorus m c d) ∧
      scalarPair m (c,d)=SemilinearScalarPairRigidity.diagonalAction tau nu (scalarPair m (a,b)) := by
  have hD : fixedToOriginal m hm (fixedTorus m a b)∈originalDiagonal m hm := by
    rw [←fixedDiagonal_map_originalDiagonal]
    exact ⟨fixedTorus m a b,fixedTorus_mem_diagonal m a b,rfl⟩
  have hF : f.val (fixedToOriginal m hm (fixedTorus m a b))∈originalDiagonal m hm := by
    rw [←originalDiagonal_map_pair m hm f]
    exact ⟨_,hD,rfl⟩
  obtain ⟨c,d,he⟩ := exists_originalDiagonal_torus m hm _ hF
  refine ⟨c,d,he,Prod.ext ?_ ?_⟩
  · exact outer_character_of_torus_image m hm f tau hfields.1 a b c d he
  · exact middle_character_of_torus_image m hm f nu hfields.2 a b c d he

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalFieldAction
