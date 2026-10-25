import SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphCentralLayers

/-! The actual graph's central chart is reordered into the standard
quadratic point coordinates. Both its covariance and its kernel in the
actual eight-dimensional vector quotient are proved literally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphPointLayers
open CFSGFFourBinaryLeviConjugationGraph CFSGFFourBinaryGraphCentralLayers
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourBinaryRadicalCentralLayers
open CFSGSymplecticBinaryPointTailAction CFSGFFourBinaryNativeCentralAction
local instance fFourGraphPointRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K=2)

private theorem equiv_center {R S : Type} [Group R] [Group S]
    (e : R ≃* S) (c : R) (hc : ∀ r, r*c=c*r) : e c ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro n
  obtain ⟨r,rfl⟩ := e.surjective n
  simpa only [map_mul] using congrArg e (hc r)

private theorem transport_exact {R S Z T V : Type}
    [Group R] [Group S] [Group Z] [Group T] [Group V]
    (e : R ≃* S) (f : Z →* R) (t : T ≃* Z) (π : R →* V)
    (hexact : f.range=π.ker) :
    ((e.toMonoidHom.comp f).comp t.toMonoidHom).range =
      (π.comp e.symm.toMonoidHom).ker := by
  apply Subgroup.ext
  intro n
  constructor
  · rintro ⟨a,rfl⟩
    change π (e.symm (e (f (t a))))=1
    rw [e.symm_apply_apply]
    have ha : f (t a) ∈ f.range := ⟨t a,rfl⟩
    rw [hexact] at ha
    exact ha
  · intro hn
    have hr : e.symm n ∈ π.ker := hn
    rw [←hexact] at hr
    obtain ⟨z,hz⟩ := hr
    refine ⟨t.symm z,?_⟩
    change e (f (t (t.symm z)))=n
    rw [t.apply_symm_apply,hz]
    exact e.apply_symm_apply n

abbrev Point := BinaryQuadraticLiftAction.Coordinates (K := K) (I := Fin 3)

def pointEquiv : Multiplicative (Point K) ≃* CentralCoordinates K :=
  AddEquiv.toMultiplicative (LinearEquiv.prodComm K ((Fin 3 → K) × (Fin 3 → K)) K).toAddEquiv

def pointLift : Multiplicative (Point K) →* liftedRadical K hK :=
  (centralLift K hK).comp (pointEquiv K).toMonoidHom

theorem pointLift_injective : Function.Injective (pointLift K hK) :=
  (centralLift_injective K hK).comp (pointEquiv K).injective

theorem pointLift_central (z : Multiplicative (Point K)) :
    pointLift K hK z ∈ Subgroup.center (liftedRadical K hK) :=
  equiv_center (radicalEquiv K hK) (centralCoordinates K (pointEquiv K z))
    (fun r => (centralCoordinates_commute K (pointEquiv K z) r).symm.eq)

def vectorAction : Graph K hK →*
    (((Fin 3 → K) × (Fin 3 → K)) ≃ₗ[K] ((Fin 3 → K) × (Fin 3 → K))) :=
  (vectorLinearHom K 3).comp (first K hK)

theorem vectorAction_polar (p : Graph K hK) (v w : (Fin 3 → K) × (Fin 3 → K)) :
    BinaryQuadraticRefinementTransvections.polar (vectorAction K hK p v)
      (vectorAction K hK p w) = BinaryQuadraticRefinementTransvections.polar v w :=
  vectorLinearHom_preserves_polar K 3 (first K hK p) v w

theorem pointLift_covariance (p : Graph K hK) (a : Point K) :
    pointLift K hK (Multiplicative.ofAdd
      (BinaryQuadraticLiftAction.liftHom hK (vectorAction K hK)
        (vectorAction_polar K hK) p a)) =
      MulAut.conjNormal p (pointLift K hK (Multiplicative.ofAdd a)) := by
  have he : pointEquiv K (Multiplicative.ofAdd
      (BinaryQuadraticLiftAction.liftHom hK (vectorAction K hK)
        (vectorAction_polar K hK) p a)) =
      nativeCentralAction K hK (first K hK p) (pointEquiv K (Multiplicative.ofAdd a)) := rfl
  exact (congrArg (centralLift K hK) he).trans
    (centralLift_covariance K hK p (pointEquiv K (Multiplicative.ofAdd a)))

def vectorMap : liftedRadical K hK →*
    Multiplicative ((Fin 4 → K) × (Fin 4 → K)) :=
  (vectorProjection K).comp (radicalEquiv K hK).symm.toMonoidHom

private theorem source_vector_surjective : Function.Surjective (vectorProjection K) := by
  intro v
  obtain ⟨g,hg⟩ := CFSGHeisenbergCoordinateGroup.projection_surjective (K := K) (m := 4) v
  exact ⟨(g,1),hg⟩

theorem vectorMap_surjective : Function.Surjective (vectorMap K hK) :=
  (source_vector_surjective K).comp (radicalEquiv K hK).symm.surjective

theorem pointLift_range_eq_kernel : (pointLift K hK).range=(vectorMap K hK).ker :=
  transport_exact (radicalEquiv K hK) (centralCoordinates K) (pointEquiv K)
    (vectorProjection K) (vectorProjection_ker K).symm

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphPointLayers
