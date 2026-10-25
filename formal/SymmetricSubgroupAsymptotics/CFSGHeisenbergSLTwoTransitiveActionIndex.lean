import SymmetricSubgroupAsymptotics.CFSGHeisenbergTransitiveActionIndex
import SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoStabilizers

/-! Literal SL2 transitivity pays the dimension-one Heisenberg tail.
The quotient action is constructed from the supplied actual automorphism
homomorphism and its proved coordinate formula. Both index factors still
come from the SAME subgroup; no field-linearity of its image is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoTransitiveActionIndex
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSLTwoStabilizers CFSGTypeASLTwoWeyl
variable {K : Type*} [Field K]

private def sectionElement (v : (Fin 1 → K) × (Fin 1 → K)) : Element K 1 :=
  ⟨v.1,v.2,0⟩

private theorem coordinates_eq_of_coordinateVector_eq (g h : Element K 1)
    (he : coordinateVector g=coordinateVector h) : (g.a,g.b)=(h.a,h.b) := by
  apply Prod.ext
  · funext i
    fin_cases i
    exact congrFun he 0
  · funext i
    fin_cases i
    exact congrFun he 1

private def act (φ : SL2 (F := K) →* MulAut (Element K 1))
    (A : SL2 (F := K)) (v : (Fin 1 → K) × (Fin 1 → K)) :=
  ((φ A (sectionElement v)).a,(φ A (sectionElement v)).b)

private theorem act_coordinates (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g)=(A⁻¹).transpose.toLin' (coordinateVector g))
    (A : SL2 (F := K)) (g : Element K 1) :
    ((φ A g).a,(φ A g).b)=act φ A (g.a,g.b) := by
  apply coordinates_eq_of_coordinateVector_eq
  rw [hφ,hφ]
  rfl

private def vectorAction (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g)=(A⁻¹).transpose.toLin' (coordinateVector g)) :
    MulAction (SL2 (F := K)) ((Fin 1 → K) × (Fin 1 → K)) where
  smul := act φ
  one_smul v := by
    change ((φ 1 (sectionElement v)).a,(φ 1 (sectionElement v)).b)=v
    rw [map_one]
    rfl
  mul_smul A B v := by
    change ((φ (A*B) (sectionElement v)).a,(φ (A*B) (sectionElement v)).b)=
      act φ A ((φ B (sectionElement v)).a,(φ B (sectionElement v)).b)
    rw [map_mul]
    exact act_coordinates φ hφ A (φ B (sectionElement v))

private theorem section_vector_ne_zero (v : (Fin 1 → K) × (Fin 1 → K)) (hv : v ≠ 0) :
    coordinateVector (sectionElement v) ≠ 0 := by
  intro he
  apply hv
  apply Prod.ext
  · funext i
    fin_cases i
    exact congrFun he 0
  · funext i
    fin_cases i
    exact congrFun he 1

theorem prime_mul_field_square_le_index [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g)=(A⁻¹).transpose.toLin' (coordinateVector g))
    (M : Subgroup (Element K 1 ⋊[φ] SL2 (F := K)))
    (hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl) :
    p*Nat.card K^2 ≤ M.index := by
  letI : MulAction (SL2 (F := K)) ((Fin 1 → K) × (Fin 1 → K)) := vectorAction φ hφ
  have hzero (A : SL2 (F := K)) : A • (0 : (Fin 1 → K) × (Fin 1 → K))=0 := by
    change ((φ A 1).a,(φ A 1).b)=0
    rw [map_one]
    rfl
  have ht (v w : (Fin 1 → K) × (Fin 1 → K)) (hv : v ≠ 0) (hw : w ≠ 0) :
      ∃ A : SL2 (F := K), A • v=w := by
    obtain ⟨B,hB⟩ := CFSGTypeAVectorTransitivity.exists_map_nonzero
      (0 : Fin 2) 1 (by decide) (coordinateVector (sectionElement v))
      (coordinateVector (sectionElement w)) (section_vector_ne_zero v hv)
      (section_vector_ne_zero w hw)
    let A : SL2 (F := K) := B.transpose⁻¹
    have hA : (A⁻¹).transpose=B := by
      change ((B.transpose⁻¹)⁻¹).transpose=B
      rw [inv_inv]
      apply Subtype.ext
      exact Matrix.transpose_transpose B.val
    refine ⟨A,?_⟩
    change ((φ A (sectionElement v)).a,(φ A (sectionElement v)).b)=
      ((sectionElement w).a,(sectionElement w).b)
    apply coordinates_eq_of_coordinateVector_eq
    rw [hφ,hA,hB]
  simpa only [Nat.mul_one] using
    CFSGHeisenbergTransitiveActionIndex.prime_mul_field_power_le_index φ p hzero ht
      (act_coordinates φ hφ) M hcentre

theorem degree_le_of_central_motion [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (φ : SL2 (F := K) →* MulAut (Element K 1))
    (hφ : ∀ A g, coordinateVector (φ A g)=(A⁻¹).transpose.toLin' (coordinateVector g))
    {X : Type*} [Finite X] [MulAction (Element K 1 ⋊[φ] SL2 (F := K)) X]
    (x : X) (c : Multiplicative K)
    (hc : (SemidirectProduct.inl (central c) : Element K 1 ⋊[φ] SL2 (F := K)) • x ≠ x) :
    p*Nat.card K^2 ≤ Nat.card X := by
  let M := MulAction.stabilizer (Element K 1 ⋊[φ] SL2 (F := K)) x
  have hcentre : ¬(central (K := K) (m := 1)).range ≤ M.comap SemidirectProduct.inl := by
    intro hh
    exact hc (hh ⟨c,rfl⟩)
  exact (prime_mul_field_square_le_index p φ hφ M hcentre).trans
    ((MulAction.index_stabilizer _ _).trans_le (Set.ncard_le_card _))

end SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoTransitiveActionIndex
