import SymmetricSubgroupAsymptotics.ScalarFourCentralC4RetainedCentralImage
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4ActiveQuotientCubic
import SymmetricSubgroupAsymptotics.C4CoordinateSurjectiveQuotient

/-! Actual central-repeat coordinates survive every quotient retaining the
original finite top. Both ranks decrease, on the same quotient map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H] [Finite Q] [Finite H] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)
  (f : Q →* H) (hf : Function.Surjective f) (hker : f.ker≤D.top.ker)
  (n : Q) (hn : D.top n=D.cubic)

def retainedCentralProjection : D.active.ker →*
    (D.descendedActive f hf hker n hn).ker where
  toFun z := ⟨D.quotientKernelProjection f hf hker (z : D.top.ker),by
    change D.descendedActive f hf hker n hn
      (D.quotientKernelProjection f hf hker (z : D.top.ker))=1
    rw [D.descendedActive_projection]
    apply (D.quotientActive_eq_one_iff (D.normalActiveImage f n hn) _).mpr
    have hz : D.fieldActive (z : D.top.ker)=1 := by
      change ScalarFourQuadraticField.tupleEquivalence d (D.active (z : D.top.ker))=1
      rw [z.property,map_one]
    refine ⟨1,Subgroup.one_mem _,?_⟩
    rw [map_one,hz]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' z w := by apply Subtype.ext; exact map_mul _ _ _

theorem retainedCentralProjection_surjective :
    Function.Surjective (D.retainedCentralProjection f hf hker n hn) := by
  intro y
  obtain ⟨z,hz⟩ := D.retained_central_image f hf hker n hn y y.property
  exact ⟨z,Subtype.ext hz⟩

include D f hf hker n hn

/-- The actual quotient has bounded central and active ranks, derived from
original maps and actual scalar quotient bases. -/
theorem retained_quotient_coordinates : ∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
    Nonempty (ScalarFourCentralC4TopCoordinates H T c' d') := by
  obtain ⟨c',hc',e,he⟩ := C4CoordinateSurjectiveQuotient.exists_embedding
    D.centralCoordinates D.centralCoordinates_injective
    (D.retainedCentralProjection f hf hker n hn)
    (D.retainedCentralProjection_surjective f hf hker n hn)
  refine ⟨c',D.activeQuotientRank (D.normalActiveImage f n hn),hc',
    D.activeQuotientRank_le _,⟨?_⟩⟩
  exact
    { top := D.quotientTop f hf hker
      top_surjective := by
        intro t
        obtain ⟨g,rfl⟩ := D.top_surjective t
        exact ⟨f g,D.quotientTop_apply f hf hker g⟩
      cubic := D.cubic
      active := D.descendedActive f hf hker n hn
      central := D.retained_central_commutes f hf hker n hn
      centralCoordinates := e
      centralCoordinates_injective := he
      cubic_action := by
        intro v hv k j
        obtain ⟨g,rfl⟩ := hf v
        obtain ⟨l,rfl⟩ := D.quotientKernelProjection_surjective f hf hker k
        have hg : D.top g=D.cubic :=
          (D.quotientTop_apply f hf hker g).symm.trans hv
        have he : MulAut.conjNormal (f g) (D.quotientKernelProjection f hf hker l)=
            D.quotientKernelProjection f hf hker (MulAut.conjNormal g l) := by
          apply Subtype.ext
          change f g*f (l : Q)*(f g)⁻¹=f (g*(l : Q)*g⁻¹)
          rw [map_mul,map_mul,map_inv]
        rw [he,D.descendedActive_projection,D.descendedActive_projection]
        exact D.quotientActive_cubic (D.normalActiveImage f n hn) g hg l j }

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
