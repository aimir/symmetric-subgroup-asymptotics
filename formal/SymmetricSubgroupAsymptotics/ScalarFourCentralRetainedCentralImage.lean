import SymmetricSubgroupAsymptotics.ScalarFourCentralRetainedTopDescent

/-! The retained quotient's central kernel is the image of the ORIGINAL
central kernel. This is an exact image statement for the same denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)
  (f : Q →* H) (hf : Function.Surjective f) (hker : f.ker≤D.top.ker)
  (n : Q) (hn : D.top n=D.cubic)

theorem retained_central_image (y : (D.quotientTop f hf hker).ker)
    (hy : D.descendedActive f hf hker n hn y=1) :
    ∃ z : D.active.ker, D.quotientKernelProjection f hf hker (z : D.top.ker)=y := by
  obtain ⟨k,rfl⟩ := D.quotientKernelProjection_surjective f hf hker y
  rw [D.descendedActive_projection] at hy
  have hk := (D.quotientActive_eq_one_iff (D.normalActiveImage f n hn) k).mp hy
  obtain ⟨l,hl,he⟩ := hk
  have hal : D.active l=D.active k := by
    apply (ScalarFourQuadraticField.tupleEquivalence d).injective
    apply Multiplicative.toAdd.injective
    exact he
  have hfl : f (l : Q)=1 := hl
  refine ⟨⟨k*l⁻¹,?_⟩,?_⟩
  · change D.active (k*l⁻¹)=1
    rw [map_mul,map_inv,hal,mul_inv_cancel]
  · apply Subtype.ext
    change f ((k : Q)*(l : Q)⁻¹)=f (k : Q)
    rw [map_mul,map_inv,hfl,inv_one,mul_one]

theorem retained_central_commutes (y : (D.descendedActive f hf hker n hn).ker)
    (h : H) : (((y : (D.quotientTop f hf hker).ker) : H))*h=
      h*(((y : (D.quotientTop f hf hker).ker) : H)) := by
  obtain ⟨z,hz⟩ := D.retained_central_image f hf hker n hn y y.property
  obtain ⟨g,rfl⟩ := hf h
  have hz' := congrArg Subtype.val hz
  change f (((z : D.top.ker) : Q))=(y : H) at hz'
  rw [← hz',← map_mul,← map_mul,D.central z g]

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
