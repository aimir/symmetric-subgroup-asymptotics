import SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates

/-! Killing an actual cubic lift forces the image of the original top
kernel into the image of the original central kernel. This retains the
same quotient homomorphism and does not assume a split extension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

private theorem twist_difference (x : ScalarFour) :
    scalarFourTwist 1 (scalarFourTwist 1 x)*(scalarFourTwist 1 x)⁻¹=x := by
  revert x
  decide +kernel

/-- Every original kernel element has the same quotient image as an actual
original central element, whenever that quotient kills a cubic lift. -/
theorem kernel_image_central (f : Q →* H) (n : Q)
    (hn : D.top n=D.cubic) (hfn : f n=1) (k : D.top.ker) :
    ∃ z : D.active.ker, f ((z : D.top.ker) : Q)=f (k : Q) := by
  let a : D.top.ker := MulAut.conjNormal n k
  let w : D.top.ker := MulAut.conjNormal n a*a⁻¹
  have hw : D.active w=D.active k := by
    funext j
    change D.active (MulAut.conjNormal n a*a⁻¹) j=D.active k j
    rw [map_mul,map_inv]
    change D.active (MulAut.conjNormal n a) j*(D.active a j)⁻¹=D.active k j
    rw [D.cubic_action n hn a j]
    change scalarFourTwist 1 (D.active (MulAut.conjNormal n k) j)*
      (D.active (MulAut.conjNormal n k) j)⁻¹=D.active k j
    rw [D.cubic_action n hn k j]
    exact twist_difference (D.active k j)
  have hfw : f (w : Q)=1 := by
    change f (n*(a : Q)*n⁻¹*(a : Q)⁻¹)=1
    simp only [map_mul,map_inv,hfn,inv_one,one_mul,mul_one,mul_inv_cancel]
  refine ⟨⟨k*w⁻¹,?_⟩,?_⟩
  · change D.active (k*w⁻¹)=1
    rw [map_mul,map_inv,hw,mul_inv_cancel]
  · change f ((k : Q)*(w : Q)⁻¹)=f (k : Q)
    rw [map_mul,map_inv,hfw,inv_one,mul_one]

/-- In the same actual quotient, the whole original top-kernel image is
central. No assertion about other normal denominators is used. -/
theorem kernel_image_commutes (f : Q →* H) (n : Q)
    (hn : D.top n=D.cubic) (hfn : f n=1) (k : D.top.ker) (g : Q) :
    f (k : Q)*f g=f g*f (k : Q) := by
  obtain ⟨z,hz⟩ := D.kernel_image_central f n hn hfn k
  rw [← hz,← map_mul,← map_mul,D.central z g]

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
