import SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates

/-! Coordinate structures pull back along a faithful ORIGINAL group map
whose retained top is still onto. No normal-generator or source-count
bound is inherited from an arbitrary ambient subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates

variable {Q H T : Type} [Group Q] [Group H] [Group T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d) (f : H →* Q)

private def pullKernel : (D.top.comp f).ker →* D.top.ker where
  toFun k := ⟨f k.val,k.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' a b := Subtype.ext (f.map_mul a.val b.val)

private theorem pullKernel_injective (hf : Function.Injective f) :
    Function.Injective (pullKernel D f) := by
  intro x y h
  apply Subtype.ext
  apply hf
  exact congrArg (fun z : D.top.ker => (z : Q)) h

private def pullActiveKernel : (D.active.comp (pullKernel D f)).ker →* D.active.ker where
  toFun z := ⟨pullKernel D f z.val,z.property⟩
  map_one' := Subtype.ext (pullKernel D f).map_one
  map_mul' a b := Subtype.ext ((pullKernel D f).map_mul a.val b.val)

private theorem pullActiveKernel_injective (hf : Function.Injective f) :
    Function.Injective (pullActiveKernel D f) := by
  intro x y h
  apply Subtype.ext
  apply pullKernel_injective D f hf
  exact congrArg (fun z : D.active.ker => (z : D.top.ker)) h

/-- Restrict actual coordinates through a faithful map and retain their
actual composite top; all kernel maps are literal restrictions of f. -/
def ofInjective (hf : Function.Injective f)
    (htop : Function.Surjective (D.top.comp f)) :
    ScalarFourCentralTopCoordinates H T c d where
  top := D.top.comp f
  top_surjective := htop
  cubic := D.cubic
  active := D.active.comp (pullKernel D f)
  central := by
    intro z g
    apply hf
    rw [map_mul,map_mul]
    exact D.central (pullActiveKernel D f z) (f g)
  centralCoordinates := D.centralCoordinates.comp (pullActiveKernel D f)
  centralCoordinates_injective :=
    D.centralCoordinates_injective.comp (pullActiveKernel_injective D f hf)
  cubic_action := by
    intro v hv k j
    have he : pullKernel D f (MulAut.conjNormal v k)=
        MulAut.conjNormal (f v) (pullKernel D f k) := by
      apply Subtype.ext
      change f (v*k.val*v⁻¹)=f v*f k.val*(f v)⁻¹
      rw [map_mul,map_mul,map_inv]
    change D.active (pullKernel D f (MulAut.conjNormal v k)) j=
      scalarFourTwist 1 (D.active (pullKernel D f k) j)
    rw [he]
    exact D.cubic_action (f v) hv (pullKernel D f k) j

@[simp] theorem ofInjective_top (hf : Function.Injective f)
    (htop : Function.Surjective (D.top.comp f)) :
    (D.ofInjective f hf htop).top=D.top.comp f := rfl

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
