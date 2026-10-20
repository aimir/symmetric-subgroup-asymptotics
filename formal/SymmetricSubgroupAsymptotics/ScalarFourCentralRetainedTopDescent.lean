import SymmetricSubgroupAsymptotics.ScalarFourCentralActiveQuotientCoordinates

/-! The retained-top branch descends through the same actual quotient map.
The kernel map is onto, and scalar coordinates kill exactly the actual
normal active image rather than an assumed proxy denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open BinaryQuadraticField
variable {Q T H : Type} [Group Q] [Group T] [Group H] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)
  (f : Q →* H) (hf : Function.Surjective f) (hker : f.ker≤D.top.ker)

def quotientTop : H →* T := f.liftOfSurjective hf ⟨D.top,hker⟩

@[simp] theorem quotientTop_apply (g : Q) : D.quotientTop f hf hker (f g)=D.top g := by
  simp only [quotientTop,MonoidHom.liftOfSurjective,MonoidHom.liftOfRightInverse_comp_apply]

def quotientKernelProjection : D.top.ker →* (D.quotientTop f hf hker).ker where
  toFun k := ⟨f (k : Q),by
    change D.quotientTop f hf hker (f (k : Q))=1
    rw [D.quotientTop_apply f hf hker]
    exact k.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' k l := Subtype.ext (f.map_mul (k : Q) (l : Q))

theorem quotientKernelProjection_surjective :
    Function.Surjective (D.quotientKernelProjection f hf hker) := by
  rintro ⟨h,hh⟩
  obtain ⟨g,rfl⟩ := hf h
  have hg : D.top g=1 := by rw [← D.quotientTop_apply f hf hker g]; exact hh
  exact ⟨⟨g,hg⟩,rfl⟩

variable (n : Q) (hn : D.top n=D.cubic)

def normalActiveImage : Submodule Scalar (Fin d → Scalar) :=
  D.scalarActiveImage (f.ker.subgroupOf D.top.ker) n hn
    (fun k hk => D.original_normal_cubic_stable f.ker n k hk)

theorem projection_ker_le_quotientActive_ker :
    (D.quotientKernelProjection f hf hker).ker ≤
      (D.quotientActive (D.normalActiveImage f n hn)).ker := by
  intro k hk
  apply (D.quotientActive_eq_one_iff (D.normalActiveImage f n hn) k).mpr
  refine ⟨k,?_,rfl⟩
  change f (k : Q)=1
  exact congrArg Subtype.val hk

/-- The new active map is on the actual kernel of the actual quotient top. -/
def descendedActive : (D.quotientTop f hf hker).ker →*
    (Fin (D.activeQuotientRank (D.normalActiveImage f n hn)) → ScalarFour) :=
  (D.quotientKernelProjection f hf hker).liftOfSurjective
    (D.quotientKernelProjection_surjective f hf hker)
    ⟨D.quotientActive (D.normalActiveImage f n hn),
      D.projection_ker_le_quotientActive_ker f hf hker n hn⟩

@[simp] theorem descendedActive_projection (k : D.top.ker) :
    D.descendedActive f hf hker n hn (D.quotientKernelProjection f hf hker k)=
      D.quotientActive (D.normalActiveImage f n hn) k := by
  simp only [descendedActive,MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
