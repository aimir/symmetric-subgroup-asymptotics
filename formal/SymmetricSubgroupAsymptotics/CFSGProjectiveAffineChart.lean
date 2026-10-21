import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates

/-! The literal affine chart [1:v] in the original coordinate projective space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
variable {F n : Type*} [Field F]

abbrev Vector := (Unit⊕n)→F
abbrev Point := Projectivization F (Vector (F:=F) (n:=n))

def vector (v : n→F) : Vector (F:=F) (n:=n) := Sum.elim (fun _ => 1) v

@[simp] theorem vector_zeroCoord (v : n→F) : vector v (Sum.inl ())=1 := rfl
@[simp] theorem vector_coord (v : n→F) (i : n) : vector v (Sum.inr i)=v i := rfl

theorem vector_ne_zero (v : n→F) : vector v≠0 := by
  intro he
  have hh := congrArg (fun w : Vector (F:=F) (n:=n) => w (Sum.inl ())) he
  exact one_ne_zero hh

def point (v : n→F) : Point (F:=F) (n:=n) :=
  Projectivization.mk F (vector v) (vector_ne_zero v)

theorem point_injective : Function.Injective (point (F:=F) (n:=n)) := by
  intro v w he
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he
  have hc1 : (c:F)=1 := by
    simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul,vector_zeroCoord,mul_one] using
      congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inl ())) hc
  funext i
  have hi := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr i)) hc
  simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul,vector_coord,hc1,one_mul] using hi.symm

def infinity : Submodule F (Vector (F:=F) (n:=n)) :=
  LinearMap.ker (LinearMap.proj (Sum.inl ()))

@[simp] theorem mem_infinity (v : Vector (F:=F) (n:=n)) :
    v∈infinity (F:=F) (n:=n)↔v (Sum.inl ())=0 := Iff.rfl

theorem mem_projective_infinity (p : Point (F:=F) (n:=n)) :
    p∈(infinity (F:=F) (n:=n)).projectivization↔p.rep (Sum.inl ())=0 := by
  rw [Submodule.mem_projectivization_iff_submodule_le,Projectivization.submodule_eq,
    Submodule.span_singleton_le_iff_mem,mem_infinity]

theorem point_not_infinity (v : n→F) :
    point v∉(infinity (F:=F) (n:=n)).projectivization := by
  change Projectivization.mk F (vector v) (vector_ne_zero v)∉_
  rw [Submodule.mk_mem_projectivization_iff,mem_infinity,vector_zeroCoord]
  exact one_ne_zero

def coordinates (p : Point (F:=F) (n:=n)) : n→F :=
  fun i => p.rep (Sum.inr i)/p.rep (Sum.inl ())

theorem point_coordinates (p : Point (F:=F) (n:=n))
    (hp : p∉(infinity (F:=F) (n:=n)).projectivization) : point (coordinates p)=p := by
  have h0 : p.rep (Sum.inl ())≠0 := fun he => hp ((mem_projective_infinity p).mpr he)
  conv_rhs => rw [←p.mk_rep]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨(Units.mk0 (p.rep (Sum.inl ())) h0)⁻¹,?_⟩
  funext i
  rcases i with _ | i
  · simp [vector,Pi.smul_apply,Units.smul_def,h0]
  · simp [vector,coordinates,Pi.smul_apply,Units.smul_def,div_eq_mul_inv,mul_comm]

@[simp] theorem coordinates_point (v : n→F) : coordinates (point v)=v :=
  point_injective (point_coordinates _ (point_not_infinity v))

def chart : (n→F)≃{p : Point (F:=F) (n:=n) //
    p∉(infinity (F:=F) (n:=n)).projectivization} where
  toFun v := ⟨point v,point_not_infinity v⟩
  invFun p := coordinates p.val
  left_inv := coordinates_point
  right_inv p := Subtype.ext (point_coordinates p.val p.property)

end SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
