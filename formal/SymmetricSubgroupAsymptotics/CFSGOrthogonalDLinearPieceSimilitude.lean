import SymmetricSubgroupAsymptotics.CFSGQuadraticPiecePairing
import SymmetricSubgroupAsymptotics.CFSGBilinearZeroLocusScalar
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOpposedSpaces

/-! The two actual linear representatives on opposed coordinate spaces
glue directly to a genuine quadratic similitude. Their cross pairings
have the same zero locus, hence ONE scalar. This avoids an independent
orthogonal recognition or a transitivity assumption on the two components. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearPieceSimilitude
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDOpposedSpaces
open CFSGSingularPlaneTriangle
variable (K : Type) [Field K]

def sourceCross (r : ℕ) : (positiveSpace K r)→ₗ[K](negativeSpace K r)→ₗ[K]K :=
  (splitQuadraticForm K r).polarBilin.compl₁₂
    (positiveSpace K r).subtype (negativeSpace K r).subtype

theorem sourceCross_injective (r : ℕ) : Function.Injective (sourceCross K r) := by
  intro x y h
  apply sub_eq_zero.mp
  apply Subtype.ext
  by_contra hn
  have hz : sourceCross K r (x-y)=0 := by rw [map_sub,h,sub_self]
  exact cross_negative_nondegenerate K r (x-y).val (x-y).property hn hz

theorem cross_scalar (r : ℕ) (hr : 0<r)
    (f : Points (splitQuadraticForm K r)≃Points (splitQuadraticForm K r))
    (horth : ∀P R,ZeroOn (splitQuadraticForm K r).polarBilin (f P).val (f R).val ↔
      ZeroOn (splitQuadraticForm K r).polarBilin P.val R.val)
    (F : SemilinearPiece (splitQuadraticForm K r) f (positiveSingular K r) (RingEquiv.refl K))
    (G : SemilinearPiece (splitQuadraticForm K r) f (negativeSingular K r) (RingEquiv.refl K)) :
    ∃c : K,c≠0 ∧ ∀(x : positiveSpace K r) (y : negativeSpace K r),
      (splitQuadraticForm K r).polarBilin (F.map x) (G.map y)=
        c*(splitQuadraticForm K r).polarBilin x.val y.val := by
  let C := (splitQuadraticForm K r).polarBilin.compl₁₂ F.map G.map
  have hne : ∃x y,sourceCross K r x y≠0 := by
    let i : Fin r := ⟨0,hr⟩
    let x : positiveSpace K r := ⟨Pi.single (Sum.inl i) 1,by intro j;simp⟩
    let y : negativeSpace K r := ⟨Pi.single (Sum.inr i) 1,by intro j;simp⟩
    refine ⟨x,y,?_⟩
    change (splitQuadraticForm K r).polarBilin x.val y.val≠0
    rw [splitQuadraticForm_polar]
    simp [x,y,polar,leftPart,rightPart,dotProduct,Pi.single_apply]
  obtain ⟨c,hc,he⟩ := CFSGBilinearZeroLocusScalar.exists_nonzero_scalar
    (sourceCross K r) C (sourceCross_injective K r) hne
    (fun x y=>piece_pairing_zero_iff (splitQuadraticForm K r) f horth
      (positiveSingular K r) (negativeSingular K r) (RingEquiv.refl K) (RingEquiv.refl K) F G x y)
  refine ⟨c,hc,?_⟩
  intro x y
  exact congrArg (fun B : (positiveSpace K r)→ₗ[K](negativeSpace K r)→ₗ[K]K=>B x y) he

def positivePartMap (r : ℕ) : (Index r→K)→ₗ[K]positiveSpace K r :=
  (positiveEquiv K r).toLinearMap.comp (LinearMap.pi fun i=>LinearMap.proj (Sum.inl i))

def negativePartMap (r : ℕ) : (Index r→K)→ₗ[K]negativeSpace K r :=
  (negativeEquiv K r).toLinearMap.comp (LinearMap.pi fun i=>LinearMap.proj (Sum.inr i))

def gluedMap (r : ℕ)
    (f : Points (splitQuadraticForm K r)≃Points (splitQuadraticForm K r))
    (F : SemilinearPiece (splitQuadraticForm K r) f (positiveSingular K r) (RingEquiv.refl K))
    (G : SemilinearPiece (splitQuadraticForm K r) f (negativeSingular K r) (RingEquiv.refl K)) :
    (Index r→K)→ₗ[K](Index r→K) :=
  F.map.comp (positivePartMap K r)+G.map.comp (negativePartMap K r)

theorem gluedMap_quadratic (r : ℕ)
    (f : Points (splitQuadraticForm K r)≃Points (splitQuadraticForm K r))
    (F : SemilinearPiece (splitQuadraticForm K r) f (positiveSingular K r) (RingEquiv.refl K))
    (G : SemilinearPiece (splitQuadraticForm K r) f (negativeSingular K r) (RingEquiv.refl K))
    (c : K) (hcross : ∀(x : positiveSpace K r) (y : negativeSpace K r),
      (splitQuadraticForm K r).polarBilin (F.map x) (G.map y)=
        c*(splitQuadraticForm K r).polarBilin x.val y.val) (v : Index r→K) :
    splitQuadraticForm K r (gluedMap K r f F G v)=c*splitQuadraticForm K r v := by
  let q := splitQuadraticForm K r
  let x := positivePartMap K r v
  let y := negativePartMap K r v
  have hsum : v=x.val+y.val := decompose K r v
  have hqsum : q v=q.polarBilin x.val y.val := by
    conv_lhs => rw [hsum]
    rw [QuadraticMap.map_add q x.val y.val]
    change q x.val+q y.val+q.polarBilin x.val y.val=_
    rw [positiveSpace_singular K r x,negativeSpace_singular K r y.val y.property,
      zero_add,zero_add]
  change q (F.map x+G.map y)=c*q v
  rw [QuadraticMap.map_add q (F.map x) (G.map y)]
  change q (F.map x)+q (G.map y)+q.polarBilin (F.map x) (G.map y)=c*q v
  rw [F.quadratic_zero,G.quadratic_zero,zero_add,zero_add,hcross,←hqsum]

theorem exists_glued_similitude (r : ℕ) (hr : 0<r)
    (f : Points (splitQuadraticForm K r)≃Points (splitQuadraticForm K r))
    (horth : ∀P R,ZeroOn (splitQuadraticForm K r).polarBilin (f P).val (f R).val ↔
      ZeroOn (splitQuadraticForm K r).polarBilin P.val R.val)
    (F : SemilinearPiece (splitQuadraticForm K r) f (positiveSingular K r) (RingEquiv.refl K))
    (G : SemilinearPiece (splitQuadraticForm K r) f (negativeSingular K r) (RingEquiv.refl K)) :
    ∃(c : K) (L : (Index r→K)≃ₗ[K](Index r→K)),c≠0 ∧
      (∀v,splitQuadraticForm K r (L v)=c*splitQuadraticForm K r v) ∧
      (∀x : positiveSpace K r,L x.val=F.map x) ∧
      (∀y : negativeSpace K r,L y.val=G.map y) := by
  obtain ⟨c,hc,hcross⟩ := cross_scalar K r hr f horth F G
  let H := gluedMap K r f F G
  have hQ := gluedMap_quadratic K r f F G c hcross
  have hpolar (u v : Index r→K) :
      (splitQuadraticForm K r).polarBilin (H u) (H v)=
        c*(splitQuadraticForm K r).polarBilin u v := by
    change splitQuadraticForm K r (H u+H v)-splitQuadraticForm K r (H u)-
      splitQuadraticForm K r (H v)=c*(splitQuadraticForm K r (u+v)-
        splitQuadraticForm K r u-splitQuadraticForm K r v)
    rw [←H.map_add,hQ,hQ,hQ]
    ring
  have hinj : Function.Injective H := by
    intro u v huv
    apply sub_eq_zero.mp
    apply (splitQuadraticForm_nondegenerate K r).1
    intro z
    have he := hpolar (u-v) z
    rw [H.map_sub,huv,sub_self,map_zero,LinearMap.zero_apply] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hc
  let L := LinearEquiv.ofInjectiveEndo H hinj
  refine ⟨c,L,hc,hQ,?_,?_⟩
  · intro x
    change F.map (positivePartMap K r x.val)+G.map (negativePartMap K r x.val)=F.map x
    have hP : positivePartMap K r x.val=x := by
      apply Subtype.ext
      exact positiveEmbedding_leftPart K r x.val x.property
    have hZ : negativePartMap K r x.val=0 := by
      apply Subtype.ext
      funext i
      cases i with
      | inl j => rfl
      | inr j => exact x.property j
    exact (congrArg₂ (fun a b : Index r→K=>a+b)
      (congrArg F.map hP) ((congrArg G.map hZ).trans G.map.map_zero)).trans (add_zero _)
  · intro y
    change F.map (positivePartMap K r y.val)+G.map (negativePartMap K r y.val)=G.map y
    have hP : positivePartMap K r y.val=0 := by
      apply Subtype.ext
      funext i
      cases i with
      | inl j => exact y.property j
      | inr j => rfl
    have hZ : negativePartMap K r y.val=y := by
      apply Subtype.ext
      funext i
      cases i with
      | inl j => exact (y.property j).symm
      | inr j => rfl
    exact (congrArg₂ (fun a b : Index r→K=>a+b)
      ((congrArg F.map hP).trans F.map.map_zero) (congrArg G.map hZ)).trans (zero_add _)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearPieceSimilitude
