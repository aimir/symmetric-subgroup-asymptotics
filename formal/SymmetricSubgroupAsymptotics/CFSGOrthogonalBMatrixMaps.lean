import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

/-! Literal coefficient change for B root and exponential matrices. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem map_positive {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (positive R r i)=positive S r i := by
  by_cases hi : i.val+1<r
  · simp only [positive,dif_pos hi]
    rw [map_sub]
    change (Matrix.single _ _ (1:R)).map f-(Matrix.single _ _ (1:R)).map f=_
    simp only [Matrix.map_single,map_one]
  · simp only [positive,dif_neg hi]
    rw [map_sub]
    change (Matrix.single _ _ (1:R)).map f-(Matrix.single _ _ (2:R)).map f=_
    simp only [Matrix.map_single,map_one,map_ofNat]

theorem map_negative {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (negative R r i)=negative S r i := by
  by_cases hi : i.val+1<r
  · simp only [negative,dif_pos hi]
    rw [map_sub]
    change (Matrix.single _ _ (1:R)).map f-(Matrix.single _ _ (1:R)).map f=_
    simp only [Matrix.map_single,map_one]
  · simp only [negative,dif_neg hi]
    rw [map_sub]
    change (Matrix.single _ _ (2:R)).map f-(Matrix.single _ _ (1:R)).map f=_
    simp only [Matrix.map_single,map_one,map_ofNat]

theorem map_positiveSecond {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (positiveSecond R r i)=positiveSecond S r i := by
  by_cases hi : i.val+1<r
  · simp only [positiveSecond,if_pos hi,map_zero]
  · simp only [positiveSecond,if_neg hi]
    change (Matrix.single _ _ (-1:R)).map f=_
    simp only [Matrix.map_single,map_neg,map_one]

theorem map_negativeSecond {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (negativeSecond R r i)=negativeSecond S r i := by
  by_cases hi : i.val+1<r
  · simp only [negativeSecond,if_pos hi,map_zero]
  · simp only [negativeSecond,if_neg hi]
    change (Matrix.single _ _ (-1:R)).map f=_
    simp only [Matrix.map_single,map_neg,map_one]

theorem map_cartan {S : Type*} [CommRing S] (f : R→+*S) (i : Fin r) :
    f.mapMatrix (cartan R r i)=cartan S r i := by
  simp only [cartan,Ring.lie_def,map_sub,map_mul,map_positive,map_negative]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
