import SymmetricSubgroupAsymptotics.E6UniversalSelectedWordIdentities

/-! Semantic selected E6 word identities in ANY actual involution system.
All long identities come from the same imported universal braid certificates.
No Y spider relation, derived-centre quotient, root faithfulness, whole-group
generation or model-specific nontriviality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6BraidSystemWordAlgebra
open InvolutionBraidTrace InvolutionBraidPresentation
open CFSGYE6SelectedWords (adjacent guideW thetaWord wordA wordB wordC)
open CFSGYE6RotationFirstConjugationBraidPilot (rotationWord)
open CFSGYE6FourierFirstConjugationBraidCertificate (fourierWord differenceWord)
variable {G : Type*} [Group G] (S : System adjacent G)

def eval (w : List (Fin 6)) : G := value S.generator w
abbrev a : G := eval S wordA
abbrev b : G := eval S wordB
abbrev c : G := eval S wordC
abbrev r : G := eval S rotationWord
abbrev q : G := eval S fourierWord

 theorem eval_pair (i j : Fin 6) : eval S [i,j]=S.generator i*S.generator j := by
  simp only [eval,value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]

 theorem generator_commutes (i j : Fin 6) (hij : adjacent i j=false) :
    Commute (S.generator i) (S.generator j) := S.commute i j hij

private theorem cube_of_braid {K : Type*} [Group K] (x y : K)
    (hx : x*x=1) (hy : y*y=1) (hxy : x*y*x=y*x*y) : (x*y)^3=1 := by
  calc
    (x*y)^3=(x*y*x)*(y*x*y) := by simp only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc]
    _=(y*x*y)*(y*x*y) := by rw [hxy]
    _=y*x*(y*y)*x*y := by group
    _=y*(x*x)*y := by rw [hy]; group
    _=1 := by rw [hx,mul_one,hy]

 theorem a_cube : a S^3=1 := by
  change eval S [1,2]^3=1
  rw [eval_pair]
  exact cube_of_braid _ _ (S.square 1) (S.square 2) (S.braid 1 2 rfl)

 theorem b_cube : b S^3=1 := by
  change eval S [3,4]^3=1
  rw [eval_pair]
  exact cube_of_braid _ _ (S.square 3) (S.square 4) (S.braid 3 4 rfl)

 theorem conjugation_of_identity (u v w : List (Fin 6))
    (h : eval S (u++v++u.reverse++w.reverse)=1) :
    eval S u*eval S v*(eval S u)⁻¹=eval S w := by
  have hh : (eval S u*eval S v*(eval S u)⁻¹)*(eval S w)⁻¹=1 := by
    simpa only [eval,value_append,value_reverse S.generator S.square,mul_assoc] using h
  exact mul_inv_eq_one.mp hh

 theorem inverse_conjugation_of_identity (u v w : List (Fin 6))
    (h : eval S (u++v++u.reverse++w)=1) :
    eval S u*eval S v*(eval S u)⁻¹=(eval S w)⁻¹ := by
  have hh : (eval S u*eval S v*(eval S u)⁻¹)*eval S w=1 := by
    simpa only [eval,value_append,value_reverse S.generator S.square,mul_assoc] using h
  exact mul_eq_one_iff_eq_inv.mp hh

 theorem guide_conjugation_of_identity (i j : Fin 6)
    (h : eval S (guideW.reverse++[i]++guideW++[j])=1) :
    (eval S guideW)⁻¹*S.generator i*eval S guideW=S.generator j := by
  have hs (k : Fin 6) : value S.generator [k]=S.generator k := by simp [value]
  have hh : ((eval S guideW)⁻¹*S.generator i*eval S guideW)*S.generator j=1 := by
    simpa only [eval,value_append,hs,value_reverse S.generator S.square,mul_assoc] using h
  have hj : (S.generator j)⁻¹=S.generator j := inv_eq_of_mul_eq_one_right (S.square j)
  apply mul_inv_eq_one.mp
  rw [hj]
  exact hh

 theorem theta_description : eval S thetaWord=eval S guideW*S.generator 5*(eval S guideW)⁻¹ := by
  have hs : value S.generator [5]=S.generator 5 := by simp [value]
  simp only [thetaWord,eval,value_append,hs,value_reverse S.generator S.square,mul_assoc]

 theorem theta_square : eval S thetaWord^2=1 := by
  rw [theta_description]
  calc
    _=eval S guideW*(S.generator 5*S.generator 5)*(eval S guideW)⁻¹ := by rw [pow_two]; group
    _=1 := by rw [S.square]; group

private theorem conjugation_commute {K : Type*} [Group K] (w x y z : K)
    (h : w⁻¹*x*w=y) (hc : Commute y z) : Commute x (w*z*w⁻¹) := by
  have hx : x=w*y*w⁻¹ := by rw [←h]; group
  change x*(w*z*w⁻¹)=(w*z*w⁻¹)*x
  calc
    _=(w*y*w⁻¹)*(w*z*w⁻¹) := by rw [hx]
    _=w*(y*z)*w⁻¹ := by group
    _=w*(z*y)*w⁻¹ := by rw [hc.eq]
    _=(w*z*w⁻¹)*(w*y*w⁻¹) := by group
    _=_ := by rw [←hx]

 theorem theta_commutes_of_identity (i j : Fin 6) (hj : adjacent j 5=false)
    (h : eval S (guideW.reverse++[i]++guideW++[j])=1) :
    Commute (S.generator i) (eval S thetaWord) := by
  rw [theta_description]
  exact conjugation_commute _ _ _ _ (guide_conjugation_of_identity S i j h)
    (generator_commutes S j 5 hj)

 theorem theta_commutes_one : Commute (S.generator 1) (eval S thetaWord) := by
  apply theta_commutes_of_identity S 1 4 rfl
  simpa only [CFSGYE6FirstConjugationBraidPilot.source_word,eval] using
    E6UniversalSelectedWordIdentities.FirstTheta.identity_in_system S

 theorem theta_commutes_two : Commute (S.generator 2) (eval S thetaWord) := by
  apply theta_commutes_of_identity S 2 3 rfl
  simpa only [CFSGYE6SecondConjugationBraidPilot.source_word,eval] using
    E6UniversalSelectedWordIdentities.SecondTheta.identity_in_system S

 theorem theta_commutes_three : Commute (S.generator 3) (eval S thetaWord) := by
  apply theta_commutes_of_identity S 3 2 rfl
  simpa only [CFSGYE6ThirdConjugationBraidPilot.source_word,eval] using
    E6UniversalSelectedWordIdentities.ThirdTheta.identity_in_system S

 theorem theta_commutes_four : Commute (S.generator 4) (eval S thetaWord) := by
  apply theta_commutes_of_identity S 4 1 rfl
  simpa only [CFSGYE6FourthConjugationBraidPilot.source_word,eval] using
    E6UniversalSelectedWordIdentities.FourthTheta.identity_in_system S

 theorem raw_a : a S=S.generator 1*S.generator 2 := eval_pair S 1 2
 theorem raw_b : b S=S.generator 3*S.generator 4 := eval_pair S 3 4
 theorem raw_c : c S=S.generator 5*eval S thetaWord := by
  change value S.generator ([5]++thetaWord)=_
  rw [value_append]
  simp only [eval,value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]

 theorem first_commutes_c : Commute (S.generator 1) (c S) := by
  rw [raw_c]
  exact (generator_commutes S 1 5 rfl).mul_right (theta_commutes_one S)

 theorem third_commutes_c : Commute (S.generator 3) (c S) := by
  rw [raw_c]
  exact (generator_commutes S 3 5 rfl).mul_right (theta_commutes_three S)

 theorem a_commutes_b : Commute (a S) (b S) := by
  rw [raw_a,raw_b]
  exact ((generator_commutes S 1 3 rfl).mul_left (generator_commutes S 2 3 rfl)).mul_right
    ((generator_commutes S 1 4 rfl).mul_left (generator_commutes S 2 4 rfl))

 theorem a_commutes_c : Commute (a S) (c S) := by
  rw [raw_a]
  have h2 : Commute (S.generator 2) (c S) := by
    rw [raw_c]
    exact (generator_commutes S 2 5 rfl).mul_right (theta_commutes_two S)
  exact (first_commutes_c S).mul_left h2

 theorem b_commutes_c : Commute (b S) (c S) := by
  rw [raw_b]
  have h4 : Commute (S.generator 4) (c S) := by
    rw [raw_c]
    exact (generator_commutes S 4 5 rfl).mul_right (theta_commutes_four S)
  exact (third_commutes_c S).mul_left h4

 theorem rotation_a : r S*a S*(r S)⁻¹=b S := by
  apply conjugation_of_identity S rotationWord wordA wordB
  simpa only [CFSGYE6RotationFirstConjugationBraidPilot.source_word,eval] using
    E6UniversalSelectedWordIdentities.RotationFirst.identity_in_system S

 theorem rotation_b : r S*b S*(r S)⁻¹=c S := by
  apply conjugation_of_identity S rotationWord wordB wordC
  simpa only [CFSGYE6RotationSecondConjugationBraidCertificate.source_word,eval] using
    E6UniversalSelectedWordIdentities.RotationSecond.identity_in_system S

 theorem r_cube : r S^3=1 := by
  have h := E6UniversalSelectedWordIdentities.RotationCube.identity_in_system S
  rw [CFSGYE6RotationCubeBraidCertificate.source_word] at h
  simpa only [eval,value_append,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using h

 theorem rotation_c : r S*c S*(r S)⁻¹=a S := by
  calc
    _=r S*(r S*b S*(r S)⁻¹)*(r S)⁻¹ := by rw [rotation_b]
    _=r S*(r S*(r S*a S*(r S)⁻¹)*(r S)⁻¹)*(r S)⁻¹ := by rw [rotation_a]
    _=r S^3*a S*(r S^3)⁻¹ := by simp only [pow_succ,pow_zero,mul_one,one_mul] <;> group
    _=a S := by rw [r_cube,inv_one,one_mul,mul_one]

 theorem c_cube : c S^3=1 := by
  calc
    c S^3=(r S*b S*(r S)⁻¹)^3 := by rw [rotation_b]
    _=r S*(b S^3)*(r S)⁻¹ := by simp only [pow_succ,pow_zero,mul_one,one_mul] <;> group
    _=1 := by rw [b_cube]; group

 theorem difference_description : eval S differenceWord=a S*(b S)⁻¹ := by
  simp only [differenceWord,eval,value_append,value_reverse S.generator S.square]

 theorem fourier_first : q S*(a S*(b S)⁻¹)*(q S)⁻¹=r S := by
  have hword : eval S (fourierWord++differenceWord++fourierWord.reverse++rotationWord.reverse)=1 := by
    simpa only [CFSGYE6FourierFirstConjugationBraidCertificate.source_word,eval] using
      E6UniversalSelectedWordIdentities.FourierFirst.identity_in_system S
  have h := conjugation_of_identity S fourierWord differenceWord rotationWord hword
  rw [difference_description] at h
  exact h

 theorem fourier_second : q S*r S*(q S)⁻¹=(a S*(b S)⁻¹)⁻¹ := by
  have hword : eval S (fourierWord++rotationWord++fourierWord.reverse++differenceWord)=1 := by
    simpa only [CFSGYE6FourierSecondConjugationBraidCertificate.source_word,
      CFSGYE6FourierSecondConjugationBraidCertificate.fourierWord,
      CFSGYE6FourierSecondConjugationBraidCertificate.differenceWord,fourierWord,differenceWord,eval] using
      E6UniversalSelectedWordIdentities.FourierSecond.identity_in_system S
  have h := inverse_conjugation_of_identity S fourierWord rotationWord differenceWord hword
  rw [difference_description] at h
  exact h

end SymmetricSubgroupAsymptotics.E6BraidSystemWordAlgebra
