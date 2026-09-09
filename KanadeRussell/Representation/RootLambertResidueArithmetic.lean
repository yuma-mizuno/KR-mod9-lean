import KanadeRussell.Representation.RootLambertMomentTable

/-! Arithmetic descriptions of the actual twelve-period moments. These
identities hold at every degree, not only within the first period. -/
set_option autoImplicit false
namespace KanadeRussell.Representation

def residueCharacter3 (n : ℕ) : ℤ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0
def residueCharacter4 (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

theorem principalRootMomentCount_dvd (n : ℕ) :
    principalRootMomentCount (positiveModeResidue n) =
      3-(if 2 ∣ n+1 then 1 else 0)-(if 3 ∣ n+1 then 1 else 0)+(if 6 ∣ n+1 then 1 else 0) := by
  have h2 : (2 ∣ n+1) ↔ 2 ∣ n%12+1 := by omega
  have h3 : (3 ∣ n+1) ↔ 3 ∣ n%12+1 := by omega
  have h6 : (6 ∣ n+1) ↔ 6 ∣ n%12+1 := by omega
  simp only [h2, h3, h6]
  exact (by decide : ∀ s : Fin 12, principalRootMomentCount s =
    3-(if 2 ∣ s.val+1 then 1 else 0)-(if 3 ∣ s.val+1 then 1 else 0)+
      (if 6 ∣ s.val+1 then 1 else 0)) (positiveModeResidue n)

theorem principalRootMomentNorm_dvd (n : ℕ) :
    principalRootMomentNorm (positiveModeResidue n) =
      5-3*(if 2 ∣ n+1 then 1 else 0)-3*(if 3 ∣ n+1 then 1 else 0)+
        (if 4 ∣ n+1 then 1 else 0)+3*(if 6 ∣ n+1 then 1 else 0)-
        3*(if 12 ∣ n+1 then 1 else 0) := by
  have h2 : (2 ∣ n+1) ↔ 2 ∣ n%12+1 := by omega
  have h3 : (3 ∣ n+1) ↔ 3 ∣ n%12+1 := by omega
  have h4 : (4 ∣ n+1) ↔ 4 ∣ n%12+1 := by omega
  have h6 : (6 ∣ n+1) ↔ 6 ∣ n%12+1 := by omega
  have h12 : (12 ∣ n+1) ↔ 12 ∣ n%12+1 := by omega
  simp only [h2, h3, h4, h6, h12]
  exact (by decide : ∀ s : Fin 12, principalRootMomentNorm s =
    5-3*(if 2 ∣ s.val+1 then 1 else 0)-3*(if 3 ∣ s.val+1 then 1 else 0)+
      (if 4 ∣ s.val+1 then 1 else 0)+3*(if 6 ∣ s.val+1 then 1 else 0)-
      3*(if 12 ∣ s.val+1 then 1 else 0)) (positiveModeResidue n)

theorem principalRootMomentT_character (n : ℕ) :
    -principalRootMomentA (positiveModeResidue n)-principalRootMomentB (positiveModeResidue n) =
      residueCharacter4 (n+1)+3*(if 3 ∣ n+1 then residueCharacter4 ((n+1)/3) else 0) := by
  have h3 : (3 ∣ n+1) ↔ 3 ∣ n%12+1 := by omega
  have h4 : residueCharacter4 (n+1) = residueCharacter4 (n%12+1) := by
    unfold residueCharacter4
    have hh : (n+1)%4=(n%12+1)%4 := by omega
    simp only [hh]
  have h43 : residueCharacter4 ((n+1)/3) = residueCharacter4 ((n%12+1)/3) := by
    unfold residueCharacter4
    have hh : ((n+1)/3)%4=((n%12+1)/3)%4 := by omega
    simp only [hh]
  simp only [h3, h4, h43]
  exact (by decide : ∀ s : Fin 12, -principalRootMomentA s-principalRootMomentB s =
    residueCharacter4 (s.val+1)+3*(if 3 ∣ s.val+1 then residueCharacter4 ((s.val+1)/3) else 0))
      (positiveModeResidue n)

theorem principalRootMomentU_character (n : ℕ) :
    principalRootMomentA (positiveModeResidue n)-principalRootMomentB (positiveModeResidue n) =
      residueCharacter3 (n+1)+(if 2 ∣ n+1 then residueCharacter3 ((n+1)/2) else 0)-
        2*(if 4 ∣ n+1 then residueCharacter3 ((n+1)/4) else 0) := by
  have h2 : (2 ∣ n+1) ↔ 2 ∣ n%12+1 := by omega
  have h4 : (4 ∣ n+1) ↔ 4 ∣ n%12+1 := by omega
  have h3 : residueCharacter3 (n+1) = residueCharacter3 (n%12+1) := by
    unfold residueCharacter3
    have hh : (n+1)%3=(n%12+1)%3 := by omega
    simp only [hh]
  have h32 : residueCharacter3 ((n+1)/2) = residueCharacter3 ((n%12+1)/2) := by
    unfold residueCharacter3
    have hh : ((n+1)/2)%3=((n%12+1)/2)%3 := by omega
    simp only [hh]
  have h34 : residueCharacter3 ((n+1)/4) = residueCharacter3 ((n%12+1)/4) := by
    unfold residueCharacter3
    have hh : ((n+1)/4)%3=((n%12+1)/4)%3 := by omega
    simp only [hh]
  simp only [h2, h4, h3, h32, h34]
  exact (by decide : ∀ s : Fin 12, principalRootMomentA s-principalRootMomentB s =
    residueCharacter3 (s.val+1)+(if 2 ∣ s.val+1 then residueCharacter3 ((s.val+1)/2) else 0)-
      2*(if 4 ∣ s.val+1 then residueCharacter3 ((s.val+1)/4) else 0)) (positiveModeResidue n)

end KanadeRussell.Representation
