import ..lovelib
import .eudoxus

/-! # Project : Eudoxus Reals
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

lemma almost_hom_id :
  almost_hom (λ n, n) :=
  begin
    rw almost_hom,
    simp,
  end

noncomputable def mul_and_floor (r : ℝ) (n : ℤ) := ⌊r * n⌋

lemma mul_and_floor_lt_add_one (r : ℝ) (n : ℤ) : 
  r * n ≤ mul_and_floor r n + 1 :=
  begin
    rw mul_and_floor,
    apply le_of_lt,
    apply lt_floor_add_one,
  end

lemma mul_and_floor_le (r : ℝ) (n : ℤ) : 
  r * n ≥ mul_and_floor r n :=
  begin
    rw mul_and_floor,
    apply floor_le,
  end

lemma almost_hom_maf.aux1 (r : ℝ) (n m : ℤ) :
  ((mul_and_floor r n) + (mul_and_floor r m) - (mul_and_floor r (n + m))) ≤ 1 :=
  begin
    have hrnm : r*(n+m) ≤ mul_and_floor r (n+m) + 1 := 
      begin
        rw mul_and_floor,
        norm_num,
        apply le_of_lt,
        apply lt_floor_add_one,
      end,
    have hrn : -r*n ≤ - mul_and_floor r n := 
      begin
        rw mul_and_floor, norm_num, apply floor_le,
      end,
    have hrm : -r*m ≤ - mul_and_floor r m := 
      begin
        rw mul_and_floor, norm_num, apply floor_le,
      end,
    rw mul_and_floor at *,
    rw mul_and_floor at *,
    rw mul_and_floor at *,
    
    have haux : r * (↑n + ↑m) + -r * ↑n + -r * ↑m ≤ ↑⌊r * ↑(n + m)⌋ + 1 + -↑⌊r * ↑n⌋ + -↑⌊r * ↑m⌋ :=
      by apply add_le_add (add_le_add hrnm hrn) hrm,
    
    have hzero : r * (↑n + ↑m) + -r * ↑n + -r * ↑m = 0 := by linarith,
    /-
    have h : ⌊r * ↑(n + m)⌋ + 1 -⌊r * ↑n⌋ -⌊r * ↑m⌋ ≥ 0 :=
      begin 
        rw [hzero] at haux,
        simp [ge.le],
      end,
      -/
    have h1 : ⌊r * ↑(n + m)⌋ + 1 -⌊r * ↑n⌋ -⌊r * ↑m⌋ ≥ 0 := sorry,
    linarith,
  end

lemma almost_hom_maf.aux2 (r : ℝ) (n m : ℤ) :
  ((mul_and_floor r n) + (mul_and_floor r m) - (mul_and_floor r (n + m))) ≥ -2 :=
  begin
    simp,
    calc ((mul_and_floor r n) + (mul_and_floor r m) - (mul_and_floor r (n + m))) 
          > (r * n - 1) + (r * m - 1) - (mul_and_floor r (n + m)) : _ 
      ... ≥ (r * n - 1) + (r * m - 1) - r (n + m) : _
      ... = - 2 : _,


  end

-- #check set.finite_Icc, 
lemma almost_hom_maf.aux3 : 
  {x : ℤ | -1 ≤ x ∧ x ≤ 2}.finite :=
    begin
      sorry,
      --apply set.finite_Icc (-2) 1
    end

lemma almost_hom_maf.aux4 (r : ℝ) :
  {x | ∃ m n : ℤ, x = (mul_and_floor r (n + m)) - (mul_and_floor r n) - (mul_and_floor r m)}  
  ⊆ {x : ℤ | -1 ≤ x ∧ x ≤ 2} :=
  begin
    simp [set.subset_def],
    intros x m n h,
    apply and.intro,
    {rw h,
    sorry},
    {sorry},
  end

lemma almost_hom_maf (r : ℝ):
  almost_hom (mul_and_floor r) := 
  begin
      simp [almost_hom],
      sorry,
  end

end LoVe
