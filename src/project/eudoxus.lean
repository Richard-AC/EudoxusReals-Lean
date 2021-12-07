import ..lovelib

/-! # Project : Eudoxus Reals -/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

def almost_hom (f : ℤ → ℤ) : Prop :=
{x | ∃ m n : ℤ, x = f(n + m) - f(n) - f(m)}.finite

structure almost_homs :=
(func         : ℤ → ℤ)
(almost_hom   : almost_hom func)

namespace almost_homomorphisms

@[instance] def setoid : setoid almost_homs :=
{ r     := λf g : almost_homs, {x | ∃ n : ℤ, x = f.func(n) - g.func(n) }.finite,
  iseqv := 
        begin 
          apply and.intro,
          { simp [reflexive] },
          apply and.intro,
          { simp [symmetric], 
            intros f g,
            intro hfg,
            let sfg := {x | ∃ n : ℤ, x = f.func(n) - g.func(n)},
            let sgf := {x | ∃ n : ℤ, x = g.func(n) - f.func(n)},
            have hneg : sgf = (λn, -n) '' sfg := 
              begin
                apply eq.symm,
                apply set.surj_on.image_eq_of_maps_to _ _,
                { simp [set.surj_on, set.subset_def],
                  intro a, apply exists.intro a, simp,},
                { simp [set.maps_to],
                  intro a, apply exists.intro a, simp,},
              end,
            have sgf_def : {x | ∃ n : ℤ, x = g.func(n) - f.func(n)} = sgf := by simp,
            have sfg_def : {x | ∃ n : ℤ, x = f.func(n) - g.func(n)} = sfg := by simp,
            rw sgf_def at ⊢,
            rw sfg_def at hfg,
            rw hneg at ⊢,
            apply set.finite.image (λ n, -n) hfg,
            },
          { simp [transitive],
            intros f g h hfg hgh,
            let sfg := {x : ℤ | ∃ (n : ℤ), x = f.func n - g.func n},
            have sfg_def : {x : ℤ | ∃ (n : ℤ), x = f.func n - g.func n} = sfg := by refl,
            let sgh := {x : ℤ | ∃ (n : ℤ), x = g.func n - h.func n},
            have sgh_def : {x : ℤ | ∃ (n : ℤ), x = g.func n - h.func n} = sgh := by refl,
            let sfh := {x : ℤ | ∃ (n : ℤ), x = f.func n - h.func n},
            have sfh_def : {x : ℤ | ∃ (n : ℤ), x = f.func n - h.func n} = sfh := by refl,
            rw sfg_def at hfg,
            rw sgh_def at hgh,
            have hsub : sfh ⊆ set.image2 (λa b, a+b) sfg sgh :=
              begin
                rw set.image2,
                simp [set.subset_def],
                intro n,
                apply exists.intro (f.func n - g.func n),
                apply and.intro,
                {apply exists.intro n, refl,},
                apply exists.intro (g.func n - h.func n),
                apply and.intro,
                {apply exists.intro n, refl},
                linarith,
              end,
            simp [sfh_def],
            have himfin : set.finite(set.image2 (λ a b, a + b) sfg sgh) :=
              by apply set.finite.image2 (λ a b, a+b) hfg hgh,
            apply set.finite.subset himfin hsub,
          },
        end
}

lemma setoid_iff (f g : almost_homs) :
  f ≈ g ↔ {x | ∃ n : ℤ, x = f.func(n) - g.func(n) }.finite :=
by refl

@[instance] def has_zero : has_zero almost_homs :=
{ zero := 
    { func:= λ n, 0,
      almost_hom         := by simp [almost_hom],
    } 
}

@[simp] lemma zero_func :
  (0 : almost_homs).func = λn, 0 :=
  by refl

@[instance] def has_neg : has_neg almost_homs :=
{ neg := λ f : almost_homs,   
    { func           := - f.func,
      almost_hom         := 
        begin
          simp [almost_hom],
          let s := {x | ∃ m n : ℤ, x = f.func(n + m) - f.func(n) - f.func(m)},
          have hsfin : s.finite := f.almost_hom,
          have him : {x | ∃ m n : ℤ, x = f.func(n) - f.func(n + m) + f.func(m)} = (λn, -n) '' s :=
            begin
              apply eq.symm,
              refine set.surj_on.image_eq_of_maps_to _ _,
              { simp [set.surj_on, set.subset_def],
                intros x m n h,
                apply exists.intro m,
                apply exists.intro n,
                linarith,
              },
              { simp [set.maps_to],
                intros x m n h,
                apply exists.intro m,
                apply exists.intro n,
                linarith,},
            end,
          rw him at ⊢,
          refine set.finite.image (λ n, -n) hsfin,
        end,
    } 
}

@[instance] def has_one : has_one almost_homs :=
{ one := 
    { func:= λ n, n,
      almost_hom         := by simp [almost_hom],
    } 
}

@[simp] lemma one_func :
  (1 : almost_homs).func = λn, n :=
  by refl

-- # Addition

@[instance] def has_add : has_add almost_homs :=
{ add := λf g : almost_homs,
    { func:= f.func + g.func,
      almost_hom         :=
        begin
          simp [almost_hom],
          let sf := {x | ∃ m n : ℤ, x = f.func(n + m) - f.func(n) - f.func(m)},
          have hf : sf.finite := f.almost_hom,
          let sg := {x | ∃ m n : ℤ, x = g.func(n + m) - g.func(n) - g.func(m)},
          have hg : sg.finite := g.almost_hom,
          let sfg := {x : ℤ | ∃ (m n : ℤ), x = f.func (n + m) + g.func (n + m) 
                              - (f.func n + g.func n) - (f.func m + g.func m)},
          have sfg_def : {x : ℤ | ∃ (m n : ℤ), x = f.func (n + m) + g.func (n + m) 
                - (f.func n + g.func n) - (f.func m + g.func m)} = sfg := by refl,
          have hsub : sfg ⊆ set.image2 (λ a b, a + b) sf sg :=
            begin
              rw set.image2,
              simp [set.subset_def],
              intros x m n hmn,
              apply exists.intro (f.func (n + m) - f.func n - f.func m),
              apply and.intro,
              {
              apply exists.intro m,
              apply exists.intro n,
              refl,
              },
              apply exists.intro (g.func (n + m) - g.func n - g.func m),
              apply and.intro,
              {
                apply exists.intro m,
                apply exists.intro n,
                refl,
              },
              simp [hmn],
              linarith,
            end,
          simp [sfg_def],
          have himfin : set.finite(set.image2 (λ a b, a + b) sf sg) :=
            by apply set.finite.image2 (λ a b, a+b) hf hg,
          apply set.finite.subset himfin hsub,
        end,
    } 
}

@[simp] lemma add_func (f g : almost_homs): 
  (f + g).func = f.func + g.func :=
  by refl

lemma add_comm (f g : almost_homs): 
  f + g = g + f :=
  begin
    cases' f with f_func hf,
    cases' g with g_func hg,
    --simp,
    sorry,
  end
  

lemma add_equiv_add {f f' g g' : almost_homs} 
(hf : f ≈ f') (hg : g ≈ g') :
  f + g ≈ f' + g' :=
  begin
    simp [setoid_iff] at *,
    let sff' := {x | ∃ n : ℤ, x = f.func n - f'.func n},
    have sff'_def : {x | ∃ n : ℤ, x = f.func n - f'.func n} = sff' := by refl,
    let sgg' := {x | ∃ n : ℤ, x = g.func n - g'.func n},
    have sgg'_def : {x | ∃ n : ℤ, x = g.func n - g'.func n} = sgg' := by refl,
    let s := {x | ∃ n : ℤ, x = f.func n + g.func n - (f'.func n + g'.func n)},
    have s_def : {x | ∃ n : ℤ, x = f.func n + g.func n - (f'.func n + g'.func n)} = s := by refl,
    simp [sff'_def, sgg'_def, s_def] at *,
    have hsub : s ⊆ set.image2 (λ a b, a + b) sff' sgg' :=
    begin
      rw set.image2,
      simp [set.subset_def],
      intro n,
      apply exists.intro (f.func n - f'.func n),
      apply and.intro,
      {apply exists.intro n, refl},
      {
        apply exists.intro (g.func n - g'.func n),
        apply and.intro,
        {apply exists.intro n, refl},
        linarith,
      }
    end,
  have himfin : set.finite(set.image2 (λ a b, a + b) sff' sgg') :=
    by apply set.finite.image2 (λ a b, a+b) hf hg,
  apply set.finite.subset himfin hsub,
  end

lemma zero_add {f : almost_homs} :
  0 + f ≈ f :=
  by simp [setoid_iff]

-- @[instance] def almost_homs.add_group : add_group almost_homs :=

-- # Multiplication

-- We now define the error of an almost homomorphism.
-- d_f(m, n) = f(m + n) - f(m) - f(n)
-- This value represents by how much f is not actually a homomorphism.

def hom_error (f : ℤ → ℤ) (m n : ℤ) := 
  f(m + n) - f(m) - f(n)

-- Almost homomorphisms are functions that have bounded hom_error 
constant int_set : {x | ∃ y : ℤ, x = y}
#check int_set
/-
lemma almost_hom_iff_bounded_hom_error (f : ℤ → ℤ) :
  almost_hom f ↔ bounded (hom_error f) int_set := 
  sorry 
  -/

lemma finset_exists_max {α : Type} (s : set α) [linear_order α] 
  (hnonempty : set.nonempty s) :
  s.finite → ∃ m ∈ s, ∀ x ∈ s, x ≤ m :=
  begin 
    intro hfin,
    exact set.exists_max_image s (λ (b : α), b) hfin hnonempty,
  end

-- We only need the following theorem for ℤ but it could be stated more generally
--lemma finset_exists_bound {α : Type} (s : set α ) [linear_order α] [add_group α]
--  [covariant_class α α has_add.add has_le.le] {a : α}
lemma finset_exists_bound (s : set ℤ ) 
  (hnonempty : set.nonempty s) :
  s.finite → ∃ m ∈ s, ∀ x ∈ s, abs(x) ≤ abs(m) :=
  begin 
    intro hfin,
    exact set.exists_max_image s (λ (b : ℤ), abs(b)) hfin hnonempty,
  end

lemma finset_exists_stict_bound (s : set ℤ ) 
  (hnonempty : set.nonempty s) :
  s.finite → ∃ C : ℤ, ∀ x ∈ s, abs(x) < C :=
  begin 
    intro hfin,
    cases' (finset_exists_bound s hnonempty hfin),
    cases' h with hw,
    apply exists.intro (abs w + 1),
    have haux1 : abs w < abs w + 1 := lt_add_one (abs w),
    intros x hx,
    specialize h x hx,
    exact lt_of_le_of_lt h haux1,
  end

lemma int_interval_is_finite (M : ℤ):
M ≥ 0 → set.finite ({x | x < M ∧ -M < -x}):=
  begin
    intro hM,
    sorry,
  end

lemma bounded_intset_is_finite (s : set ℤ) :
  (∃ M : ℤ, ∀ x ∈ s, abs(x) < M) → s.finite :=
  begin
    intro hbounded,
    cases' hbounded with M1,
    let M := abs M1,
    have haux1 : M1 ≤ M :=
      by exact le_abs_self M1,

    have haux2 : ∀ (x : ℤ), x ∈ s → abs x < M := 
    begin
      intros x hx,
      exact gt_of_ge_of_gt haux1 (h x hx),
    end,

    have haux3 : s ⊆ {x | x < M ∧ -M < -x} :=
    begin
      simp [set.subset_def],
      intros x hx,
      specialize h x hx,
      exact lt_of_abs_lt (haux2 x hx),
    end,

    have haux4 : M ≥ 0 :=
      by exact abs_nonneg M1,

    apply (set.finite.subset (int_interval_is_finite M haux4) haux3),
  end

lemma hbounded_error (f : almost_homs) : 
∃ C : ℤ, ∀ m n : ℤ, abs (f.func(n + m) - f.func(n) - f.func(m)) < C :=
begin
  let s_hom_err := {x | ∃ m n : ℤ, x = f.func(n + m) - f.func(n) - f.func(m)},
  have hfin : set.finite s_hom_err := f.almost_hom,
  have hnonempty : set.nonempty s_hom_err :=
  begin 
    simp [set.nonempty_def],
    apply exists.intro (- f.func 0),
    apply exists.intro (int.of_nat 0),
    apply exists.intro (int.of_nat 0),
    simp,
  end,

  cases' (finset_exists_bound s_hom_err hnonempty hfin),
  let C := abs(w) + 1,
  have hC_def : C = abs(w) + 1 := by refl,
  apply exists.intro C,
  intros m n,
  cases' h with hw,
  have hin : f.func (n + m) - f.func n - f.func m ∈ s_hom_err :=
  begin
    simp,
    apply exists.intro m,
    apply exists.intro n,
    simp,
  end,
  rw hC_def,
  have haux : abs (f.func (n + m) - f.func n - f.func m) ≤ abs w :=
  by apply (h (f.func (n + m) - f.func n - f.func m) hin),
  have hsimp : abs w <  abs w + 1 := by linarith,
  apply lt_of_le_of_lt haux hsimp,
end

lemma lemma7 (f : almost_homs) : 
∃ C : ℤ, ∀ m n : ℤ, 
abs (m * (f.func n) - n * (f.func m)) < (abs m + abs n + 2) * C :=
  begin
    
    let s_hom_err := {x | ∃ m n : ℤ, x = f.func(n + m) - f.func(n) - f.func(m)},
    have hbounded_homerror : ∃ C : ℤ, ∀ x ∈ s_hom_err,
        abs(x) < C := 
        begin
          simp,
          cases' (hbounded_error f) with C,
          apply exists.intro C,
          intros x m n hx,
          rw hx,
          apply (h m n),
        end,

      cases' hbounded_homerror with C,

    -- m ≥ 0 
    have haux_m_nat : ∀ m : ℕ, ∀ n : ℤ, 
    abs(f.func (m*n) - m * f.func n) < (abs (m) + 1) * C := 
    begin
      intros m n,
      induction m,
        {
          -- m = 0
          simp,
          have hf_mzero_in : (- f.func 0) ∈ s_hom_err := 
          begin
            simp,
            apply exists.intro (int.of_nat 0),
            apply exists.intro (int.of_nat 0),
            simp,
          end, 
          have habsneg : abs (f.func 0) = abs (- f.func 0) :=
          by simp [abs_neg],
          rw habsneg at ⊢,
          refine h (- f.func 0) hf_mzero_in,
        },
          -- p m → p m+1
        {
          simp,
          rename m_n m,
          rename m_ih ih,
          have hin : f.func (m*n + n) - f.func (m*n) - f.func n ∈ s_hom_err :=
          begin
            simp,
            apply exists.intro n,
            apply exists.intro (int.of_nat m*n),
            simp,
          end,
          have haux : abs (f.func (m*n + n) - f.func (m*n) - f.func n) < C :=
            by exact h (f.func (↑m * n + n) - f.func (↑m * n) - f.func n) hin,
          calc abs (f.func ((↑m + 1) * n) - (↑m + 1) * f.func n) 
          = abs (f.func (↑m * n + n) - f.func (↑m * n) - f.func n
                + f.func (int.of_nat m * n) - int.of_nat m * f.func n) : _
          ... ≤ abs (f.func (↑m * n + n) - f.func (↑m * n) - f.func n)
                + abs (f.func (int.of_nat m * n) - int.of_nat m * f.func n) : _
          ... < (abs(↑m + 1) + 1) * C : _,
          {
            simp,
            have hsimp1 : (↑m + 1) * n = ↑m * n + n := 
              begin 
                linarith,
              end,
            rw hsimp1 at ⊢,
            have hsimp2 : f.func (↑m * n + n) - f.func (↑m * n) - f.func n + f.func (↑m * n) - ↑m * f.func n
            = f.func (↑m * n + n) - f.func n - ↑m * f.func n := by linarith,
            rw hsimp2 at ⊢,
            have hsimp3 : (↑m + 1) * f.func n = f.func n + ↑m * f.func n := by linarith,
            rw hsimp3 at ⊢,
            have hsimp4 : f.func (↑m * n + n) - (f.func n + ↑m * f.func n) 
                        = f.func (↑m * n + n) - f.func n - ↑m * f.func n := by linarith,
            rw hsimp4 at ⊢,
          },
          {
            let a := f.func (↑m * n + n) - f.func (↑m * n) - f.func n,
            have a_def : f.func (↑m * n + n) - f.func (↑m * n) - f.func n = a := by refl,
            have hsimp1 : a + f.func (↑m * n) - ↑m * f.func n
                        = a + (f.func (↑m * n) - ↑m * f.func n) := by linarith,
            let b := f.func (↑m * n) - ↑m * f.func n,
            have b_def : f.func (↑m * n) - ↑m * f.func n = b := by refl,
            rw a_def,
            simp,
            rw hsimp1 at ⊢,
            rw b_def,
            exact abs_add a b,
          },
          {
            have haux2 : abs (f.func (int.of_nat m * n) - int.of_nat m * f.func n)
                        + abs (f.func (↑m * n + n) - f.func (↑m * n) - f.func n) 
                        < (abs (int.of_nat m) + 1) * C + C := by exact add_lt_add ih haux,
            have hsimp1 : (abs (int.of_nat m) + 1) = int.of_nat m + 1 := 
            begin
              have haux1_1 : abs (int.of_nat m) = int.of_nat m :=
              begin
                simp,
              end, 
              rw haux1_1 at ⊢,
            end,
            have hsimp2 : (abs (int.of_nat m + 1) + 1) = int.of_nat m + 1 + 1 := 
            begin
              exact rfl,
            end,
            have hsimp3 : (abs (↑m + 1) + 1) * C = (abs (int.of_nat m + 1) + 1) * C := by refl,
            rw hsimp3,
            rw hsimp2,
            rw hsimp1 at haux2,
            linarith,
          }
        },
    end,

    -- m ≤ 0 
    have haux_m_neg : ∀ m : ℕ, ∀ n : ℤ, 
    abs (f.func (-[1+ m] * n) - -[1+ m] * f.func n) < (abs -[1+ m] + 1) * C := 
    begin
      intro m,
      induction m,
      {
        intro n,
        have hsimp0 : -[1+0] = -1 :=
          by exact rfl,
        
        simp [hsimp0],

        have hsimp1 : f.func (-n) + f.func n 
        = (f.func (-n) + f.func n - f.func(n - n)) + f.func 0 :=
          by simp,

        calc abs (f.func (-n) + f.func n)
        = abs(f.func (-n) + f.func n - f.func(n - n) + f.func 0) : by simp
        ... ≤ abs (f.func (-n) + f.func n - f.func(n - n)) + abs (f.func 0) : _
        ... < C + C : _
        ... = (1 + 1) * C : by linarith,
        {
          exact abs_add (f.func (-n) + f.func n - f.func (n - n)) (f.func 0),
        },
        {
          have haux1 : abs (f.func (-n) + f.func n - f.func (n - n)) < C :=
          begin
            have hmember : (f.func (n-n) - f.func(-n) - f.func n) ∈ s_hom_err :=
              begin
                simp,
                apply exists.intro n,
                apply exists.intro (-n),
                simp,
              end,
            have haux1_1 : abs((f.func (n-n) - f.func(-n) - f.func n)) < C :=
              by exact h (f.func (n - n) - f.func (-n) - f.func n) hmember,
            
            have hsimp: abs (f.func (n-n) - f.func (-n) - f.func n) 
            = abs (f.func (-n) + f.func n - f.func (n - n)) :=
            begin
              have hsimp_simp : (f.func (n-n) - f.func (-n) - f.func n) 
              = - (f.func (-n) + f.func n - f.func (n - n)) :=
                by linarith,
              rw hsimp_simp,
              exact abs_neg (f.func (-n) + f.func n - f.func (n - n)),
            end,
            rw hsimp at haux1_1,
            exact haux1_1,
          end,
          have haux2 : abs(f.func 0) < C :=
          begin
            have hmem : f.func 0 - f.func 0 - f.func 0 ∈ s_hom_err := 
            begin
              simp,
              apply exists.intro (int.of_nat 0),
              apply exists.intro (int.of_nat 0),
              simp,
            end,

            have hsimp1 : abs(f.func 0) = abs (- f.func 0) :=
              by simp [abs_neg (f.func 0)],
            have hsimp2 : -f.func 0 = f.func 0 - f.func 0 - f.func 0 := 
            by linarith,
            rw hsimp1,
            rw hsimp2,
            exact h (f.func 0 - f.func 0 - f.func 0) hmem,
          end,
          exact add_lt_add haux1 haux2,
        },
      },
      {
        sorry,
      },

    end,

    -- m : ℤ 
    have haux : ∀ m n : ℤ, 
    abs(f.func (m*n) - m * f.func n) < (abs (m) + 1) * C := 
    begin
      intros m n,
      cases' m, -- m is positive or negative
      simp,
      simp at haux_m_nat,
      exact haux_m_nat m n,
      exact haux_m_neg m n,
    end,

    apply exists.intro C,
    intros m n,
    have h1 : abs (f.func(m*n) - m*f.func(n)) < (abs(m) + 1) * C := haux m n,
    have h2 : abs (n*f.func(m) - f.func(m*n)) < (abs(n) + 1) * C := 
      begin
        have hsimp : abs (n*f.func(m) - f.func(m*n)) 
        = abs (f.func(m*n) - n*f.func(m)) :=
          by exact abs_sub (n * f.func m) (f.func (m * n)),
        rw hsimp,
        have hsimp2 : m*n = n*m := by linarith,
        rw hsimp2,
        exact haux n m,
      end,
    calc abs (m * f.func n - n * f.func m)
      = abs (f.func (m * n) - m * f.func n + n * f.func m - f.func (m * n)) : _
      ... ≤ abs (f.func (m * n) - m * f.func n) + abs (n * f.func m - f.func (m * n)) : _
      ... < (abs m + 1) * C + (abs n + 1) * C : by exact add_lt_add h1 h2
      ... = (abs m + abs n + 2) * C : by linarith,
      {
        have hsimp : m * f.func n - n * f.func m 
        = - (f.func (m * n) - m * f.func n + n * f.func m - f.func (m * n)) :=
        begin
          linarith,
        end,
        rw hsimp,
        exact abs_neg (f.func (m * n) - m * f.func n + n * f.func m - f.func (m * n)), 
      },
      {
        let a := f.func (m * n) - m * f.func n,
        have a_def : f.func (m * n) - m * f.func n = a := by refl,
        let b := n * f.func m - f.func (m * n),
        have b_def : n * f.func m - f.func (m * n) = b := by refl,
        rw a_def,
        have hsimp : a + n * f.func m - f.func (m * n) = 
        a + (n * f.func m - f.func (m * n)) := by linarith,
        rw hsimp,
        rw b_def,
        exact abs_add a b,
      },
  end 

lemma lemma8 (f : almost_homs) : 
∃ A B : ℤ, ∀ m : ℤ, abs (f.func m) < A * abs(m) + B := 
  begin
    cases' (lemma7 f) with C,
    apply exists.intro (C + abs (f.func 1)), 
    apply exists.intro (3*C),
    intro m,
    have haux1 : abs (m * f.func 1 - 1 * f.func m) < (abs m + abs 1 + 2) * C := 
    by exact (h m 1),
    simp at haux1,
    have haux2 : abs (f.func m) - abs (m * f.func 1) ≤  abs (f.func m - m * f.func 1) :=
      by apply abs_sub_abs_le_abs_sub,
    have hsimp1 : abs (m * f.func 1 - f.func m) = abs (f.func m - m * f.func 1) :=
      by exact abs_sub (m * f.func 1) (f.func m),
    rw hsimp1 at haux1,
    have haux3 : abs (f.func m) - abs (m * f.func 1) < (abs m + 1 + 2) * C :=
      by apply lt_of_le_of_lt haux2 haux1,
    have haux4 : abs (f.func m) < (abs m + 1 + 2) * C + abs (m * f.func 1) :=
      by exact sub_lt_iff_lt_add.mp haux3,

    have hsimp2 : abs (m * f.func 1) = abs (m) * abs(f.func 1) :=
      by exact abs_mul m (f.func 1),
    have hsimp3 : (abs m + 1 + 2) * C + abs (m) * abs(f.func 1)
      = (C + abs (f.func 1)) * abs m + 3 * C :=
        by linarith,
    simp [hsimp2, hsimp3] at haux4,
    exact haux4,
  end

@[instance] def has_mul : has_mul almost_homs :=
{ mul := λf g : almost_homs,
    { func:= f.func ∘ g.func,
      almost_hom         :=
        begin
          simp [almost_hom],
          apply bounded_intset_is_finite,
          cases' (hbounded_error f) with Cf hCf,
          cases' (hbounded_error g) with Cg hCg,

          have haux1 : ∀ m n : ℤ, abs(f.func(g.func m + g.func n) 
              - f.func (g.func m) - f.func (g.func n)) < Cf :=
              begin
                intros m n,
                apply (hCf (g.func n) (g.func m)),
              end,

          have haux2 : ∀ m n : ℤ, abs(f.func(g.func (m + n)) 
              - f.func (g.func (m + n) - g.func m - g.func n) 
              - f.func (g.func m + g.func n)) < Cf :=
              begin
                intros m n,
                let h := (hCf (g.func m + g.func n) (g.func(m + n) - g.func m - g.func n)),
                simp at *,
                apply h,
              end,

          have haux3 : ∃ C, ∀ m n : ℤ, 
          abs(f.func(g.func (m + n) - g.func m - g.func n)) < C :=
          begin
            let sg := {x | ∃ m n : ℤ, x = g.func(n + m) - g.func(n) - g.func(m)},
            have hsg_fin : sg.finite := g.almost_hom,
            let sfg := {x | ∃ y ∈ sg, x = (f.func y)},
            have hfabs_fin : set.finite sfg :=
              by exact set.finite.dependent_image hsg_fin (λ (x : ℤ) (hx : x ∈ sg), (f.func x)),
            cases' (finset_exists_bound sfg _ hfabs_fin),
            {
              apply exists.intro ((abs w) + 1),
              intros m n,
              have haux1 : (g.func (m + n) - g.func m - g.func n) ∈ sg := 
              begin
                simp,
                apply exists.intro n,
                apply exists.intro m,
                refl,
              end,
              have haux2 : (f.func(g.func (m + n) - g.func m - g.func n)) ∈ sfg :=
              begin
                simp,
                apply exists.intro (g.func (m + n) - g.func m - g.func n),
                apply and.intro,
                apply exists.intro n,
                apply exists.intro m,
                refl,
                refl,
              end, 
              cases' h with w hw,
              have haux3 : abs w < abs w + 1 := 
                by exact lt_add_one (abs w),
              exact lt_of_le_of_lt (hw (f.func (g.func (m + n) - g.func m - g.func n)) haux2) haux3,
            },
            {
              simp [set.nonempty_def],
              apply exists.intro (f.func(- g.func 0)),
              apply exists.intro (- g.func 0),
              apply and.intro,
              apply exists.intro (int.of_nat 0),
              apply exists.intro (int.of_nat 0),
              simp,
            },
          end, 

          have haux4 : 
          ∀ m n : ℤ, 
          f.func(g.func (m + n)) - f.func (g.func m) - f.func (g.func n) =
          f.func(g.func m + g.func n) - f.func (g.func m) - f.func (g.func n)
          + (f.func(g.func (m + n)) - f.func (g.func (m + n) - g.func m - g.func n) - f.func (g.func m + g.func n))
          + (f.func(g.func (m + n) - g.func m - g.func n)) :=
          by intros m n; linarith,

          cases' haux3 with C,

          have haux5 : 
          ∀ m n : ℤ, 
          abs (f.func(g.func (m + n)) - f.func (g.func m) - f.func (g.func n)) < 2*Cf + C 
          := 
          begin
            intros m n,
            calc abs (f.func(g.func (m + n)) - f.func (g.func m) - f.func (g.func n))
            = abs (f.func(g.func m + g.func n) - f.func (g.func m) - f.func (g.func n)
              + (f.func(g.func (m + n)) - f.func (g.func (m + n) - g.func m - g.func n) - f.func (g.func m + g.func n))
              + (f.func(g.func (m + n) - g.func m - g.func n))) : by simp [haux4]
            ... ≤ abs (f.func(g.func m + g.func n) - f.func (g.func m) - f.func (g.func n))
              + abs(f.func(g.func (m + n)) - f.func (g.func (m + n) - g.func m - g.func n) - f.func (g.func m + g.func n)) 
              + abs(f.func(g.func (m + n) - g.func m - g.func n)) : _
            ... < Cf + Cf + C : by exact add_lt_add (add_lt_add (haux1 m n) (haux2 m n)) (h m n)
            ... = 2 * Cf + C : by linarith,
            {
              exact abs_add_three (f.func (g.func m + g.func n) - f.func (g.func m) - f.func (g.func n))
              (f.func (g.func (m + n)) - f.func (g.func (m + n) - g.func m - g.func n) - f.func (g.func m + g.func n))
              (f.func (g.func (m + n) - g.func m - g.func n)),
            },
          end,
        
          apply exists.intro (2*Cf + C),
          intro x,
          simp,
          intros m n hx,
          rw hx,
          apply (haux5 n m),
        end,
    } 
}

@[simp] lemma mul_func (f g : almost_homs): 
  (f * g).func = f.func ∘ g.func :=
  by refl

lemma one_mul {f : almost_homs} :
  1 * f ≈ f :=
  by simp [setoid_iff]

lemma mul_equiv_mul {f f' g g' : almost_homs} 
(hff' : f ≈ f') (hgg' : g ≈ g') :
  f * g ≈ f' * g' :=
  begin
    simp [setoid_iff] at *,
    apply bounded_intset_is_finite,
    set sff' := {x : ℤ | ∃ (n : ℤ), x = f.func n - f'.func n} with sff'_def,
    set sgg' := {x : ℤ | ∃ (n : ℤ), x = g.func n - g'.func n} with sgg'_def,

    have hnonemptyf : set.nonempty sff' := 
    begin
      simp [set.nonempty_def],
      apply exists.intro  (f.func 0 - f'.func 0),
      apply exists.intro (int.of_nat 0),
      simp,
    end,
    have hnonemptyg : set.nonempty sgg' := 
    begin
      simp [set.nonempty_def],
      apply exists.intro  (g.func 0 - g'.func 0),
      apply exists.intro (int.of_nat 0),
      simp,
    end,
    cases' (finset_exists_stict_bound sff' hnonemptyf hff') with Cff' hCff',
    cases' (finset_exists_stict_bound sgg' hnonemptyg hgg') with Cgg' hCgg',
    
    have haux1 : ∀ n : ℤ, 
    abs (f.func (g.func n) - f'.func (g.func n)) < Cff' :=
    begin
      intro n,
      have hmember : f.func (g.func n) - f'.func (g.func n) ∈ sff' :=
      begin
        simp,
        apply exists.intro (g.func n),
        refl,
      end, 
      apply (hCff' (f.func (g.func n) - f'.func (g.func n)) hmember),
    end,

    let sf' := {x | ∃ m n : ℤ, x = f'.func(n + m) - f'.func(n) - f'.func(m)},
    have hsg_fin : sf'.finite := f'.almost_hom,
    cases' (hbounded_error f') with Cf' hCf',

    have haux2 : ∀ n : ℤ,
    abs (f'.func(g.func n) - f'.func(g.func n - g'.func n) - f'.func (g'.func n)) < Cf' :=
    begin
      intro n,
      have hsimp : f'.func (g.func n) = f'.func(g.func n - g'.func n + g'.func n) := by simp,
      rw hsimp,
      apply (hCf' (g'.func n) (g.func n - g'.func n)),
    end,

    have haux3 : ∃ C : ℤ, ∀ n : ℤ, 
    abs (f'.func (g.func n - g'.func n)) < C :=
    begin
      set sf'g := {x | ∃ y ∈ sgg', x = f'.func y} with sf'g_def,
      have hfin : set.finite sf'g :=
        by exact set.finite.dependent_image hgg' (λ (x : ℤ) (hx : x ∈ sgg'), f'.func x),
      have hnonempty : set.nonempty sf'g :=
      begin
        simp [set.nonempty_def],
        apply exists.intro (f'.func (g.func 0 - g'.func 0)),
        apply exists.intro ((g.func 0 - g'.func 0)),
        apply and.intro,
        apply exists.intro (int.of_nat 0),
        refl,
        refl,        
      end,
      cases' (finset_exists_stict_bound sf'g hnonempty hfin) with C hC,
      apply exists.intro C,
      simp [sf'g_def] at hC,
      exact hC,
    end,

    cases' haux3 with C,

    have hrw : ∀ n : ℤ,
    f.func (g.func n) - f'.func (g'.func n) 
    = 
    (f.func (g.func n) - f'.func (g.func n))
    + (f'.func(g.func n) - f'.func(g.func n - g'.func n) - f'.func (g'.func n))
    + (f'.func (g.func n - g'.func n)) := by intro n; linarith,

    apply exists.intro (Cff' + Cf' + C),
    --intros x hx,

    have haux4 : ∀ n : ℤ,
    abs (f.func (g.func n) - f'.func (g'.func n)) < Cff' + Cf' + C := 
    begin
      intro n,

      calc abs (f.func (g.func n) - f'.func (g'.func n))
      = abs((f.func (g.func n) - f'.func (g.func n))
      + (f'.func(g.func n) - f'.func(g.func n - g'.func n) - f'.func (g'.func n))
      + (f'.func (g.func n - g'.func n))) : by rw hrw
      ... ≤ abs (f.func (g.func n) - f'.func (g.func n))
      + abs (f'.func(g.func n) - f'.func(g.func n - g'.func n) - f'.func (g'.func n))
      + abs (f'.func (g.func n - g'.func n)) : _
      ... < Cff' + Cf' + C : _,
      {
        exact abs_add_three (f.func (g.func n) - f'.func (g.func n))
        (f'.func (g.func n) - f'.func (g.func n - g'.func n) - f'.func (g'.func n))
        (f'.func (g.func n - g'.func n)),  
      },
      {
        apply add_lt_add (add_lt_add (haux1 n) (haux2 n)) (h n),
      }
    end,

    simp,
    exact haux4,
  end

end almost_homomorphisms

namespace Eudoxus_Reals

def Eudoxus_Reals : Type := 
quotient almost_homomorphisms.setoid

@[instance] def has_add : has_add Eudoxus_Reals :=
{ add := quotient.lift₂ (λf g : almost_homs, ⟦f + g⟧)
    begin
      intros f g f' g' hf hg,
      apply quotient.sound,
      exact almost_homomorphisms.add_equiv_add hf hg,
    end }

@[instance] def has_mul : has_mul Eudoxus_Reals :=
{ mul := quotient.lift₂ (λf g : almost_homs, ⟦f * g⟧)
    begin
      intros f g f' g' hf hg,
      apply quotient.sound,
      exact almost_homomorphisms.mul_equiv_mul hf hg,
    end }

@[instance] def has_zero : has_zero Eudoxus_Reals :=
{ zero := ⟦0⟧ }

lemma zero_add (x : Eudoxus_Reals) : 0 + x = x :=
begin 
  apply quotient.induction_on x,
  intro x',
  apply quotient.sound,
  apply almost_homomorphisms.zero_add,
end 

@[instance] def has_one : has_one Eudoxus_Reals :=
{ one := ⟦1⟧ }

lemma add_commutes (a b : Eudoxus_Reals) : 
  a+b=b+a :=
  begin
    apply quotient.induction_on₂ a b,
    intros a' b',
    apply quotient.sound,
    simp [almost_homomorphisms.setoid_iff],
    have haux : a'.func + b'.func - (b'.func + a'.func) = 0 :=
    begin
      have hauxaux: a'.func + b'.func = b'.func + a'.func :=
        by exact add_comm a'.func b'.func,
      exact sub_eq_zero.mpr hauxaux,
    end,
    have haux2 : ∀ n, a'.func n + b'.func n - (b'.func n + a'.func n) = 0 :=
      by exact congr_fun haux,
    simp [haux2],
  end

end Eudoxus_Reals

end LoVe
