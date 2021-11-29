import ..lovelib

/-! # Project : Eudoxus Reals
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

def almost_hom (f : ℤ → ℤ) : Prop :=
{x | ∃ m n : ℤ, x = f(n + m) - f(n) - f(m)}.finite

structure almost_homs :=
(func         : ℤ → ℤ)
(almost_hom   : almost_hom func)

namespace almost_homomorphisms

-- Almost homomorphisms form an abelian group

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

@[instance] def has_add : has_add almost_homs :=
{ add := λf g : almost_homs,
    { func:= f.func + g.func,
      almost_hom         :=
        begin
          simp [almost_hom],
          let sf := {x | ∃ m n : ℤ, x = f.func(n + m) - f.func(n) - f.func(m)},
          have hsffin : sf.finite := f.almost_hom,
          let sg := {x | ∃ m n : ℤ, x = g.func(n + m) - g.func(n) - g.func(m)},
          have hsgfin : sg.finite := g.almost_hom,
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
            by apply set.finite.image2 (λ a b, a+b) hsffin hsgfin,
          apply set.finite.subset himfin hsub,
        end,
    } 
}

lemma add_comm (f g : almost_homs): 
  f + g = g + f :=
  begin
    cases' f with f_func hf,
    cases' g with g_func hg,
    sorry,
  end

lemma add_equiv_add {f f' g g' : almost_homs} 
(hf : f ≈ f') (hg : g ≈ g') :
  f + g ≈ f' + g' :=
  begin
    simp [setoid_iff] at *, 
    sorry,
  end


@[instance] def almost_homs.add_group : add_group almost_homs :=
{
  add := sorry,
}

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

--lemma add_commutes (a b : Eudoxus_Reals) : 
--  a+b=b+a :=

end Eudoxus_Reals

end LoVe
