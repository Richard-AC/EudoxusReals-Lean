# Eudoxus Reals
A formalization of Eudoxus Reals in Lean.

Reference: https://arxiv.org/pdf/math/0405454.pdf 

  This project formalizes a construction of the real numbers called the Eudoxus reals.
  
  To do so we first introduce "almost homomorphisms" which are functions `ℤ → ℤ` for which
  the set `{f(m+n) - f(m) - f(n), n m : ℤ}` is finite.
  
  Eudoxus Reals are then defined as equivalence classes of almost homomorphisms.
  With `f ~ g ↔ {f(n) - g(n), n : ℤ}` is finite.
  
  Therefore these are fonctions that grow almost linearily and the growth rate
  represents a given real.
  
  For intuition, the Eudoxus real that represents the real number α will be the 
  equivalence class of `(λ n : ℤ, ⌊α * n⌋)`.
