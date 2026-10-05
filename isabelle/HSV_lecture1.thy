theory HSV_lecture1 imports Complex_Main begin

(* Monday 5th October 2026 *)

find_theorems "_ \<in> \<rat>"

thm Rats_abs_nat_div_natE

theorem sqrt2_irrational: "sqrt 2 \<notin> \<rat>"
proof
  assume "sqrt 2 \<in> \<rat>"
  then obtain m n where "\<bar>sqrt 2\<bar> = real m / real n" and thm1: "coprime m n" and "n \<noteq> 0" 
    using Rats_abs_nat_div_natE by metis

  hence eq1: "2 * n^2 = m^2"
    by (smt (verit, ccfv_threshold) divide_eq_eq_numeral(1) numeral_Bit0_eq_double numeral_One of_nat_1
        of_nat_eq_iff of_nat_mult of_nat_numeral power2_eq_square power_divide real_sqrt_abs
        real_sqrt_pow2)
  hence fact1: "even m"
    by (metis dvd_mult2 even_power gcd_nat.eq_iff)
  then obtain m' where "m = 2*m'" by auto
  hence "2 * n^2 = (2 * m')^2" using eq1 by presburger
  hence "n^2 = 2*m'^2" by simp
  hence "even (n^2)" by simp
  hence "even n" by simp
  with fact1 and thm1 show False by auto
qed


end