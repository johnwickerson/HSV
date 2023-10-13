(* Live script from the lecture on 12 October 2023 *)

theory HSV_lecture1 imports Complex_Main begin

find_theorems "_ \<in> \<rat>" 
thm Rats_abs_nat_div_natE

theorem sqrt2_irrational: "sqrt 2 \<notin> \<rat>"
proof 
  assume "sqrt 2 \<in> \<rat>"
  then obtain m n
    where "\<bar>sqrt 2\<bar> = real m / real n" and coprimemn: "coprime m n" and john: "n \<noteq> 0"
    by (rule Rats_abs_nat_div_natE)
  hence "2 = (real m / real n)^2"
    by (metis abs_of_nat of_nat_numeral real_sqrt_abs real_sqrt_power)
  hence "2 = (real m)^2 / (real n)^2"
    by (simp add: power_divide)
  hence "2 * (real n)^2 = (real m)^2"
    by (simp add: john eq_divide_eq_numeral(1))
  hence "2 * n^2 = m^2" 
    by (metis (mono_tags, lifting) of_nat_mult 
      of_nat_numeral of_nat_power_eq_of_nat_cancel_iff)
  hence "even (m^2)"
    by presburger 
  hence meven: "even m"
    by simp
  then obtain m' where "m = 2 * m'" by blast
  hence "2 * n^2 = (2 * m')^2"
    by (simp add: \<open>2 * n\<^sup>2 = m\<^sup>2\<close>)
  hence "2 * n^2 = 4 * m'^2" by simp
  from this have "n^2 = 2 * m'^2" by simp
  hence "even (n^2)" by auto
  hence neven: "even n" by simp
  from neven and meven and coprimemn show False by auto
qed

end