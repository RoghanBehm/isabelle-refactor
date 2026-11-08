theory AU_Eval
  imports
    Refactor.Refactor_Setup
    "HOL-Library.Extended_Nat"
    "HOL-Library.Extended_Nonnegative_Real"
    "HOL-Computational_Algebra.Primes"
    "HOL-Number_Theory.Cong"
begin

text \<open>
  Case studies for the generalisation (anti-unification) refactoring.

  Each pair restates two library lemmas, linked in the text before it. Before the
  tool was run, each restatement was proved from its original by \<open>fact\<close>.
  Running the tool on a pair inserts the generalised lemma \<open>auN_gen\<close> above
  the pair and replaces the restatements' proofs with instances of it. The
  generalised lemmas are the tool's output, unchanged except for their proofs, 
where:
  \<sqdot> a proof found by Sledgehammer is kept;
  \<sqdot> \<open>sorry\<close> or \<open>oops\<close> marks a statement that Sledgehammer did not prove
    (oops was just used occassionally to keep the fake proof out of 
    sledgehammer's context)
\<close>


section \<open>Pair 1 (exact): \<open>nat\<close> and \<open>enat\<close>, then \<open>ennreal\<close> with the generalised stmt\<close>

text \<open>
  @{thm [source] Nat.nat_0_less_mult_iff} in \<open>~~/src/HOL/Nat.thy\<close>,
  @{thm [source] Extended_Nat.enat_0_less_mult_iff} in
  \<open>~~/src/HOL/Library/Extended_Nat.thy\<close>, and
  @{thm [source] Extended_Nonnegative_Real.ennreal_zero_less_mult_iff} in
  \<open>~~/src/HOL/Library/Extended_Nonnegative_Real.thy\<close>.

  \<open>au1_gen\<close> generalises the \<open>nat\<close> and \<open>enat\<close> lemmas, and
  \<open>au1_gen_ennreal\<close> generalises \<open>au1_gen\<close> with the \<open>ennreal\<close> lemma.
\<close>

lemma au1_gen_ennreal:
  fixes G2 G3 :: "'T1::{term_of,conditionally_complete_linorder,minus,strict_ordered_ab_semigroup_add,distrib_lattice,topological_comm_monoid_add,order_bot,dioid,linordered_nonzero_semiring,semiring_no_zero_divisors,linorder_topology}"
  shows "(0 < G2 * G3) = (0 < G2 \<and> 0 < G3)"
  using zero_order(4) by fastforce

lemma au1_gen:
  fixes m0 n0 :: "'T0::{conditionally_complete_linorder,countable,linordered_ab_semigroup_add,minus,strict_ordered_comm_monoid_add,equal,distrib_lattice,topological_comm_monoid_add,order_bot,wellorder,full_exhaustive,narrowing,partial_term_of,random,dioid,linordered_nonzero_semiring,semiring_no_zero_divisors,linorder_topology}"
  shows "(0 < m0 * n0) = (0 < m0 \<and> 0 < n0)"
  by (fact au1_gen_ennreal)

lemma au1_nat: "0 < m * n \<longleftrightarrow> 0 < m \<and> 0 < n" for m n :: nat
  by (fact au1_gen)
lemma au1_enat: "0 < m * n \<longleftrightarrow> 0 < m \<and> 0 < n" for m n :: enat
  by (fact au1_gen)
lemma au1_ennreal: "0 < a * b \<longleftrightarrow> 0 < a \<and> 0 < b" for a b :: ennreal
  by (fact au1_gen_ennreal)


section \<open>Pair 2 (exactt)\<close>

text \<open>
  @{thm [source] Euclidean_Rings.mod_less_divisor} and
  @{thm [source] Euclidean_Rings.pos_mod_bound} in
  \<open>~~/src/HOL/Euclidean_Rings.thy\<close>.
\<close>

lemma au2_gen:
  fixes G1 G2 :: "'T0::{linordered_euclidean_semiring_bit_operations,conditionally_complete_linorder,countable,euclidean_semiring_gcd,normalization_euclidean_semiring_multiplicative,semiring_gcd_mult_normalize,equal,distrib_lattice,topological_comm_monoid_add,topological_comm_monoid_mult,interval,no_top,linordered_euclidean_semiring_division,check_prime_by_range,exhaustive,full_exhaustive,narrowing,partial_term_of,random,comm_semiring_1_cancel_crossproduct,discrete_topology,linorder_topology}"
  shows "0 < G1 \<Longrightarrow> G2 mod G1 < G1"
  sorry

lemma au2_nat: "0 < n \<Longrightarrow> m mod n < n" for m n :: nat
  by (fact au2_gen)
lemma au2_int: "0 < l \<Longrightarrow> k mod l < l" for k l :: int
  by (fact au2_gen)


section \<open>Pair 3 (exact)\<close>

text \<open>
  @{thm [source] Nat.dvd_imp_le} in \<open>~~/src/HOL/Nat.thy\<close> and
  @{thm [source] Int.zdvd_imp_le} in \<open>~~/src/HOL/Int.thy\<close>.
\<close>

lemma au3_gen:
  fixes G1 n0 :: "'T0::{linordered_euclidean_semiring_bit_operations,conditionally_complete_linorder,countable,euclidean_semiring_gcd,normalization_euclidean_semiring_multiplicative,semiring_gcd_mult_normalize,equal,distrib_lattice,topological_comm_monoid_add,topological_comm_monoid_mult,interval,no_top,linordered_euclidean_semiring_division,check_prime_by_range,exhaustive,full_exhaustive,narrowing,partial_term_of,random,comm_semiring_1_cancel_crossproduct,discrete_topology,linorder_topology}"
  shows "G1 dvd n0 \<Longrightarrow> 0 < n0 \<Longrightarrow> G1 \<le> n0"
  sorry

lemma au3_nat: "k dvd n \<Longrightarrow> 0 < n \<Longrightarrow> k \<le> n" for k n :: nat
  by (fact au3_gen)
lemma au3_int: "z dvd n \<Longrightarrow> 0 < n \<Longrightarrow> z \<le> n" for n z :: int
  by (fact au3_gen)


section \<open>Pair 4 (exact)\<close>

text \<open>
  @{thm [source] Primes.prime_gt_0_nat} and @{thm [source] Primes.prime_gt_0_int}
  in \<open>~~/src/HOL/Computational_Algebra/Primes.thy\<close>.
\<close>

lemma au4_gen:
  fixes p0 :: "'T0::{linordered_euclidean_semiring_bit_operations,conditionally_complete_linorder,countable,euclidean_semiring_gcd,normalization_euclidean_semiring_multiplicative,semiring_gcd_mult_normalize,equal,distrib_lattice,topological_comm_monoid_add,topological_comm_monoid_mult,interval,no_top,linordered_euclidean_semiring_division,check_prime_by_range,exhaustive,full_exhaustive,narrowing,partial_term_of,random,comm_semiring_1_cancel_crossproduct,discrete_topology,linorder_topology}"
  shows "prime p0 \<Longrightarrow> 0 < p0"
  using order_less_trans prime_iff zero_less_one by blast

lemma au4_nat: "prime p \<Longrightarrow> 0 < p" for p :: nat
  by (fact au4_gen)
lemma au4_int: "prime p \<Longrightarrow> 0 < p" for p :: int
  by (fact au4_gen)


section \<open>Pair 5 (exact)\<close>

text \<open>
  @{thm [source] Cong.cong_solve_nat} and @{thm [source] Cong.cong_solve_int} in
  \<open>~~/src/HOL/Number_Theory/Cong.thy\<close>.
\<close>

lemma au5_gen:
  fixes a0 n0 :: "'T0::{linordered_euclidean_semiring_bit_operations,conditionally_complete_linorder,countable,euclidean_semiring_gcd,normalization_euclidean_semiring_multiplicative,semiring_gcd_mult_normalize,equal,distrib_lattice,topological_comm_monoid_add,topological_comm_monoid_mult,interval,no_top,linordered_euclidean_semiring_division,check_prime_by_range,exhaustive,full_exhaustive,narrowing,partial_term_of,random,comm_semiring_1_cancel_crossproduct,discrete_topology,linorder_topology}"
  shows "\<exists>a. [a0 * a = gcd a0 n0] (mod n0)"
  sorry

lemma au5_nat: "\<exists>x. [a * x = gcd a n] (mod n)" for a n :: nat
  by (fact au5_gen)
lemma au5_int: "\<exists>x. [a * x = gcd a n] (mod n)" for a n :: int
  by (fact au5_gen)


section \<open>Pair 6 (choice)\<close>

text \<open>
  @{thm [source] GCD.gcd_le1_nat} and @{thm [source] GCD.gcd_le1_int} in
  \<open>~~/src/HOL/GCD.thy\<close>.
\<close>

lemma au6_gen:
  fixes G0 :: "bool" and a0 b0 :: "'T1::{linordered_euclidean_semiring_bit_operations,conditionally_complete_linorder,countable,euclidean_semiring_gcd,normalization_euclidean_semiring_multiplicative,semiring_gcd_mult_normalize,equal,distrib_lattice,topological_comm_monoid_add,topological_comm_monoid_mult,interval,no_top,linordered_euclidean_semiring_division,check_prime_by_range,exhaustive,full_exhaustive,narrowing,partial_term_of,random,comm_semiring_1_cancel_crossproduct,discrete_topology,linorder_topology}"
  shows "G0 \<Longrightarrow> gcd a0 b0 \<le> a0"
  oops



lemma au6_gen_counterexample: "\<not> gcd (0::nat) 1 \<le> 0"
  by simp

lemma au6_nat: "a \<noteq> 0 \<Longrightarrow> gcd a b \<le> a" for a b :: nat
  by (fact GCD.gcd_le1_nat)
lemma au6_int: "0 < a \<Longrightarrow> gcd a b \<le> a" for a b :: int
  by (fact GCD.gcd_le1_int)


section \<open>Pair 7 (\<open>Suc\<close>)\<close>

text \<open>
  @{thm [source] Nat.less_Suc_eq} in \<open>~~/src/HOL/Nat.thy\<close> and
  @{thm [source] Int.zless_add1_eq} in \<open>~~/src/HOL/Int.thy\<close>.
\<close>

lemma au7_gen:
  fixes G1 G2 G3 :: "'T0::{linordered_euclidean_semiring_bit_operations,conditionally_complete_linorder,countable,euclidean_semiring_gcd,normalization_euclidean_semiring_multiplicative,semiring_gcd_mult_normalize,equal,distrib_lattice,topological_comm_monoid_add,topological_comm_monoid_mult,interval,no_top,linordered_euclidean_semiring_division,check_prime_by_range,exhaustive,full_exhaustive,narrowing,partial_term_of,random,comm_semiring_1_cancel_crossproduct,discrete_topology,linorder_topology}"
  shows "(G1 < G2) = (G1 < G3 \<or> G1 = G3)"
  oops



lemma au7_gen_counterexample: "\<not> (((0::nat) < 0) = ((0::nat) < 0 \<or> (0::nat) = 0))"
  by simp

lemma au7_nat: "m < Suc n \<longleftrightarrow> m < n \<or> m = n" for m n :: nat
  by (fact Nat.less_Suc_eq)
lemma au7_int: "w < z + 1 \<longleftrightarrow> w < z \<or> w = z" for w z :: int
  by (fact Int.zless_add1_eq)


section \<open>Pair 8 (union)\<close>

text \<open>
  @{thm [source] Nat.dvd_antisym} in \<open>~~/src/HOL/Nat.thy\<close> and
  @{thm [source] Int.zdvd_antisym_nonneg} in \<open>~~/src/HOL/Int.thy\<close>.

\<close>

lemma au8_gen:
  fixes G0 G1 :: "bool" and G2 :: "prop"
  shows "G0 \<Longrightarrow> G1 \<Longrightarrow> PROP G2"
  oops

lemma au8_nat: "m dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = n" for m n :: nat
  by (fact Nat.dvd_antisym)
lemma au8_int: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> m dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = n" for m n :: int
  by (fact Int.zdvd_antisym_nonneg)


end
