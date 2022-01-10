theory Misc_Luby_Rackoff
  imports Compressed_Oracles.CO_Invariants
begin

definition cnot :: \<open>('a::ab_group_add \<times> 'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'a) ell2\<close> where
  \<open>cnot = classical_operator (Some o (\<lambda>(x,y). (x, y+x)))\<close>

lemma cnot_apply: \<open>cnot *\<^sub>V ket (x,y) = ket (x, y+x)\<close>
  apply (simp add: cnot_def)
  apply (subst classical_operator_ket)
   apply (rule classical_operator_exists_inj)
  by (auto intro: injI)

fun the_default where
  \<open>the_default d (Some x) = x\<close>
| \<open>the_default d None = d\<close>

lemma sum_of_bool1: \<open>(\<Sum>x::_::finite|P x. of_bool (f x) *\<^sub>C g x) = (\<Sum>x|P x \<and> f x. g x)\<close>
  for g :: \<open>_ \<Rightarrow> 'a::complex_vector\<close>
  by (rule sum.mono_neutral_cong_right, auto)

lemma sum_of_bool2: \<open>(\<Sum>(x::_::finite)\<in>P. of_bool (f x) *\<^sub>C g x) = (\<Sum>x|x\<in>P \<and> f x. g x)\<close>
  for g :: \<open>_ \<Rightarrow> 'a::complex_vector\<close>
  by (rule sum.mono_neutral_cong_right, auto)

lemma ket_eq_scaleC_ket[simp]: \<open>(ket x = c *\<^sub>C ket y) \<longleftrightarrow> (c = 1 \<and> x = y)\<close>
  by (metis cinner_scaleC_right mult_cancel_left1 orthogonal_ket scaleC_cancel_right scaleC_one)

lemma ket_cinner': \<open>cinner (ket x) (ket y) = of_bool (x=y)\<close>
  by (simp add: cinner_ket)

lemma tensor_ell2_ket_split: \<open>ket xy = ket (fst xy) \<otimes>\<^sub>s ket (snd xy)\<close>
  by auto

lemma explicit_pair: 
  fixes f g \<alpha> F G U
  assumes [simp]: \<open>compatible F G\<close>
  assumes U: \<open>\<And>x y. U *\<^sub>V ket (x,y) = of_bool (h x y) *\<^sub>C ket (f x y, g x y)\<close>
  shows \<open>(F;G) U *\<^sub>V \<psi> = (\<Sum>(x,y)|h x y. F (butterket (f x y) x)
               *\<^sub>V (G (butterket (g x y) y) *\<^sub>V \<psi>))\<close>
proof -
  have \<open>U *\<^sub>V ket (x,y) = (\<Sum>(x,y)\<in>UNIV. of_bool (h x y) *\<^sub>C butterket (f x y, g x y) (x, y)) *\<^sub>V ket (x,y)\<close> for x y
    apply (subst U)
    apply (auto simp: cblinfun.sum_left case_prod_beta ket_cinner' split del: split_of_bool)
    apply (subst sum_single[where i=\<open>(x,y)\<close>])
    by auto
  then have U2: \<open>U = (\<Sum>(x,y)\<in>UNIV. of_bool (h x y) *\<^sub>C butterket (f x y, g x y) (x, y))\<close>
    apply (rule_tac equal_ket, case_tac x) by simp
  show ?thesis
    by (simp add: U2 complex_vector.linear_sum clinear.scaleC tensor_ell2_ket_split
        register_pair_apply sum_of_bool2 cblinfun.sum_left case_prod_unfold
        flip: tensor_butterfly cinner_ket tensor_ell2_ket)
qed

lemma standard_query1_apply: \<open>standard_query1 *\<^sub>V ket (x, d) = ket (x + the_default 0 d, d)\<close>
  apply (cases d) by auto

lemma function_at_selfbutterket_apply: \<open>function_at x (selfbutterket y) *\<^sub>V ket h = of_bool (h x = y) *\<^sub>C ket h\<close>
  apply (simp add: function_at_def Let_def sandwich_def classical_operator_ket classical_operator_adjoint
      bij_fix_punctured_function bij_is_inj bij_is_surj inv_map_total Fst_def tensor_ell2_ket_split
      tensor_op_ell2 tensor_ell2_scaleC1 ket_cinner'
      flip: tensor_ell2_ket
      split del: split_of_bool)
  apply (simp add: classical_operator_ket tensor_op_ell2 tensor_ell2_scaleC1
      split del: split_of_bool)
  apply transfer
  apply (auto intro!: ext simp: o_def)
  apply (metis transpose_apply_second transpose_involutory)
  by (metis transpose_apply_second transpose_involutory)

lemma l4: \<open>(Fst;Snd \<circ> function_at x) standard_query1 *\<^sub>V ket (y, h) = ket (y + the_default 0 (h x), h)\<close>
  apply (subst explicit_pair)
    apply simp
   apply (simp add: standard_query1_apply split del: split_of_bool)
  apply (simp add: complex_vector.linear_sum clinear.scaleC tensor_ell2_ket_split
        register_pair_apply sum_of_bool2 cblinfun.sum_left case_prod_unfold
        Fst_def tensor_op_ell2 ket_cinner' function_at_selfbutterket_apply
        flip: tensor_butterfly cinner_ket tensor_ell2_ket)
  apply (subst sum_single[where i=\<open>(y, h x)\<close>])
  by auto

lemma standard_query_apply:
  \<open>standard_query (ket (x,y,d)) = ket (x, y + the_default 0 (d x), d)\<close>
  by (simp add: standard_query_def l4)

lemma standard_query_apply':
  \<open>standard_query (ket xyd) = ket
       ((case xyd of (x,y,d) \<Rightarrow> x), 
        (case xyd of (x,y,d) \<Rightarrow> y + the_default 0 (d x)),
        (case xyd of (x,y,d) \<Rightarrow> d))\<close>
  by (cases xyd, simp add: standard_query_apply)


end
