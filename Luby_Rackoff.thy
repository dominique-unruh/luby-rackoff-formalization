theory Luby_Rackoff
  imports Compressed_Oracles.CO_Invariants (* Apply_Pure *)
begin

definition cnot :: \<open>('a::ab_group_add \<times> 'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'a) ell2\<close> where
  \<open>cnot = classical_operator (Some o (\<lambda>(x,y). (x, y+x)))\<close>

lemma cnot_apply: \<open>cnot *\<^sub>V ket (x,y) = ket (x, y+x)\<close>
  apply (simp add: cnot_def)
  apply (subst classical_operator_ket)
   apply (rule classical_operator_exists_inj)
  by (auto intro: injI)

type_synonym whole = \<open>half \<times> half\<close>

definition UP :: \<open>(whole \<times> whole \<times> db) ell2 \<Rightarrow>\<^sub>C\<^sub>L (whole \<times> whole \<times> db) ell2\<close> where \<open>UP = 
  (reg_1_3 o Fst; reg_2_3 o Snd) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Snd; reg_2_3 o Fst) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Fst; (reg_2_3 o Fst; reg_3_3)) standard_query\<close>

definition X :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>X = Fst\<close>
definition X1 :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>X1 = Snd o Fst\<close>
definition X2 :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>X2 = Snd o Snd o Fst\<close>
definition Y :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>Y = Snd o Snd o Snd o Fst\<close>
definition D1 :: \<open>db update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>D1 = Snd o Snd o Snd o Snd o Fst\<close>
definition D2 :: \<open>db update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>D2 = Snd o Snd o Snd o Snd o Snd o Fst\<close>
definition D3 :: \<open>db update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>D3 = Snd o Snd o Snd o Snd o Snd o Snd\<close>

fun the_default where
  \<open>the_default d (Some x) = x\<close>
| \<open>the_default d None = d\<close>

lemma [simp]: \<open>compatible reg_1_3 reg_2_3\<close> \<open>compatible reg_1_3 reg_3_3\<close> \<open>compatible reg_2_3 reg_3_3\<close>
  \<open>compatible X X1\<close> \<open>compatible X D1\<close> \<open>compatible X1 D1\<close> \<open>compatible X1 X2\<close> \<open>compatible X1 D3\<close>
  \<open>compatible X2 D3\<close> \<open>compatible X1 D2\<close> \<open>compatible X2 D2\<close> \<open>compatible X2 Y\<close> \<open>compatible Y D3\<close>
            apply (simp_all add: reg_1_3_def reg_2_3_def reg_3_3_def X_def X1_def D1_def X2_def
      D2_def D3_def Y_def)
  by -

lemma sum_of_bool1: \<open>(\<Sum>x::_::finite|P x. of_bool (f x) *\<^sub>C g x) = (\<Sum>x|P x \<and> f x. g x)\<close>
  for g :: \<open>_ \<Rightarrow> 'a::complex_vector\<close>
  by (rule sum.mono_neutral_cong_right, auto)

lemma sum_of_bool2: \<open>(\<Sum>(x::_::finite)\<in>P. of_bool (f x) *\<^sub>C g x) = (\<Sum>x|x\<in>P \<and> f x. g x)\<close>
  for g :: \<open>_ \<Rightarrow> 'a::complex_vector\<close>
  by (rule sum.mono_neutral_cong_right, auto)

lemma [simp]: \<open>(ket x = c *\<^sub>C ket y) \<longleftrightarrow> (c = 1 \<and> x = y)\<close>
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

lemma l1: \<open>(reg_1_3 \<circ> Fst; (reg_2_3 \<circ> Fst; reg_3_3)) standard_query *\<^sub>V ket ((xL, xR), (yL, yR), d)
     = ket ((xL, xR), (yL + the_default 0 (d xL), yR), d)\<close>
  for xL xR yL yR :: half and d :: db
proof -
  have \<open>(reg_1_3 \<circ> Fst; (reg_2_3 \<circ> Fst; reg_3_3)) standard_query *\<^sub>V ket ((xL, xR), (yL, yR), d)
      = (\<Sum>(x, y, d')\<in>UNIV.
           (reg_1_3 \<circ> Fst) (selfbutterket x) *\<^sub>V
           (reg_2_3 \<circ> Fst; reg_3_3) (butterket (y + the_default 0 (d' x), d') (y,d')) *\<^sub>V
           ket ((xL, xR), (yL, yR), d))\<close>
    apply (subst explicit_pair)
      apply simp
     apply (subst standard_query_apply')
     apply simp
    by (simp add: case_prod_beta)
  also have \<open>\<dots> = ket ((xL, xR), (yL + the_default 0 (d xL), yR), d)\<close>
    apply (simp add: register_pair_apply reg_1_3_def reg_2_3_def reg_3_3_def Fst_def Snd_def
        tensor_op_ell2 ket_cinner' tensor_ell2_scaleC2 tensor_ell2_scaleC1
        flip: tensor_butterfly of_bool_conj tensor_ell2_ket)
    apply (subst sum_single[where i=\<open>(xL,yL,d)\<close>])
    by auto
  finally show ?thesis
    by -
qed

lemma l2: \<open>(reg_1_3 \<circ> Snd;reg_2_3 \<circ> Fst) cnot *\<^sub>V ket ((xL, xR), (yL, yR), d) = ket ((xL, xR), (yL + xR, yR), d)\<close>
  apply (subst explicit_pair)
    apply simp
   apply (subst cnot_apply)
   apply simp
  apply (simp add: register_pair_apply reg_1_3_def reg_2_3_def reg_3_3_def Fst_def Snd_def
      tensor_op_ell2 ket_cinner' tensor_ell2_scaleC2 tensor_ell2_scaleC1
      flip: tensor_butterfly of_bool_conj tensor_ell2_ket)
  apply (subst sum_single[where i=\<open>(xR,yL)\<close>])
  by auto

lemma l3: \<open>(reg_1_3 \<circ> Fst;reg_2_3 \<circ> Snd) cnot *\<^sub>V ket ((xL, xR), (yL, yR), d) = ket ((xL, xR), (yL, yR + xL), d)\<close>
  apply (subst explicit_pair)
    apply simp
   apply (subst cnot_apply)
   apply simp
  apply (simp add: register_pair_apply reg_1_3_def reg_2_3_def reg_3_3_def Fst_def Snd_def
      tensor_op_ell2 ket_cinner' tensor_ell2_scaleC2 tensor_ell2_scaleC1
      flip: tensor_butterfly of_bool_conj tensor_ell2_ket)
  apply (subst sum_single[where i=\<open>(xL,yR)\<close>])
  by auto

lemma UP_apply: \<open>UP *\<^sub>V ket ((xL,xR), (yL,yR), d) = ket ((xL, xR), (yL + the_default 0 (d xL) + xR, yR + xL), d)\<close>
  by (simp add: UP_def l1 l2 l3)

lemma UP_apply': \<open>UP *\<^sub>V ket state = (case state of ((xL,xR), (yL,yR), d) \<Rightarrow> ket ((xL, xR), (yL + the_default 0 (d xL) + xR, yR + xL), d))\<close>
  apply (cases state, hypsubst_thin, case_tac c, hypsubst_thin)
  by (simp add: UP_apply)

definition LR3 where \<open>LR3 =
  (X;(X1;D1)) UP o\<^sub>C\<^sub>L (X1;(X2;D2)) UP o\<^sub>C\<^sub>L (X2;(Y;D3)) UP o\<^sub>C\<^sub>L (X1;(X2;D2)) UP o\<^sub>C\<^sub>L (X;(X1;D1)) UP\<close>

lemma up1: \<open>(X;(X1;D1)) UP *\<^sub>V ket ((xL,xR), (x1L,x1R), (x2L,x2R), (yL,yR), d1, d2, d3)
      = ket ((xL, xR), (x1L + the_default 0 (d1 xL) + xR, x1R + xL), (x2L,x2R), (yL,yR), d1, d2, d3)\<close>
  apply (subst explicit_pair)
    apply simp
   apply (subst UP_apply')
   apply (simp add: case_prod_beta split del: split_of_bool)
  apply (simp add: register_pair_apply reg_1_3_def reg_2_3_def reg_3_3_def Fst_def Snd_def
      tensor_op_ell2 ket_cinner' tensor_ell2_scaleC2 tensor_ell2_scaleC1 tensor_ell2_ket_split
      X_def X1_def D1_def
      flip: tensor_butterfly of_bool_conj tensor_ell2_ket)
  apply (subst sum_single[where i=\<open>((xL, xR), (x1L, x1R), d1)\<close>])
  by auto

lemma up2: \<open>(X1;(X2;D2)) UP *\<^sub>V ket ((xL,xR), (x1L,x1R), (x2L,x2R), (yL,yR), d1, d2, d3)
      = ket ((xL, xR), (x1L, x1R), (x2L + the_default 0 (d2 x1L) + x1R, x2R + x1L), (yL, yR), d1, d2, d3)\<close>
  apply (subst explicit_pair)
    apply simp
   apply (subst UP_apply')
   apply (simp add: case_prod_beta split del: split_of_bool)
  apply (simp add: register_pair_apply reg_1_3_def reg_2_3_def reg_3_3_def Fst_def Snd_def
      tensor_op_ell2 ket_cinner' tensor_ell2_scaleC2 tensor_ell2_scaleC1 tensor_ell2_ket_split
      X_def X1_def D1_def D3_def X2_def D2_def
      flip: tensor_butterfly of_bool_conj tensor_ell2_ket)
  apply (subst sum_single[where i=\<open>((x1L, x1R), (x2L, x2R), d2)\<close>])
  by auto

lemma up3: \<open>(X2;(Y;D3)) UP *\<^sub>V ket ((xL,xR), (x1L,x1R), (x2L,x2R), (yL,yR), d1, d2, d3)
      = ket ((xL, xR), (x1L, x1R), (x2L, x2R), (yL + the_default 0 (d3 x2L) + x2R, yR + x2L), d1, d2, d3)\<close>
  apply (subst explicit_pair)
    apply simp
   apply (subst UP_apply')
   apply (simp add: case_prod_beta split del: split_of_bool)
  apply (simp add: register_pair_apply reg_1_3_def reg_2_3_def reg_3_3_def Fst_def Snd_def
      tensor_op_ell2 ket_cinner' tensor_ell2_scaleC2 tensor_ell2_scaleC1 tensor_ell2_ket_split
      X_def X1_def D1_def D3_def X2_def D2_def Y_def
      flip: tensor_butterfly of_bool_conj tensor_ell2_ket)
  apply (subst sum_single[where i=\<open>((x2L, x2R), (yL, yR), d3)\<close>])
  by auto

lemma test: 
  shows \<open>LR3 *\<^sub>V ket ((xL,xR), 0, 0, 0, Some o d1, Some o d2, Some o d3) = ket ((xL,xR), 0, 0,
      (d3 (d2 (d1 xL + xR) + xL) + d1 xL + xR, d2 (d1 xL + xR) + xL), 
    Some o d1, Some o d2, Some o d3)\<close>
  by (simp add: LR3_def zero_prod_def up1 up2 up3 add.commute add.left_commute)

end
