theory LR3_Standard
  imports Compressed_Oracles.CO_Invariants Misc_Luby_Rackoff General_Luby_Rackoff
begin

(* U_UP,i, using standard queries *)
definition UP :: \<open>(whole \<times> whole \<times> db) ell2 \<Rightarrow>\<^sub>C\<^sub>L (whole \<times> whole \<times> db) ell2\<close> where \<open>UP = 
  (reg_1_3 o Fst; reg_2_3 o Snd) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Snd; reg_2_3 o Fst) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Fst; (reg_2_3 o Fst; reg_3_3)) standard_query\<close>

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
