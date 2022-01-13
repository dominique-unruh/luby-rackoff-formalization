theory LR3_Compressed
  imports Compressed_Oracles.CO_Invariants General_Luby_Rackoff
begin

(* U_UP,i, using compressed queries *)
definition UPc :: \<open>(whole \<times> whole \<times> db) ell2 \<Rightarrow>\<^sub>C\<^sub>L (whole \<times> whole \<times> db) ell2\<close> where \<open>UPc = 
  (reg_1_3 o Fst; reg_2_3 o Snd) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Snd; reg_2_3 o Fst) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Fst; (reg_2_3 o Fst; reg_3_3)) query\<close>

(* LR3 using compressed oracles *)
definition LR3c where \<open>LR3c =
  (X;(X1;D1)) UPc o\<^sub>C\<^sub>L (X1;(X2;D2)) UPc o\<^sub>C\<^sub>L (X2;(Y;D3)) UPc o\<^sub>C\<^sub>L (X1;(X2;D2)) UPc o\<^sub>C\<^sub>L (X;(X1;D1)) UPc\<close>

(* Notion of good from the current eprint of the LR4-paper. Note: uniqueness condition missing. *)
definition old_good where \<open>old_good D1 D2 D3 \<longleftrightarrow> (\<forall>x2L \<in> dom D3. \<exists>xL\<in>dom D1. \<exists>\<beta>\<in>ran D2. x2L = xL + \<beta>)\<close>
  for D1 D2 D3 :: db

(* Notion of good from the current eprint of the LR4-paper, more intuitive formulation *)
lemma old_good_alt_def: \<open>old_good D1 D2 D3 \<longleftrightarrow> (\<forall>x2L \<in> dom D3. \<exists>xL xR. do { (x2L',x2R) \<leftarrow> LR2 D1 D2 (xL,xR); Some (x2L=x2L') } = Some True)\<close>
  for D1 D2 D3
proof (unfold old_good_def; intro iffI ballI)
  fix x2L assume x2L_D3: \<open>x2L \<in> dom D3\<close>
  assume \<open>\<forall>x2L\<in>dom D3. \<exists>xL\<in>dom D1. \<exists>\<beta>\<in>ran D2. x2L = xL + \<beta>\<close>
  from this[rule_format, OF x2L_D3]
  obtain xL \<beta> where \<open>xL \<in> dom D1\<close> \<open>\<beta> \<in> ran D2\<close> \<open>x2L = xL + \<beta>\<close>
    by auto
  from \<open>xL \<in> dom D1\<close> obtain \<alpha> where [simp]: \<open>D1 xL = Some \<alpha>\<close>
    by force
  from \<open>\<beta> \<in> ran D2\<close> obtain D2_in where [simp]: \<open>D2 D2_in = Some \<beta>\<close>
    by (smt (verit, del_insts) mem_Collect_eq ran_def)
  have \<open>LR2 D1 D2 (xL, D2_in + \<alpha>) \<bind> (\<lambda>(x2L', x2R). Some (x2L = x2L')) = Some True\<close>
    using \<open>x2L = xL + \<beta>\<close> by (auto simp: LR2_def)
  then show \<open>\<exists>xL xR. LR2 D1 D2 (xL, xR) \<bind> (\<lambda>(x2L', x2R). Some (x2L = x2L')) = Some True\<close>
    by auto
next
  fix x2L assume x2L_D3: \<open>x2L \<in> dom D3\<close>
  assume \<open>\<forall>x2L\<in>dom D3. \<exists>xL xR. LR2 D1 D2 (xL, xR) \<bind> (\<lambda>(x2L', x2R). Some (x2L = x2L')) = Some True\<close>
  from this[rule_format, OF x2L_D3]
  show \<open>\<exists>xL\<in>dom D1. \<exists>\<beta>\<in>ran D2. x2L = xL + \<beta>\<close>
    by (smt (z3) LR2_def bind_eq_Some_conv domI old.prod.case option.inject ranI)
qed

definition old_good_state_00 :: \<open>state set\<close> where \<open>old_good_state_00 = {(x,0,0,y,D1,D2,D3)| x y D1 D2 D3. old_good D1 D2 D3}\<close>
definition old_good_state_0 :: \<open>state set\<close> where \<open>old_good_state_0 = {(x,x1,0,y,D1,D2,D3)| x x1 y D1 D2 D3. old_good D1 D2 D3}\<close>
(* definition old_good_state :: \<open>state set\<close> where \<open>old_good_state = {(x,x1,x2,y,D1,D2,D3). old_good D1 D2 D3}\<close> *)

definition \<open>co1_old_good = 2 / sqrt N\<close>
lemma preserves_co1_old_good:
  \<open>preserves_ket ((X o Fst; (X1 o Fst; D1)) query) old_good_state_00 old_good_state_0 co1_old_good\<close>
proof -
  define K :: \<open>(half\<times>half\<times>whole\<times>db\<times>db\<times>db) \<Rightarrow> state ell2 ccsubspace\<close> 
    where \<open>K = (\<lambda>(xL,xR,y,D1',D2,D3).
          ket_invariant {((xL,xR),(x1L,0),0,y,D1'(xL:=d),D2,D3) | x1L d. True})\<close>
  define M :: \<open>(half\<times>half\<times>whole\<times>db\<times>db\<times>db) set\<close> where
    \<open>M = {(xL,xR,y,D1',D2,D3). D1' xL = None \<and> (\<exists>d. old_good (D1'(xL:=d)) D2 D3)}\<close>

  define I1 J1 :: \<open>(half\<times>half\<times>whole\<times>db\<times>db\<times>db) \<Rightarrow> (half \<times> half option) set\<close> 
    where \<open>I1 = (\<lambda>(xL,xR,y,D1',D2,D3).
          {0} \<times> {d. old_good (D1'(xL:=d)) D2 D3})\<close>
      and \<open>J1 = (\<lambda>(xL,xR,y,D1',D2,D3). 
          UNIV \<times> {d. old_good (D1'(xL:=d)) D2 D3})\<close>

  show ?thesis
  proof (rule inv_split_reg_query[where X=\<open>X o Fst\<close> and Y=\<open>X1 o Fst\<close> and H=\<open>D1\<close> and K=K
        and ?I1.0=\<open>\<lambda>z. ket_invariant (I1 z)\<close> and ?J1.0=\<open>\<lambda>z. ket_invariant (J1 z)\<close>])
    show \<open>(X \<circ> Fst;(X1 \<circ> Fst;D1)) query = (X \<circ> Fst;(X1 \<circ> Fst;D1)) query\<close>
      by simp
    show [simp]: \<open>compatible (X \<circ> Fst) (X1 \<circ> Fst)\<close> \<open>compatible (X \<circ> Fst) D1\<close> \<open>compatible (X1 \<circ> Fst) D1\<close>
      by simp_all
    show \<open>compatible_register_invariant (X1 \<circ> Fst) (K z)\<close> for z
      apply (cases z, hypsubst_thin)
      by (auto simp add: K_def X1_def comp_assoc
          intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst compatible_register_invariant_Fst_comp)
    show \<open>compatible_register_invariant (D1 \<circ> function_at (fst z)) (K z)\<close> for z
      by (auto simp add: K_def D1_def comp_assoc case_prod_beta
          intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst compatible_register_invariant_Fst_comp
          compatible_register_invariant_function_at)
    show \<open>ket_invariant old_good_state_00 \<le> (SUP z\<in>M. K z \<sqinter> lift_invariant (X1 \<circ> Fst;D1 \<circ> function_at (fst z)) (ket_invariant (I1 z)))\<close>
      apply (auto simp add: K_def D1_def lift_Fst_ket_inv ket_invariant_inter ket_invariant_SUP[symmetric] I1_def
          old_good_state_00_def case_prod_beta comp_assoc X1_def M_def zero_prod_def
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv lift_Snd_ket_inv)
      by (metis fun_upd_same fun_upd_triv fun_upd_upd)
    show \<open>K z \<sqinter> lift_invariant (X1 \<circ> Fst;D1 \<circ> function_at (fst z)) (ket_invariant (J1 z)) \<le> ket_invariant old_good_state_0\<close>
      if \<open>z\<in>M\<close> for z
      using that 
      apply (cases z, hypsubst_thin)
      by (auto simp add: K_def lift_Fst_ket_inv ket_invariant_inter ket_invariant_SUP[symmetric] J1_def
          case_prod_beta D1_def comp_assoc X1_def old_good_state_0_def M_def
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv)
    show \<open>orthogonal_spaces (K z) (K z')\<close> if \<open>z\<in>M\<close> \<open>z'\<in>M\<close> \<open>z \<noteq> z'\<close> for z z'
      apply (cases z; cases z')
      using that apply (auto simp: K_def M_def)
      by (metis fun_upd_triv fun_upd_upd)
    show \<open>K z \<le> lift_invariant (X \<circ> Fst) (ket_invariant {fst z})\<close> for z
      by (auto simp: K_def X_def lift_Fst_ket_inv lift_invariant_comp case_prod_beta)
    show [simp]: \<open>0 \<le> co1_old_good\<close>
      by (simp add: co1_old_good_def)
    show \<open>preserves_ket query1 (I1 z) (J1 z) co1_old_good\<close> if \<open>z\<in>M\<close> for z
    proof (cases z)
      case (fields xL xR y D1' D2 D3)
      from that have D1'xL: \<open>D1' xL = None\<close>
        by (auto simp: M_def fields)
      show ?thesis
      proof (cases \<open>old_good D1' D2 D3\<close>)
        case True
        show ?thesis
          apply (simp only: case_prod_beta I1_def J1_def fst_conv snd_conv fields)
        proof (rule preserve_query1_fixY[where b\<^sub>i=N and b\<^sub>j\<^sub>0=0])
          show \<open>{d. old_good (D1'(xL := d)) D2 D3} \<subseteq> {d. old_good (D1'(xL := d)) D2 D3}\<close> by simp
          show \<open>card (Some -` {d. old_good (D1'(xL := d)) D2 D3}) \<le> N\<close> by (simp add: card_mono)
          show \<open>card (- Some -` {d. old_good (D1'(xL := d)) D2 D3}) \<le> 0\<close> 
            using True D1'xL apply auto
            by (simp add: old_good_def)
          have *: \<open>old_good (D1'(xL := None)) D2 D3\<close>
            by (simp add: D1'xL True domIff)
          show \<open>co1_old_good \<ge> 0\<close>
            by (simp add: \<open>0 \<le> co1_old_good\<close>)
          then show \<open>preserve_query1_fixY_bound
             (None \<in> {d. old_good (D1'(xL := d)) D2 D3}) (None \<notin> {d. old_good (D1'(xL := d)) D2 D3})
             (real N) (real 0) \<le> co1_old_good\<close>
            by (simp add: * preserve_query1_fixY_bound_def)
        qed
      next
        case False
        show ?thesis
          apply (simp only: case_prod_beta I1_def J1_def fst_conv snd_conv fields)
        proof (rule preserve_query1_fixY[where b\<^sub>i=N and b\<^sub>j\<^sub>0=0])
          show \<open>{d. old_good (D1'(xL := d)) D2 D3} \<subseteq> {d. old_good (D1'(xL := d)) D2 D3}\<close> by simp
          show \<open>card (Some -` {d. old_good (D1'(xL := d)) D2 D3}) \<le> N\<close>
            by (simp add: card_mono)
          show \<open>card (- Some -` {d. old_good (D1'(xL := d)) D2 D3}) \<le> 0\<close>
            using False \<open>z\<in>M\<close>
            apply (auto simp: M_def fields old_good_def)
            by (metis DiffE domI insert_iff)
          have *: \<open>\<not> old_good (D1'(xL := None)) D2 D3\<close>
            by (simp add: D1'xL False domIff)
          show \<open>preserve_query1_fixY_bound (None \<in> {d. old_good (D1'(xL := d)) D2 D3}) (None \<notin> {d. old_good (D1'(xL := d)) D2 D3})
                     (real N) (real 0) \<le> co1_old_good\<close>
            apply (auto simp add: * preserve_query1_fixY_bound_def co1_old_good_def)
            by (simp add: inverse_eq_divide sqrt_divide_self_eq)
          show \<open>0 \<le> co1_old_good\<close>
            by simp
        qed
      qed
    qed
  qed
qed

definition \<open>UPc1_old_good = co1_old_good\<close>
lemma preserves_UPc1_old_good:
  \<open>preserves_ket ((X;(X1;D1)) UPc) old_good_state_00 old_good_state_0 UPc1_old_good\<close>
proof -
  note comp_apply[simp del]

  have UPc: \<open>((X;(X1;D1)) UPc) = 
      (X o Fst; X1 o Snd) cnot o\<^sub>C\<^sub>L (X \<circ> Snd; X1 \<circ> Fst) cnot o\<^sub>C\<^sub>L (X \<circ> Fst; (X1 \<circ> Fst; D1)) query\<close>
    by (simp add: UPc_def reg_1_3_def reg_2_3_def reg_3_3_def register_pair_Fst register_pair_Snd
        flip: register_mult comp_assoc register_comp_pair 
        o_apply[where x=cnot and f=\<open>(X;(X1;D1))\<close>] o_apply[where x=query and f=\<open>(X;(X1;D1))\<close>])

  have \<open>preserves_ket ((X \<circ> Fst; (X1 \<circ> Fst; D1)) query) old_good_state_00 old_good_state_0 co1_old_good\<close>
    by (rule preserves_co1_old_good)
  also have \<open>preserves_ket ((X \<circ> Snd; X1 \<circ> Fst) cnot) old_good_state_0 old_good_state_0 0\<close>
    apply (rule preserves_compatible[where U=cnot])
    by (auto simp add: old_good_state_0_def X_def X1_def comp_assoc
        intro!: compatible_register_invariant_pair compatible_register_invariant_Fst_comp
        compatible_register_invariant_Snd_comp)
  also have \<open>preserves_ket ((X \<circ> Fst; X1 \<circ> Snd) cnot) old_good_state_0 old_good_state_0 0\<close>
    apply (rule preserves_compatible[where U=cnot])
    by (auto simp add: old_good_state_0_def X_def X1_def comp_assoc
        intro!: compatible_register_invariant_pair compatible_register_invariant_Fst_comp
        compatible_register_invariant_Snd_comp)
  finally show ?thesis
    by (auto simp add: UPc1_old_good_def UPc cblinfun_compose_assoc register_norm)
qed

end
