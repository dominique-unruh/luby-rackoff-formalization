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

(* Notion of good from the current eprint of the LR4-paper. *)
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


end
