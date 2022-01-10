theory Rel_LR3_Standard_Compressed
  imports LR3_Standard LR3_Compressed
begin

text \<open>Shows that \<^term>\<open>LR3\<close> (Luby-Rackoff using standard oracle) and \<^term>\<open>LR3c\<close> (Luby-Rackoff using compressed oracle)
      are related by \<^term>\<open>compress\<close>. (Lemma \<open>relation_LR3c_LR3\<close> below.)\<close>

lemma l2: \<open>reg_3_3 compress o\<^sub>C\<^sub>L UP o\<^sub>C\<^sub>L reg_3_3 compress = UPc\<close>
proof -
  have 1: \<open>(reg_1_3 \<circ> Fst;(reg_2_3 \<circ> Fst;reg_3_3)) o reg_3_3 = reg_3_3\<close>
    by (simp add: reg_1_3_def reg_2_3_def reg_3_3_def register_pair_Snd
        flip: comp_assoc)
  have 1: \<open>(reg_1_3 \<circ> Fst;(reg_2_3 \<circ> Fst;reg_3_3)) (reg_3_3 A) = reg_3_3 A\<close>
    for A :: \<open>'z::finite update\<close>
    using 1[THEN fun_cong, of A]
    by (auto simp add: o_def)
  have 2: \<open>B o\<^sub>C\<^sub>L R A o\<^sub>C\<^sub>L (reg_3_3 compress) = B o\<^sub>C\<^sub>L (reg_3_3 compress) o\<^sub>C\<^sub>L R A\<close> 
    if [simp]: \<open>compatible reg_3_3 R\<close> 
    for A and B :: \<open>(whole \<times> whole \<times> db) update\<close> and R :: \<open>'z::finite update \<Rightarrow> (whole \<times> whole \<times> db) update\<close>
    by (simp add: cblinfun_compose_assoc swap_registers[OF that])
  show ?thesis
    apply (simp add: UP_def UPc_def query_def flip: register_mult cblinfun_compose_assoc 1)
    by (simp add: 1 2 2[of _ id_cblinfun, simplified])
qed

lemma l1: \<open>D1 compress o\<^sub>C\<^sub>L (X;(X1;D1)) UP o\<^sub>C\<^sub>L D1 compress = (X;(X1;D1)) UPc\<close>
  if [register]: \<open>mutually compatible (X,X1,D1)\<close>
  for D1 X X1
proof -
  have 1: \<open>D1 = (X;(X1;D1)) o reg_3_3\<close>
    by (simp add: reg_3_3_def register_pair_Snd flip: comp_assoc)
  have \<open>D1 compress o\<^sub>C\<^sub>L (X;(X1;D1)) UP o\<^sub>C\<^sub>L D1 compress = 
      (X;(X1;D1)) (reg_3_3 compress o\<^sub>C\<^sub>L UP o\<^sub>C\<^sub>L reg_3_3 compress)\<close>
    by (simp add: 1[unfolded o_def, THEN fun_cong] register_mult)
  also have \<open>\<dots> = (X;(X1;D1)) UPc\<close>
    by (simp add: l2)
  finally show ?thesis
    by -
qed

lemma relation_LR3c_LR3: \<open>LR3c = D1 compress o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L LR3 o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D1 compress\<close>
proof -
  have rm_end[intro!]: \<open>A o\<^sub>C\<^sub>L B = A o\<^sub>C\<^sub>L B'\<close> if \<open>B = B'\<close> for A A' B B' :: \<open>('z ell2, 'z ell2) cblinfun\<close>
    using that by simp
  have rm_start[intro!]: \<open>A o\<^sub>C\<^sub>L B = A' o\<^sub>C\<^sub>L B\<close> if \<open>A = A'\<close> for A A' B B' :: \<open>('z ell2, 'z ell2) cblinfun\<close>
    using that by simp
  have vanish[simp]: 
    \<open>A o\<^sub>C\<^sub>L D1 compress o\<^sub>C\<^sub>L D1 compress = A\<close>
    \<open>A o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D2 compress = A\<close>
    for A :: \<open>state ell2 \<Rightarrow>\<^sub>C\<^sub>L state ell2\<close>
    by (auto simp: cblinfun_compose_assoc register_mult compress_square intro: swap_registers)
  have D1_front: 
    \<open>A o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D1 compress = A o\<^sub>C\<^sub>L D1 compress o\<^sub>C\<^sub>L D2 compress\<close>
    \<open>A o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L D1 compress = A o\<^sub>C\<^sub>L D1 compress o\<^sub>C\<^sub>L D3 compress\<close>
    \<open>A o\<^sub>C\<^sub>L (X1;(X2;D2)) UP o\<^sub>C\<^sub>L D1 compress = A o\<^sub>C\<^sub>L D1 compress o\<^sub>C\<^sub>L (X1;(X2;D2)) UP\<close>
    \<open>A o\<^sub>C\<^sub>L (X2;(Y;D3)) UP o\<^sub>C\<^sub>L D1 compress = A o\<^sub>C\<^sub>L D1 compress o\<^sub>C\<^sub>L (X2;(Y;D3)) UP\<close>
    for A :: \<open>state ell2 \<Rightarrow>\<^sub>C\<^sub>L state ell2\<close>
    by (auto simp: cblinfun_compose_assoc intro: swap_registers)
  have D2_front: 
    \<open>A o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L D2 compress = A o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D3 compress\<close>
    \<open>A o\<^sub>C\<^sub>L (X;(X1;D1)) UP o\<^sub>C\<^sub>L D2 compress = A o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L (X;(X1;D1)) UP\<close>
    \<open>A o\<^sub>C\<^sub>L (X2;(Y;D3)) UP o\<^sub>C\<^sub>L D2 compress = A o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L (X2;(Y;D3)) UP\<close>
    for A :: \<open>state ell2 \<Rightarrow>\<^sub>C\<^sub>L state ell2\<close>
    by (auto simp: cblinfun_compose_assoc intro: swap_registers)
  have D3_front: 
    \<open>A o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D3 compress = A o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L D2 compress\<close>
    \<open>A o\<^sub>C\<^sub>L (X;(X1;D1)) UP o\<^sub>C\<^sub>L D3 compress = A o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L (X;(X1;D1)) UP\<close>
    \<open>A o\<^sub>C\<^sub>L (X1;(X2;D2)) UP o\<^sub>C\<^sub>L D3 compress = A o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L (X1;(X2;D2)) UP\<close>
    for A :: \<open>state ell2 \<Rightarrow>\<^sub>C\<^sub>L state ell2\<close>
    by (auto simp: cblinfun_compose_assoc intro: swap_registers)

  have \<open>D1 compress o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L LR3 o\<^sub>C\<^sub>L D3 compress o\<^sub>C\<^sub>L D2 compress o\<^sub>C\<^sub>L D1 compress
    = (D1 compress o\<^sub>C\<^sub>L (X;(X1;D1)) UP o\<^sub>C\<^sub>L D1 compress)
   o\<^sub>C\<^sub>L (D2 compress o\<^sub>C\<^sub>L (X1;(X2;D2)) UP o\<^sub>C\<^sub>L D2 compress)
   o\<^sub>C\<^sub>L (D3 compress o\<^sub>C\<^sub>L (X2;(Y;D3)) UP o\<^sub>C\<^sub>L D3 compress)
   o\<^sub>C\<^sub>L (D2 compress o\<^sub>C\<^sub>L (X1;(X2;D2)) UP o\<^sub>C\<^sub>L D2 compress)
   o\<^sub>C\<^sub>L (D1 compress o\<^sub>C\<^sub>L (X;(X1;D1)) UP o\<^sub>C\<^sub>L D1 compress)\<close>
    apply (auto simp add: LR3_def simp flip: cblinfun_compose_assoc) (* remove D1 at end *)
    apply (auto simp add: cblinfun_compose_assoc) (* remove D1 at start *)
    apply (auto simp add: D2_front simp flip: cblinfun_compose_assoc)
    apply (auto simp add: D3_front simp flip: cblinfun_compose_assoc) (* remove (X;(X1;D1)) at end *)
    apply (auto simp add: D1_front simp flip: cblinfun_compose_assoc) (* remove D2 at end *)
    apply (auto simp add: D2_front D2_front[of id_cblinfun, simplified] simp flip: cblinfun_compose_assoc) (* remove D2 at end *)
    by (auto simp add: D3_front simp flip: cblinfun_compose_assoc) (* remove (X1;(X2;D2)) at end *)

  also have \<open>\<dots> = LR3c\<close>
    by (simp add: LR3c_def l1)

  finally show ?thesis
    by simp
qed

end
