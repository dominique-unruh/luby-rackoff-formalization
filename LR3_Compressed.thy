theory LR3_Compressed
  imports Compressed_Oracles.CO_Invariants Misc_Luby_Rackoff General_Luby_Rackoff
begin

(* U_UP,i, using compressed queries *)
definition UPc :: \<open>(whole \<times> whole \<times> db) ell2 \<Rightarrow>\<^sub>C\<^sub>L (whole \<times> whole \<times> db) ell2\<close> where \<open>UPc = 
  (reg_1_3 o Fst; reg_2_3 o Snd) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Snd; reg_2_3 o Fst) cnot o\<^sub>C\<^sub>L
  (reg_1_3 o Fst; (reg_2_3 o Fst; reg_3_3)) query\<close>

definition LR3c where \<open>LR3c =
  (X;(X1;D1)) UPc o\<^sub>C\<^sub>L (X1;(X2;D2)) UPc o\<^sub>C\<^sub>L (X2;(Y;D3)) UPc o\<^sub>C\<^sub>L (X1;(X2;D2)) UPc o\<^sub>C\<^sub>L (X;(X1;D1)) UPc\<close>

end
