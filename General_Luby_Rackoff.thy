theory General_Luby_Rackoff
  imports Misc_Luby_Rackoff
begin

type_synonym whole = \<open>half \<times> half\<close>

definition X :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>X = Fst\<close>
definition X1 :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>X1 = Snd o Fst\<close>
definition X2 :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>X2 = Snd o Snd o Fst\<close>
definition Y :: \<open>whole update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>Y = Snd o Snd o Snd o Fst\<close>
definition D1 :: \<open>db update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>D1 = Snd o Snd o Snd o Snd o Fst\<close>
definition D2 :: \<open>db update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>D2 = Snd o Snd o Snd o Snd o Snd o Fst\<close>
definition D3 :: \<open>db update \<Rightarrow> (whole \<times> whole \<times> whole \<times> whole \<times> db \<times> db \<times> db) update\<close> where \<open>D3 = Snd o Snd o Snd o Snd o Snd o Snd\<close>

lemma [simp]: \<open>compatible reg_1_3 reg_2_3\<close> \<open>compatible reg_1_3 reg_3_3\<close> \<open>compatible reg_2_3 reg_3_3\<close>
  \<open>compatible X X1\<close> \<open>compatible X D1\<close> \<open>compatible X1 D1\<close> \<open>compatible X1 X2\<close> \<open>compatible X1 D3\<close>
  \<open>compatible X2 D3\<close> \<open>compatible X1 D2\<close> \<open>compatible X2 D2\<close> \<open>compatible X2 Y\<close> \<open>compatible Y D3\<close>
            apply (simp_all add: reg_1_3_def reg_2_3_def reg_3_3_def X_def X1_def D1_def X2_def
      D2_def D3_def Y_def)
  by -


end