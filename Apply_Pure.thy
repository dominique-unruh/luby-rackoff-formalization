theory Apply_Pure
  imports Registers.Pure_States
begin


lemma clinear_option_case_aux: \<open>clinear X \<Longrightarrow> X (case t of Some u \<Rightarrow> f u | None \<Rightarrow> g) \<equiv> (case t of Some u \<Rightarrow> X (f u) | None \<Rightarrow> X g)\<close> for X
  apply (rule eq_reflection)
  by (simp add: option.case_eq_if) 


ML \<open>
local 
open Conv
open Type
val move_clinear_down_rules = @{thms 
  complex_vector.linear_add[THEN eq_reflection]
  complex_vector.linear_diff[THEN eq_reflection]
  complex_vector.linear_sum[THEN eq_reflection]
  clinear.scaleC[THEN eq_reflection]
  clinear_option_case_aux
}
;;
;;
fun has_head ctxt head cterm = let
  (* val cterm = cterm |> Thm.beta_conversion true |> Thm.rhs_of *)
  val idx = Thm.maxidx_of_cterm cterm
  val head_argT = fastype_of head |> Term.dest_funT |> fst
  val pat = Term.betapply (head, Var(("x",idx+1), head_argT))
  val match = SOME (Pattern.first_order_match (Proof_Context.theory_of ctxt) (pat, Thm.term_of cterm) 
                      (Vartab.empty, Vartab.empty))
          handle Pattern.MATCH => NONE
  (* val _ = \<^print> (cterm |> Thm.term_of, pat, match) *)
  in Option.isSome match end

(* Converts only a toplevel "head $ stuff" *)
fun move_clinear_down_conv' ctxt head conv : conv =
  ((fn ct => conv ct handle CTERM ("no conversion",_) => 
    ((* \<^print> ("no conv", ct); *) raise CTERM ("move_clinear_down_conv: no matching rules", [ct])))
  then_conv
  (sub_conv (fn ctxt => move_clinear_down_conv'' ctxt head conv |> try_conv) ctxt)) (* #> (fn x => (\<^print> ("conv'", x); x)) *)
(* Converts "head $ stuff" anywhere in term *)
and move_clinear_down_conv'' ctxt head (conv:conv) (cterm:cterm) : thm = 
  (if has_head ctxt head cterm then ((* tracing "head"; \<^print> cterm; *) move_clinear_down_conv' ctxt head conv cterm)
  else ((* tracing "sub"; \<^print> cterm; *) Conv.sub_conv (fn ctxt => move_clinear_down_conv'' ctxt head conv) ctxt cterm))
     (* |> (fn x => (\<^print> ("conv''", cterm, x); x)) *)
in
fun move_clinear_down_conv ctxt (subterm:bool) head_clinear_thm cterm : thm = let
  val head = (case Thm.prop_of head_clinear_thm of
            Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>clinear\<close>,_) $ head') => head'
            | _ => raise THM ("move_clinear_down_conv: head_clinear_thm must be of the form 'clinear \<dots>'", 0, [head_clinear_thm]))
  val _ = subterm orelse has_head ctxt head cterm orelse
          let val head_dots = betapply (head, Var(("dddot",0),dummyT))
          in raise CTERM ("move_clinear_down_conv: term must be of the form '" ^ Syntax.string_of_term ctxt head_dots ^ "'", [cterm]) end

  val rules = move_clinear_down_rules |> map (fn rule => rule OF [head_clinear_thm])
  val conv = Conv.rewrs_conv rules
  (* val _ = rules |> \<^print> *)
  val thm = (if subterm then move_clinear_down_conv'' else move_clinear_down_conv') ctxt head conv cterm
  (* val _ = thm |> \<^print> *)
in thm end
fun move_clinear_down_tac ctxt head_clinear_thm = CONVERSION (move_clinear_down_conv ctxt true head_clinear_thm)
end
\<close>

ML \<open>
local
open Conv
in
fun apply_to_pure_states_conv focus_thm compatible_thm apply_thm = let
  val state_apply1 = @{thm state_apply1[THEN eq_reflection]} OF [compatible_thm]
  val clinear_thm = @{thm pure_state_clinear} OF [compatible_thm]
  val unfocus_thm = Thm.symmetric focus_thm
  val _ = unfocus_thm |> \<^print>
  in
    fn ctxt =>
    (fn ct => (\<^print> ct; all_conv ct))
    then_conv
    (rewr_conv focus_thm |> arg_conv)
    then_conv
    rewr_conv state_apply1
    then_conv
    (rewr_conv apply_thm |> arg1_conv |> arg1_conv)
    then_conv
    (move_clinear_down_conv ctxt false clinear_thm)
    then_conv
    (top_sweep_rewrs_conv [unfocus_thm] ctxt)
  end
fun apply_to_pure_states_tac focus_thm compatible_thm apply_thm ctxt =
  CONVERSION (top_sweep_conv (apply_to_pure_states_conv focus_thm compatible_thm apply_thm) ctxt)
end
\<close>

lemma pure_state_id: \<open>pure_state id \<psi> = \<psi>\<close>
proof -
  have \<open>ket default \<in> range ((*\<^sub>V) (selfbutterket default))\<close>
    by (metis (mono_tags, opaque_lifting) butterfly_apply cinner_ket_same rangeI scaleC_one)
  then show ?thesis
    apply (simp add: pure_state'_def id_def pure_state_target_vector_ket_default)
    apply (subst pure_state_target_vector_ket_default)
    by auto
qed


end