theory closure_algebra
  imports conditions_infinitary
begin

section \<open>Topological Closure Algebras\<close>

(**In this section we examine the traditional notion of topological closure algebras
in the spirit of McKinsey \& Tarski @{cite AOT}, but drawing primarily from the works of Zarycki
@{cite Zarycki-1} and Kuratowski @{cite Kuratowski-1}.*)

(**We define some conditions on unary operations (aka. operators) with type @{type "'w \<sigma>\<Rightarrow>'w \<sigma>"}.
Those operators are aimed at extending Boolean algebras (of propositions) towards different
sorts of topological algebras. Here we examine closure (and their dual: interior) operators.
We follow the naming conventions introduced originally by Kuratowski @{cite Kuratowski-1}
(cf. also @{cite Kuratowski-2}) and Zarycki @{cite Zarycki-1}.*)

subsection \<open>Closure conditions\<close>

(*Defining axioms*)
abbreviation "Cl_1 \<phi> \<equiv> ADDI \<phi>" (* 1st Kuratowski condition = MONO + Cl_1' *)
abbreviation "Cl_1' \<phi> \<equiv> ADDI\<^sup>a \<phi>" (* Given MONO, this is the essence of Cl_1 *)
abbreviation "iCl_1 \<phi> \<equiv> iADDI(\<phi>)"   (* infinitary variant of Cl_1 *)
abbreviation "iCl_1' \<phi> \<equiv> iADDI\<^sup>a(\<phi>)" (* infinitary variant of Cl_1' *)
abbreviation "Cl_2 \<phi> \<equiv> EXPN \<phi>"  (* 2nd Kuratowski condition: expansiveness/increasingness *)
abbreviation "Cl_3 \<phi>  \<equiv> NORM \<phi>" (* 3rd Kuratowski condition, sometimes called "normality" *)
abbreviation "Cl_4 \<phi> \<equiv> IDEM \<phi>" (* 4th Kuratowski condition: idempotence = EXPN + Cl_4' *)
abbreviation "Cl_4' \<phi> \<equiv> IDEM\<^sup>b \<phi>" (* Given EXPN, this is the essence of Cl_4 *)

(*Some interesting entailed properties*)
abbreviation "Cl_5 \<phi>  \<equiv> DNRM \<phi>" (*the dual of NORM*)
abbreviation "Cl_6 \<phi> \<equiv> DISTR\<^sub>\<rightarrow>\<^sup>d \<phi>"  (* decreasing distribution over implication *)
abbreviation "Cl_7 \<phi> \<equiv> DISTR\<^sub>\<leftharpoonup>\<^sup>d \<phi>"  (* decreasing distribution over difference *)
definition "Cl_8 \<phi>  \<equiv> \<forall>A B. \<phi>(\<phi> A \<^bold>\<and> \<phi> B) \<^bold>\<approx> (\<phi> A) \<^bold>\<and> (\<phi> B)"
definition "Cl_9 \<phi>  \<equiv> \<forall>A B.  A \<^bold>\<preceq> (\<phi> B) \<longrightarrow> (\<phi> A) \<^bold>\<preceq> (\<phi> B)"

(**As for Cl-8 and Cl-9 we show which axioms entail them*)
lemma PC8: "MONO \<phi> \<Longrightarrow> Cl_2 \<phi> \<Longrightarrow> Cl_4 \<phi> \<Longrightarrow> Cl_8 \<phi>" by (smt (verit, del_insts) Cl_8_def EXPN_def IDEM_def MONO_MULTa MULT_a_def setequ_def setequ_equ)
lemma PC9: "MONO \<phi> \<Longrightarrow> Cl_4 \<phi> \<Longrightarrow> Cl_9 \<phi>" by (metis Cl_9_def IDEM_def MONO_def setequ_equ)

(**@{text "\<phi>"} is a topological closure operator in the strict sense (@{text "\<CC>(\<phi>)"}) 
iff it satisfies the four Kuratowski conditions 1-4 (cf. @{cite Kuratowski-1} @{cite Kuratowski-2}).*)
abbreviation "\<CC> \<phi>  \<equiv> Cl_1 \<phi> \<and> Cl_2 \<phi> \<and> Cl_3  \<phi> \<and> Cl_4 \<phi>"

(*This characterization is shown consistent by generating a generating non-trivial model.*)
lemma "\<CC> \<phi>" nitpick[satisfy, card 'w=3] oops (*model found: characterization is consistent*)


subsection \<open>Interior conditions\<close>

(*Defining axioms*)
abbreviation "Int_1 \<phi>  \<equiv> MULT \<phi>" (* (dual of) 1st Kuratowski condition = MONO + Int_1' *)
abbreviation "Int_1' \<phi> \<equiv> MULT\<^sup>b \<phi>" (* Given MONO, this is the essence of Int_1 *)
abbreviation "iInt_1' \<phi> \<equiv> iMULT\<^sup>b(\<phi>)" (* infinitary variant of Int_1 *)
abbreviation "iInt_1 \<phi> \<equiv> iMULT(\<phi>)"   (* infinitary variant of Int_1' *)
abbreviation "Int_2 \<phi>  \<equiv> CNTR \<phi>"  (* (dual of) 2th Kuratowski condition: contractiveness *)
abbreviation "Int_3 \<phi>  \<equiv> DNRM \<phi>"  (* (dual of) 3th Kuratowski condition: 'dual normality'*)
abbreviation "Int_4 \<phi>  \<equiv> IDEM \<phi>" (* (dual of) 4th Kuratowski condition = CNTR + Int_4' *)
abbreviation "Int_4' \<phi> \<equiv> IDEM\<^sup>a \<phi>" (* Given CNTR, this is the essence of Int_4 *)

(*Some interesting entailed properties*)
abbreviation "Int_5 \<phi>  \<equiv> NORM \<phi>"    (* 3th Kuratowski condition: 'normality'*)
abbreviation "Int_6 \<phi>  \<equiv> DISTR\<^sub>\<leftharpoonup>\<^sup>i \<phi>" (* increasing distribution over difference *)
abbreviation "Int_7 \<phi>  \<equiv> DISTR\<^sub>\<rightarrow>\<^sup>i \<phi>" (* increasing distribution over implication *)
definition "Int_8 \<phi>  \<equiv> \<forall>A B. \<phi>(\<phi> A \<^bold>\<or> \<phi> B) \<^bold>\<approx> (\<phi> A) \<^bold>\<or> (\<phi> B)" (* dual of Cl-8 *)
definition "Int_9 \<phi>  \<equiv> \<forall>A B. \<phi> A \<^bold>\<preceq> B \<longrightarrow> (\<phi> A) \<^bold>\<preceq> (\<phi> B)"   (* dual of Cl-9 *)

(**As for Int-8 and Int-9 we show which axioms entail them*)
lemma PI8: "MONO \<phi> \<Longrightarrow> Int_2 \<phi> \<Longrightarrow> Int_4 \<phi> \<Longrightarrow> Int_8 \<phi>" by (metis ADDI_b_def CNTR_def IDEM_def Int_8_def MONO_ADDIb setequ_def setequ_equ) 
lemma PI9: "MONO \<phi> \<Longrightarrow> Int_4 \<phi> \<Longrightarrow> Int_9 \<phi>" by (metis IDEM_def Int_9_def MONO_def setequ_equ)

(**@{text "\<phi>"} is an interior operator in the strict sense (@{text "\<II>(\<phi>)"}) 
iff it satisfies the interior conditions 1-4 above (cf. @{cite Zarycki-1} and also @{cite Kuratowski-2}).*)
abbreviation "\<II> \<phi> \<equiv> Int_1 \<phi> \<and> Int_2 \<phi> \<and> Int_3 \<phi> \<and> Int_4 \<phi>"

(**This characterization is also shown consistent by generating a non-trivial model.*)
lemma "\<II> \<phi>" nitpick[satisfy, card 'w=3] oops (*model found: characterization is consistent*)

section \<open>Closure algebra\<close>
(**We define a topological Boolean algebra with a primitive closure operator and verify a few properties.
We write \<C> for a unary operator intended as a closure-like operator (though unconstrained by default)*)

(**Interior operator as derived from closure.*)
abbreviation Int_cl::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi>" ("\<I>[_]") 
  where "\<I>[\<C>] \<equiv> \<C>\<^sup>d"

(**Frontier (aka. 'boundary') operator as derived from closure.
 (cf. 'Grenze' @{cite Hausdorff}, 'fronti\`ere' @{cite Zarycki-1} @{cite Kuratowski-2})*)
definition Fr_cl::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi>" ("\<F>[_]")
  where "\<F>[\<C>] \<equiv> \<lambda>A. \<C> A \<^bold>\<and> \<C> (\<^bold>\<midarrow>A)"

(**Border operator as derived from closure (cf. 'Rand' @{cite Hausdorff}, 'bord' @{cite Zarycki-1})*)
definition Br_cl::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi>" ("\<B>[_]") 
  where "\<B>[\<C>] \<equiv> \<lambda>A. A \<^bold>\<and> \<C> (\<^bold>\<midarrow>A)"

(**(Hausdorff's) Residue operator as derived from closure (via border).*)
definition Rs_cl::"('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi>" ("\<R>[_]") 
  where "\<R>[\<C>] \<equiv> \<lambda>A. \<B>[\<C>](\<^bold>\<midarrow>(\<B>[\<C>](\<^bold>\<midarrow>A)))"


subsection \<open>Basic properties\<close>

(**The results below are well known in the literature.
Here we try to uncover the minimal conditions on the operator \<C> under which they hold.*)

(**The frontier operator is in fact symmetric wrt. complement*)
lemma F_symm: "\<forall>A. (\<F>[\<C>] A) = (\<F>[\<C>] (\<^bold>\<midarrow>A))" unfolding Fr_cl_def conn by auto

(**Fixed-point and other operators are interestingly related. 
Note that below only the second Kuratowski condition for \<C> (expansiveness) is required.*)
lemma fp1: "Cl_2 \<C> \<Longrightarrow> \<I>[\<C>]\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>[\<C>]\<^sup>c" by (smt (verit, del_insts) Br_cl_def CNTR_def EXPN_CNTR_dual2 compl_def dimpl_char fixpoint_op_def meet_def op_compl_def op_dual_def op_equal_def setequ_char subset_def)
lemma fp2: "Cl_2 \<C> \<Longrightarrow> \<B>[\<C>]\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>[\<C>]\<^sup>c" by (metis comp_symm fp1 ofp_c ofp_invol op_equal_equ)
lemma fp3: "Cl_2 \<C> \<Longrightarrow> \<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>[\<C>]\<^sup>d" by (metis dual_invol fp2 ofp_d ofp_invol op_equal_equ)
lemma fp4: "Cl_2 \<C> \<Longrightarrow> (\<B>[\<C>]\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (metis fp3 ofp_invol op_equal_equ)
lemma fp5: "Cl_2 \<C> \<Longrightarrow> \<F>[\<C>]\<^sup>f\<^sup>p \<^bold>\<equiv> (\<lambda>X. (\<B>[\<C>] X) \<^bold>\<or> (\<C>\<^sup>c X))"  by (smt (verit, del_insts) Br_cl_def EXPN_def Fr_cl_def compl_def dimpl_char fixpoint_op_def join_def meet_def op_compl_def op_equal_def setequ_char subset_def)

(**Define some fixed-point predicates and prove some properties.*)
abbreviation closedset ("Cl[_]") where "Cl[\<C>] \<equiv> fp \<C>"
abbreviation openset ("Op[_]") where "Op[\<C>] \<equiv> fp \<I>[\<C>]"
abbreviation borderset ("Br[_]") where "Br[\<C>] \<equiv> fp \<B>[\<C>]"
abbreviation frontierset ("Fr[_]") where "Fr[\<C>] \<equiv> fp \<F>[\<C>]"
abbreviation residueset ("Rs[_]") where "Rs[\<C>] \<equiv> fp \<R>[\<C>]"

lemma Int_Open: "Cl_4 \<C> \<Longrightarrow> \<forall>A. Op[\<C>](\<I>[\<C>] A)" by (metis (full_types) IDEM_def IDEM_dual fixpoint_pred_def setequ_equ)
lemma Cl_Closed: "Cl_4 \<C> \<Longrightarrow> \<forall>A. Cl[\<C>](\<C> A)" by (simp add: IDEM_def fixpoint_pred_def setequ_equ)
lemma Cl_Frontier: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>A. Cl[\<C>](\<F>[\<C>] A)" by (metis Cl_8_def EXPN_def Fr_cl_def IDEM_b_def IDEM_def PC8 fixpoint_pred_def setequ_def) 
lemma Br_Border: "MONO \<C> \<Longrightarrow> \<forall>A. Br[\<C>](\<B>[\<C>] A)" by (smt (verit, ccfv_threshold) BA_deMorgan2 Br_cl_def L12 L3 L4 L5 L6 MONO_def fixpoint_pred_def setequ_def)
(**In contrast, there are no analogous fixed-point results for frontier and residue:*)
lemma "\<CC> \<C> \<Longrightarrow> \<forall>A. Fr[\<C>](\<F>[\<C>] A)" nitpick oops (*counterexample even if assuming all closure conditions*)
lemma "\<CC> \<C> \<Longrightarrow> \<forall>A. Rs[\<C>](\<R>[\<C>] A)" nitpick oops (*counterexample even if assuming all closure conditions*)

lemma OpCldual: "\<forall>A. Cl[\<C>] A \<longleftrightarrow> Op[\<C>](\<^bold>\<midarrow>A)" by (simp add: BA_dn fp_d)
lemma ClOpdual: "\<forall>A. Op[\<C>] A \<longleftrightarrow> Cl[\<C>] (\<^bold>\<midarrow>A)" by (simp add: fp_d)
lemma Op_Bempty: "Cl_2 \<C> \<Longrightarrow> \<forall>A. Op[\<C>] A \<longleftrightarrow> \<B>[\<C>] A \<^bold>\<approx> \<^bold>\<bottom>" by (metis comp_symm fp1 fp_c_rel ofp_d ofp_dc op_equal_equ)
lemma Cl_Bempty: "Cl_2 \<C> \<Longrightarrow> \<forall>A. Cl[\<C>] A \<longleftrightarrow> \<B>[\<C>] (\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<bottom>" using OpCldual Op_Bempty by blast
lemma Br_Iempty: "Cl_2 \<C> \<Longrightarrow> \<forall>A. Br[\<C>] A \<longleftrightarrow> \<I>[\<C>] A \<^bold>\<approx> \<^bold>\<bottom>" by (metis comp_invol fp2 fp_c_rel ofp_c op_equal_equ)
lemma Fr_ClBr: "Cl_2 \<C> \<Longrightarrow> \<forall>A. Fr[\<C>] A \<longleftrightarrow> (Cl[\<C>] A \<and> Br[\<C>] A)" by (smt (verit, best) Br_cl_def EXPN_def Fr_cl_def compl_def fixpoint_pred_def meet_def setequ_def setequ_equ subset_def)

lemma Int_join_closed: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> join_closed Op[\<C>]" using fp_inf_closed_cond3 fp_meet_join_closed_dual inf_closed_char inf_meet_closed by auto
lemma Int_sup_closed: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> supremum_closed Op[\<C>]" by (simp add: fp_inf_closed_cond3 fp_inf_sup_closed_dual)
lemma Int_meet_closed: "Cl_1' \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> meet_closed Op[\<C>]" by (smt (verit, del_insts) ADDIa_impl_MULTb CNTR_def EXPN_CNTR_dual2 MULT_b_def fixpoint_pred_def meet_closed_def setequ_def setequ_equ)
lemma Int_inf_closed: "iCl_1' \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> infimum_closed Op[\<C>]" by (simp add: fp_sup_closed_cond2 fp_sup_inf_closed_dual)
lemma Cl_meet_closed: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> meet_closed Cl[\<C>]" using fp_inf_closed_cond3 inf_closed_char inf_meet_closed by auto
lemma Cl_inf_closed: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> infimum_closed Cl[\<C>]" by (simp add: fp_inf_closed_cond3)
lemma Cl_join_closed: "Cl_1' \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> join_closed Cl[\<C>]" by (metis Int_meet_closed dual_invol fp_meet_join_closed_dual op_equal_equ)
lemma Cl_sup_closed: "iCl_1' \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> supremum_closed Cl[\<C>]" by (simp add: fp_sup_closed_cond2)
lemma Br_inf_closed: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> infimum_closed' Br[\<C>]" unfolding infimum_closed'_def by (smt (z3) BA_cp DNRM_def EXPN_impl_DNRM MONO_def MONO_dual dimpl_char fixpoint_op_def fp2 fp_inf_closed_cond3 fp_rel inf_char inf_closed_char op_compl_def op_equal_equ setequ_def setequ_equ subset_def)
lemma "\<CC> \<C> \<Longrightarrow> infimum_closed Br[\<C>]" nitpick oops
lemma Br_Fr_join: "Cl_1 \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>A B. Br[\<C>] A \<and> Fr[\<C>] B \<longrightarrow> Br[\<C>](A \<^bold>\<or> B)"
proof -
  assume cl1: "Cl_1 \<C> " and cl2: "Cl_2 \<C>" and cl4: "Cl_4' \<C>"
  { fix A B
    { assume brA: "Br[\<C>] A" and frB: "Fr[\<C>] B"
      from cl2 brA have bndA: "\<I>[\<C>] A \<^bold>\<approx> \<^bold>\<bottom>" by (simp add: Br_Iempty)
      hence 1: "\<C>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<top>" by (metis brA cl2 dual_invol fp4 fp_d_rel op_equal_equ)
      from frB have "\<I>[\<C>](\<C> B) \<^bold>\<approx> \<^bold>\<bottom>" by (metis Br_Iempty Fr_ClBr cl2 fixpoint_pred_def setequ_equ)
      hence 2: "\<C>(\<^bold>\<midarrow>(\<C> B)) \<^bold>\<approx> \<^bold>\<top>" by (metis Br_Iempty cl2 fp2 fp_d_rel ofp_dc ofp_invol op_equal_equ)
      from cl1 cl2 have "\<C>(\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>((\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> B)" using DISTR_diff_dec_def DISTR_diff_dec_prop by blast
      hence "\<C>(\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" unfolding conn by simp
      hence "\<^bold>\<top> \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" using 1 setequ_equ by force
      hence 3: "\<^bold>\<midarrow>(\<C> B) \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" unfolding conn by simp
      from cl1 cl2 cl4 have 4: "let M=\<^bold>\<midarrow>(\<C> B); N=\<^bold>\<midarrow>(A \<^bold>\<or> B) in  M \<^bold>\<preceq> \<C> N \<longrightarrow> \<C> M \<^bold>\<preceq> \<C> N" by (metis (no_types) ADDI_char Cl_9_def EXPN_def IDEM_b_def IDEM_def MONO_ADDIb PC9 antisymmetric_def setequ_equ subset_antisymmetric)
      from 3 4 have "\<C>(\<^bold>\<midarrow>(\<C> B)) \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" by simp 
      hence "\<^bold>\<top> \<^bold>\<approx> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" using 2 unfolding top_def by (simp add: setequ_char subset_def)
      hence "\<^bold>\<bottom> \<^bold>\<approx> \<I>[\<C>](A \<^bold>\<or> B)" using cl2 1 bndA by (simp add: op_dual_def setequ_equ)
      hence "Br[\<C>] (A \<^bold>\<or> B)" using cl2 Br_Iempty by (metis setequ_equ)
    } hence "Br[\<C>] A \<and> Fr[\<C>] B \<longrightarrow> Br[\<C>] (A \<^bold>\<or> B)" by simp
  } hence "\<forall>A B. Br[\<C>] A \<and> Fr[\<C>] B \<longrightarrow> Br[\<C>] (A \<^bold>\<or> B)" by simp
  thus ?thesis by simp
qed
lemma Fr_inf_closed: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> infimum_closed' Fr[\<C>]" by (smt (z3) Br_inf_closed Fr_ClBr fp_inf_closed_cond3 inf_closed_char infimum_closed'_def)
lemma "\<CC> \<C> \<Longrightarrow> infimum_closed Fr[\<C>]" nitpick oops (*countermodel*)
lemma Fr_join_closed: "Cl_1 \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> join_closed Fr[\<C>]" by (metis (full_types) ADDI_joinclosed Br_Fr_join Fr_ClBr join_closed_def)

lemma pFI: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>A. \<F>[\<C>](\<I>[\<C>] A) \<^bold>\<preceq> \<F>[\<C>] A" by (simp add: BA_dn CNTR_def EXPN_CNTR_dual2 Fr_cl_def IDEM_b_def L12 MONO_def op_dual_def)
lemma pFC: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>A. \<F>[\<C>](\<C> A) \<^bold>\<preceq> \<F>[\<C>] A" by (metis BA_dn F_symm op_dual_def pFI)
lemma pBI: "Cl_4' \<C> \<Longrightarrow> \<forall>A. \<B>[\<C>](\<I>[\<C>] A) \<^bold>\<preceq> \<B>[\<C>] A" by (smt (verit, best) BA_dn Br_cl_def IDEM_b_def compl_def meet_def op_dual_def subset_def)
lemma "\<CC> \<C> \<Longrightarrow> \<forall>A. \<B>[\<C>](\<C> A) \<^bold>\<preceq> \<B>[\<C>] A" nitpick oops
lemma pRB: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> \<forall>A. \<R>[\<C>] A \<^bold>\<preceq> \<B>[\<C>] A" oops (** as exercise (evtl. without using Cl-2) *)

(**Properties involving disjointness*)
lemma Disj_IF: "\<forall>A. Disj (\<I>[\<C>] A) (\<F>[\<C>] A)" by (simp add: Disj_def Fr_cl_def bottom_def compl_def meet_def op_dual_def setequ_char)
lemma Disj_B: "\<forall>A. Disj (\<B>[\<C>] A) (\<B>[\<C>] (\<^bold>\<midarrow>A))" by (simp add: Br_cl_def Disj_def bottom_def compl_def meet_def setequ_char)
lemma Disj_I: "Cl_2 \<C> \<Longrightarrow> \<forall>A. Disj (\<I>[\<C>] A) (\<^bold>\<midarrow>A)" by (smt (verit, best) Disj_def EXPN_def bottom_def compl_def meet_def op_dual_def setequ_char subset_def)
lemma Disj_BCI: "\<forall>A. Disj (\<B>[\<C>] (\<C> A)) (\<I>[\<C>] (\<^bold>\<midarrow>A))" by (simp add: Br_cl_def Disj_def bottom_def compl_def meet_def op_dual_def setequ_char)
lemma Disj_FCI: "Cl_4 \<C> \<Longrightarrow> \<forall>A. Disj (\<F>[\<C>] (\<C> A)) (\<I>[\<C>] (\<^bold>\<midarrow>A))" by (metis Br_cl_def Disj_BCI Fr_cl_def IDEM_def setequ_equ)
lemma Disj_CRI: "MONO \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> \<forall>A. Disj (\<C> (\<B>[\<C>] (\<^bold>\<midarrow>A))) (\<I>[\<C>] (\<^bold>\<midarrow>A))" unfolding Disj_def by (smt (verit, ccfv_threshold) Br_cl_def Cl_9_def L3 L5 PC9 compl_def op_dual_def subset_def)
lemma Disj_Rcompl: "MONO \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> \<forall>A. Disj (\<R>[\<C>] A) (\<^bold>\<midarrow>A)" by (smt (verit, del_insts) BA_dn Br_cl_def Disj_CRI Disj_def Rs_cl_def compl_def meet_def op_dual_def setequ_char)

(**Closure and Interior can be interestingly characterized using the notion of disjointness*)
lemma CI_Disj_rel_a: "\<forall>A p. (\<forall>E. (\<I>[\<C>] E) p \<longrightarrow> \<not>Disj E A) \<longrightarrow> (\<C> A) p" by (metis BA_deMorgan1 BA_dn Br_cl_def Disj_BCI L1 compl_def op_dual_def)
lemma CI_Disj_rel_b: "MONO \<C> \<Longrightarrow> \<forall>A p. (\<C> A) p \<longrightarrow> (\<forall>E. (\<I>[\<C>] E) p \<longrightarrow> \<not>Disj E A)" unfolding MONO_def Disj_def op_dual_def by (metis bottom_def compl_def meet_def setequ_equ subset_def)
lemma CI_Disj_rel: "MONO \<C> \<Longrightarrow> \<forall>A. \<C> A = (\<lambda>p. \<forall>E. (\<I>[\<C>] E) p \<longrightarrow> \<not>Disj E A)" by (metis CI_Disj_rel_a CI_Disj_rel_b)

(**Closure and interior can be characterised in terms of their fixed points.*)
lemma C_fp_def: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> 
                  \<Longrightarrow> \<forall>A. \<C> A \<^bold>\<approx> \<^bold>\<And>(\<lambda>S. Cl[\<C>] S \<and> A \<^bold>\<preceq> S)"
  using inf_char unfolding setequ_def by (smt (verit, del_insts) Cl_Closed EXPN_def IDEM_a_def IDEM_char MONO_def fixpoint_pred_def setequ_equ)

lemma I_fp_def: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C>
                   \<Longrightarrow> \<forall>A. \<I>[\<C>] A \<^bold>\<approx> \<^bold>\<Or>(\<lambda>S. Op[\<C>] S \<and> S \<^bold>\<preceq> A)" 
  using iDM_b op_dual_def setequ_char by (smt (z3) BA_cp BA_dn C_fp_def EXPN_def IDEM_b_def Int_sup_closed MONO_def MONO_dual OpCldual fixpoint_pred_def setequ_def setequ_equ subset_def sup_char supremum_closed_def)
  

end