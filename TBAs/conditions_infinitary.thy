theory conditions_infinitary
  imports conditions boolean_algebra_infinitary
begin

(**We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.*)

(**Distribution over infinite meets (infima) or infinite multiplicativity (iMULT).*)
definition iMULT::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT")
  where "iMULT \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<approx> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>" 
definition iMULT_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT\<^sup>a")
  where "iMULT\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<preceq> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"
definition iMULT_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT\<^sup>b")
  where "iMULT\<^sup>b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<succeq> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"

declare iMULT_def[cond] iMULT_a_def[cond] iMULT_b_def[cond]

(**Distribution over infinite joins (suprema) or infinite additivity (iADDI).*)
definition iADDI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI")
  where "iADDI \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<approx> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI\<^sup>a")
  where "iADDI\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI\<^sup>b")
  where "iADDI\<^sup>b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<succeq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>"

declare iADDI_def[cond] iADDI_a_def[cond] iADDI_b_def[cond]

lemma iMULT_char: "iMULT \<phi> = (iMULT\<^sup>a \<phi> \<and> iMULT\<^sup>b \<phi>)" using iMULT_a_def iMULT_b_def iMULT_def by (metis setequ_def)
lemma iADDI_char: "iADDI \<phi> = (iADDI\<^sup>a \<phi> \<and> iADDI\<^sup>b \<phi>)" using iADDI_a_def iADDI_b_def iADDI_def by (metis setequ_def)

(**MULT-a and iMULT-a are in fact equivalent.*)
lemma iMULTa_equ: "iMULT\<^sup>a \<phi> = MULT\<^sup>a \<phi>" proof -
  have lr: "iMULT\<^sup>a \<phi> \<Longrightarrow> MULT\<^sup>a \<phi>" proof - (*prove as a one-liner by instantiating iMULT_a_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume imulta: "iMULT\<^sup>a \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>"
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<And>?S = A \<^bold>\<and> B" unfolding infimum_def meet_def by blast
    hence p1: "\<phi>(\<^bold>\<And>?S) = \<phi>(A \<^bold>\<and> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding img_dir_def by blast
    hence p2: "\<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<and> (\<phi> B)" unfolding infimum_def meet_def by auto
    have "\<phi>(\<^bold>\<And>?S) \<preceq> \<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk>" using imulta iMULT_a_def by blast    
    hence "\<phi>(A \<^bold>\<and> B) \<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: MULT_a_def) qed
  have rl: "MULT\<^sup>a \<phi> \<Longrightarrow> iMULT\<^sup>a \<phi>" by (smt (verit, best) MONO_MULTa MONO_def iMULT_a_def img_dir_def inf_char)
  from lr rl show ?thesis by blast
qed
(**ADDI-b and iADDI-b are also equivalent.*)
lemma iADDIb_equ: "iADDI\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" proof -
  have lr: "iADDI\<^sup>b \<phi> \<Longrightarrow> ADDI\<^sup>b \<phi>" proof - (*prove as a one-liner by instantiating iADDI_b_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume iaddib: "iADDI\<^sup>b \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>" (* for some reason Isabelle doesn't like other letters as type variable. Why?*)
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<Or>?S = A \<^bold>\<or> B" unfolding supremum_def join_def by blast
    hence p1: "\<phi>(\<^bold>\<Or>?S) = \<phi>(A \<^bold>\<or> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding img_dir_def by blast
    hence p2: "\<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<or> (\<phi> B)" unfolding supremum_def join_def by auto
    have " \<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> \<preceq> \<phi>(\<^bold>\<Or>?S)" using iaddib iADDI_b_def by blast    
    hence "(\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<or> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: ADDI_b_def) qed
  have rl: "ADDI\<^sup>b \<phi> \<Longrightarrow> iADDI\<^sup>b \<phi>"  by (smt (verit, best) MONO_ADDIb MONO_def iADDI_b_def img_dir_def sup_char)
  from lr rl show ?thesis by auto
qed

(**Thus we have that MONO, MULT-a/iMULT-a and ADDI-b/iADDI-b are all equivalent.*)
lemma MONO_iADDIb: "iADDI\<^sup>b \<phi> = MONO \<phi>" unfolding MONO_ADDIb iADDIb_equ by simp
lemma MONO_iMULTa: "iMULT\<^sup>a \<phi> = MONO \<phi>" unfolding MONO_MULTa iMULTa_equ by simp


(**Below we prove several duality relationships between iADDI(a/b) and iMULT(a/b).*)

(**The first duality is an easy corollary of the previous equivalence.*)
lemma iMULTa_iADDIb_dual1: "iMULT\<^sup>a \<phi> = iADDI\<^sup>b \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual1 iADDIb_equ iMULTa_equ)
lemma iMULTa_iADDIb_dual2: "iADDI\<^sup>b \<phi> = iMULT\<^sup>a \<phi>\<^sup>d" using MONO_dual MONO_iADDIb MONO_iMULTa by auto

(*these two lemmas below are introduced for technical reasons (as stepping stones)*)
lemma iADDIa_impl_iMULTb: "\<forall>\<phi>. iADDI\<^sup>a \<phi> \<longrightarrow> iMULT\<^sup>b \<phi>\<^sup>d" unfolding iADDI_a_def iMULT_b_def using iDM_a iDM_b Ra_dual1 using order compl_def op_dual_def by (smt (verit, del_insts) setequ_equ)
lemma iMULTb_impl_iADDIa: "\<forall>\<phi>. iMULT\<^sup>b \<phi> \<longrightarrow> iADDI\<^sup>a \<phi>\<^sup>d" unfolding iADDI_a_def iMULT_b_def by (smt (verit, del_insts) Ra_dual3 compl_def iDM_b infimum_def op_dual_def setequ_equ subset_def)

(**Duality between iADDI-a and iMULT-b.*)
lemma iADDIa_iMULTb_dual1: "iADDI\<^sup>a \<phi> = iMULT\<^sup>b \<phi>\<^sup>d" by (metis dual_invol iADDIa_impl_iMULTb iMULTb_impl_iADDIa op_equal_equ)
lemma iADDIa_iMULTb_dual2: "iMULT\<^sup>b \<phi> = iADDI\<^sup>a \<phi>\<^sup>d" by (metis dual_invol iADDIa_iMULTb_dual1 op_equal_equ) 

(**Duality between iADDI and iMULT.*)
lemma iADDI_iMULT_dual1: "iADDI \<phi> = iMULT \<phi>\<^sup>d" by (meson MONO_dual MONO_iADDIb MONO_iMULTa iADDI_char iADDIa_iMULTb_dual1 iMULT_char)
lemma iADDI_iMULT_dual2: "iMULT \<phi> = iADDI \<phi>\<^sup>d" by (metis dual_invol iADDI_iMULT_dual1 op_equal_equ)

(**Other (not really surprising) result:*)
lemma iMULT_DNRM: "iMULT \<phi> \<Longrightarrow> DNRM \<phi>" by (metis (no_types) BA_dn DNRM_def NORM_def bottom_def comp_invol fp_c_rel fp_rel iADDI_def iADDI_iMULT_dual2 img_dir_def ofp_c ofp_invol op_compl_def op_dual_def op_equal_equ setequ_def setequ_equ subset_def sup_char)
lemma iADDI_NORM: "iADDI \<phi> \<Longrightarrow> NORM \<phi>" by (simp add: NOR_dual1 iADDI_iMULT_dual1 iMULT_DNRM)

(**Interestingly, we can show that suitable conditions on an operation can make the set
of its fixed points closed under infinite meets/joins.*)
lemma fp_inf_closed_cond1: "iMULT \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)" 
  unfolding iMULT_def infimum_closed_def fixpoint_pred_def by (smt (verit, best) img_dir_def inf_char setequ_def setequ_equ)
lemma fp_inf_closed_cond2: "iMULT\<^sup>b \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)"
  by (smt (z3) CNTR_def fixpoint_pred_def iMULT_b_def img_dir_def infimum_closed_def infimum_def setequ_def subset_def)
lemma fp_inf_closed_cond3: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)" by (smt (z3) EXPN_def MONO_def fixpoint_pred_def inf_char infimum_closed_def setequ_def setequ_equ)
lemma "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> infimum_closed (\<lbrakk>\<phi> -\<rbrakk>)" by (simp add: IDEM_Ra_fp fp_inf_closed_cond3)

lemma fp_sup_closed_cond1: "iADDI \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" by (metis dual_invol fp_inf_closed_cond1 fp_inf_sup_closed_dual iADDI_iMULT_dual1 op_equal_equ)
   
lemma fp_sup_closed_cond2: "iADDI\<^sup>a \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" by (smt (verit, best) BA_dn EXPN_CNTR_dual2 dom_compl_def fp_d fp_inf_closed_cond2 iADDIa_impl_iMULTb iDM_b infimum_closed_def setequ_equ supremum_closed_def)
lemma fp_sup_closed_cond3: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" by (metis CNTR_impl_NORM EXPN_CNTR_dual2 MONO_dual NORM_def dual_invol fixpoint_pred_def fp_inf_closed_cond3 fp_inf_sup_closed_dual inf_closed_char op_equal_equ sup_closed_char)
lemma "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> supremum_closed (\<lbrakk>\<phi> -\<rbrakk>)" by (simp add: IDEM_Ra_fp fp_sup_closed_cond3)

(**OTOH, the converse conjectures have (finite) countermodels. They need additional assumptions.*)
lemma "infimum_closed (fp \<phi>) \<Longrightarrow> iMULT \<phi>" nitpick oops
lemma "supremum_closed (fp \<phi>) \<Longrightarrow> iADDI \<phi>" nitpick oops
lemma fp_inf_closed_iMULT: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> infimum_closed (fp \<phi>) \<Longrightarrow> iMULT \<phi>"
proof -
  assume mono: "MONO \<phi>" and cntr: "CNTR \<phi>" and idem:"IDEM\<^sup>a \<phi>" and ic:"infimum_closed (fp \<phi>)"
  { fix S
    from ic have "\<forall>D. D \<sqsubseteq> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<And>D)" unfolding infimum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<approx> \<phi> X)) \<longrightarrow> \<^bold>\<And>D \<approx> \<phi> \<^bold>\<And>D" by (simp add: fixpoint_pred_def setequ_equ)
    moreover from idem have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<approx> \<phi> X))" by (metis (mono_tags, lifting) CNTR_def IDEM_a_def cntr img_dir_def setequ_def)
    ultimately have aux: "\<^bold>\<And>(\<lbrakk>\<phi> S\<rbrakk>) \<approx> \<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    from cntr have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<^bold>\<And>S" by (smt (verit, best) CNTR_def img_dir_def infimum_def subset_def)
    hence "\<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>) \<preceq> \<phi>(\<^bold>\<And>S)" using mono by (simp add: MONO_def) 
    from this aux have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<And>S)" by (simp add: setequ_equ)
  } hence "\<forall>S. \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<And>S)" by (rule allI)
  thus ?thesis using MONO_iMULTa iMULT_b_def iMULT_char mono by blast
qed
lemma fp_sup_closed_iADDI: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> supremum_closed (fp \<phi>) \<Longrightarrow> iADDI \<phi>" 
  using fp_inf_closed_iMULT EXPN_CNTR_dual2 IDEM_dual2 MONO_dual fp_sup_inf_closed_dual iADDI_iMULT_dual1 by blast
(*
proof -
  assume mono: "MONO \<phi>" and expn: "EXPN \<phi>" and idem:"IDEM\<^sup>b \<phi>" and sc:"supremum_closed (fp \<phi>)"
  { fix S
    from sc have "\<forall>D. D \<sqsubseteq> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<Or>D)" unfolding supremum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<approx> \<phi> X)) \<longrightarrow> \<^bold>\<Or>D \<approx> \<phi> \<^bold>\<Or>D" by (simp add: fixpoint_pred_def setequ_def)
    moreover have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<approx> \<phi> X))" by (metis (mono_tags, lifting) EXPN_def IDEM_b_def expn idem img_dir_def setequ_def)
    ultimately have aux: "\<^bold>\<Or>(\<lbrakk>\<phi> S\<rbrakk>) \<approx> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    have "\<^bold>\<Or>S \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis EXPN_CNTR_dual2 EXPN_def IDEM_dual2 MONO_dual expn fp_inf_closed_iMULT fp_sup_inf_closed_dual iADDI_def iADDI_iMULT_dual1 idem mono sc setequ_equ)
    hence "\<phi>(\<^bold>\<Or>S) \<preceq> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" using mono by (simp add: MONO_def) 
    from this aux have "\<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis setequ_equ)
  } hence "\<forall>S. \<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (rule allI)
  thus ?thesis by (simp add: MONO_iADDIb iADDI_a_def iADDI_char mono)
qed
*)

end