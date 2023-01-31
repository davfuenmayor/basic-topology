theory boolean_algebra_infinitary
  imports boolean_algebra
begin

subsection \<open>Encoding infinitary Boolean operations\<close>

(**Our aim is to encode complete Boolean algebras (of propositions) which we can be used to
interpret quantified formulas (much in the spirit of Boolean-valued models for set theory).*)

(**We start by defining infinite meet (infimum) and infinite join (supremum) operations,*)
definition infimum:: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<And>_") 
  where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"
definition supremum::"('w \<sigma> \<Rightarrow> bool) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<Or>_") 
  where "\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w"

named_theorems iconn (*to group together definitions involving infinitary algebraic connectives*)
declare infimum_def[iconn] supremum_def[iconn]

(**and show that the encoded Boolean algebra is complete (as a lattice).*)
abbreviation "upper_bound U S \<equiv> \<forall>X. (S X) \<longrightarrow> X \<^bold>\<preceq> U"
abbreviation "lower_bound L S \<equiv> \<forall>X. (S X) \<longrightarrow> L \<^bold>\<preceq> X"
abbreviation "is_supremum U S \<equiv> upper_bound U S \<and> (\<forall>X. upper_bound X S \<longrightarrow> U \<^bold>\<preceq> X)"
abbreviation "is_infimum  L S \<equiv> lower_bound L S \<and> (\<forall>X. lower_bound X S \<longrightarrow> X \<^bold>\<preceq> L)"

lemma sup_char: "is_supremum \<^bold>\<Or>S S" unfolding order supremum_def by auto
lemma sup_ext: "\<forall>S. \<exists>X. is_supremum X S" unfolding order by (metis supremum_def)
lemma inf_char: "is_infimum \<^bold>\<And>S S" unfolding order infimum_def by auto
lemma inf_ext: "\<forall>S. \<exists>X. is_infimum X S" unfolding order by (metis infimum_def)

abbreviation "isEmpty S \<equiv> \<forall>x. \<not>S x"
abbreviation "nonEmpty S \<equiv> \<exists>x. S x"
abbreviation containment (infix "\<sqsubseteq>" 100) 
  where "D \<sqsubseteq> S \<equiv>  \<forall>X. D X \<longrightarrow> S X" (*read as "all Ds are contained in S"*)

lemma "isEmpty S \<Longrightarrow> \<^bold>\<And>S \<^bold>\<approx> \<^bold>\<top>" by (simp add: infimum_def setequ_char top_def)
lemma "isEmpty S \<Longrightarrow> \<^bold>\<Or>S \<^bold>\<approx> \<^bold>\<bottom>" by (simp add: bottom_def setequ_char supremum_def)

(**The property of being closed under arbitrary (resp. nonempty) supremum/infimum.*)
definition "infimum_closed S  \<equiv> \<forall>D. D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<And>D)" (*observe that D can be empty*)
definition "supremum_closed S \<equiv> \<forall>D. D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<Or>D)"
definition "infimum_closed' S  \<equiv> \<forall>D. nonEmpty D \<and> D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<And>D)"
definition "supremum_closed' S \<equiv> \<forall>D. nonEmpty D \<and> D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<Or>D)"

declare infimum_closed_def[iconn]  supremum_closed_def[iconn]
        infimum_closed'_def[iconn] supremum_closed'_def[iconn]

(**Note that arbitrary infimum- (resp. supremum-) closed sets include the top (resp. bottom) element.*)
lemma "infimum_closed S \<Longrightarrow> S \<^bold>\<top>" unfolding infimum_closed_def infimum_def top_def by auto
lemma "supremum_closed S \<Longrightarrow> S \<^bold>\<bottom>" unfolding supremum_closed_def supremum_def bottom_def by auto
(**However, the above does not hold for non-empty infimum- (resp. supremum-) closed sets.*)
lemma "infimum_closed' S \<Longrightarrow> S \<^bold>\<top>" nitpick oops
lemma "supremum_closed' S \<Longrightarrow> S \<^bold>\<bottom>" nitpick oops

(**We have in fact the following characterizations for the notions above:*)
lemma inf_closed_char: "infimum_closed S = (infimum_closed' S \<and> S \<^bold>\<top>)" proof -
  have l2r: "infimum_closed S \<Longrightarrow> (infimum_closed' S \<and> S \<^bold>\<top>)" unfolding infimum_closed'_def infimum_closed_def by (metis L10 L13 bottom_def infimum_def setequ_equ subset_def top_def)
  have r2l: "(infimum_closed' S \<and> S \<^bold>\<top>) \<Longrightarrow> infimum_closed S" unfolding infimum_closed'_def infimum_closed_def by (metis L10 L13 inf_char setequ_equ)
  from l2r r2l show ?thesis by blast
qed
lemma sup_closed_char: "supremum_closed S = (supremum_closed' S \<and> S \<^bold>\<bottom>)" proof -
  have l2r: "supremum_closed S \<Longrightarrow> (supremum_closed' S \<and> S \<^bold>\<bottom>)" unfolding supremum_closed'_def supremum_closed_def by (metis L14 L9 bottom_def setequ_equ sup_char)
  have r2l: "(supremum_closed' S \<and> S \<^bold>\<bottom>) \<Longrightarrow> supremum_closed S" unfolding supremum_closed'_def supremum_closed_def by (metis L14 L9 setequ_equ sup_char)
  from l2r r2l show ?thesis by blast
qed

(**We verify that being infimum-closed' (resp. supremum-closed') entails being meet-closed (resp. join-closed).*)
lemma inf_meet_closed: "\<forall>S. infimum_closed' S \<longrightarrow> meet_closed S" proof -
  { fix S::"'w \<sigma> \<Rightarrow> bool"
    { assume inf_closed: "infimum_closed' S"
      hence "meet_closed S" proof -
        { fix X::"'w \<sigma>" and Y::"'w \<sigma>"
          let ?D="\<lambda>Z. Z=X \<or> Z=Y"
          { assume "S X \<and> S Y"
            hence "?D \<sqsubseteq> S" by simp
            moreover have "nonEmpty ?D" by auto
            ultimately have "S(\<^bold>\<And>?D)" using inf_closed infimum_closed'_def by (smt (z3))
            hence "S(\<lambda>w. \<forall>Z. (Z=X \<or> Z=Y) \<longrightarrow> Z w)" unfolding infimum_def by simp
            moreover have "(\<lambda>w. \<forall>Z. (Z=X \<or> Z=Y) \<longrightarrow> Z w) = (\<lambda>w. X w \<and> Y w)" by auto
            ultimately have "S(\<lambda>w. X w \<and> Y w)" by simp
          } hence "(S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)" unfolding conn by (rule impI)
        } thus ?thesis unfolding meet_closed_def by simp  qed
    } hence "infimum_closed' S \<longrightarrow> meet_closed S" by simp
  } thus ?thesis by (rule allI)
qed
lemma sup_join_closed: "\<forall>P. supremum_closed' P \<longrightarrow> join_closed P" proof -
  { fix S::"'w \<sigma> \<Rightarrow> bool"
    { assume sup_closed: "supremum_closed' S"
      hence "join_closed S" proof -
        { fix X::"'w \<sigma>" and Y::"'w \<sigma>"
          let ?D="\<lambda>Z. Z=X \<or> Z=Y"
          { assume "S X \<and> S Y"
            hence "?D \<sqsubseteq> S" by simp
            moreover have "nonEmpty ?D" by auto
            ultimately have "S(\<^bold>\<Or>?D)" using sup_closed supremum_closed'_def by (smt (z3))
            hence "S(\<lambda>w. \<exists>Z. (Z=X \<or> Z=Y) \<and> Z w)" unfolding supremum_def by simp
            moreover have "(\<lambda>w. \<exists>Z. (Z=X \<or> Z=Y) \<and> Z w) = (\<lambda>w. X w \<or> Y w)" by auto
            ultimately have "S(\<lambda>w. X w \<or> Y w)" by simp
          } hence "(S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)" unfolding conn by (rule impI)
        } thus ?thesis unfolding join_closed_def by simp qed
    } hence "supremum_closed' S \<longrightarrow> join_closed S" by simp
  } thus ?thesis by (rule allI)
qed


subsection \<open>Domains of propositions and ranges of functions\<close>

(**This useful construct returns for a given set of propositions the set of their complements.*)
definition dom_compl::"('w \<sigma> \<Rightarrow> bool) \<Rightarrow> ('w \<sigma> \<Rightarrow> bool)" ("(_\<^sup>-)") 
  where "D\<^sup>- \<equiv> \<lambda>X. D(\<^bold>\<midarrow>X)"

(*We verify that the above definition is equivalent to the intended one.*)
lemma dom_compl_char: "D\<^sup>- = (\<lambda>X. \<exists>Y. (D Y) \<and> (X = \<^bold>\<midarrow>Y))" unfolding dom_compl_def
  by (metis (mono_tags) BA_cp compl_def setequ_def setequ_equ subset_def)

(**This construct is in fact involutive.*)
lemma dom_compl_invol: "(D\<^sup>-)\<^sup>- = D" by (simp add: BA_dn dom_compl_def)

(**We can now check an infinite variant of the De Morgan laws,*)
lemma iDM_a: "\<^bold>\<midarrow>(\<^bold>\<And>S) \<^bold>\<approx> \<^bold>\<Or>(S\<^sup>-)" unfolding order conn dom_compl_def infimum_def supremum_def using compl_def by force
lemma iDM_b:" \<^bold>\<midarrow>(\<^bold>\<Or>S) \<^bold>\<approx> \<^bold>\<And>(S\<^sup>-)" unfolding order conn dom_compl_def infimum_def supremum_def using compl_def by force

(**and that D and their complements are in a 1-1 correspondance*)
lemma dom_compl_1to1: "correspond1to1 D D\<^sup>-" by (metis (mono_tags, lifting) BA_dn dom_compl_def injectiveRel_def mapping_def surjectiveRel_def)

(**as well as some useful dualities regarding the image of propositional functions (restricted wrt. a domain).*)
lemma Ra_compl: "\<lbrakk>\<pi>\<^sup>c D\<rbrakk>  = \<lbrakk>\<pi> D\<rbrakk>\<^sup>-" unfolding img_dir_def dom_compl_char by (metis op_compl_def)
lemma Ra_dual1: "\<lbrakk>\<pi>\<^sup>d D\<rbrakk>  = \<lbrakk>\<pi> D\<^sup>-\<rbrakk>\<^sup>-" unfolding img_dir_def dom_compl_char by (metis op_dual_def)
lemma Ra_dual2: "\<lbrakk>\<pi>\<^sup>d D\<rbrakk>  = \<lbrakk>\<pi>\<^sup>c D\<^sup>-\<rbrakk>" unfolding img_dir_def dom_compl_char by (metis op_compl_def op_dual_def)
lemma Ra_dual3: "\<lbrakk>\<pi>\<^sup>d D\<rbrakk>\<^sup>- = \<lbrakk>\<pi> D\<^sup>-\<rbrakk>" by (metis Ra_compl Ra_dual2 comp_invol op_equal_equ)
lemma Ra_dual4: "\<lbrakk>\<pi>\<^sup>d D\<^sup>-\<rbrakk> = \<lbrakk>\<pi> D\<rbrakk>\<^sup>-" by (metis Ra_dual3 dual_invol op_equal_equ)

(**We check some further properties:*)
lemma fp_sup_inf_closed_dual': "supremum_closed' (fp \<phi>) \<Longrightarrow> infimum_closed' (fp \<phi>\<^sup>d)" unfolding supremum_closed'_def infimum_closed'_def by (metis dom_compl_char fp_d iDM_a setequ_equ)
lemma fp_sup_inf_closed_dual: "supremum_closed (fp \<phi>) \<Longrightarrow> infimum_closed (fp \<phi>\<^sup>d)" by (simp add: bottom_def compl_def fp_d fp_sup_inf_closed_dual' inf_closed_char sup_closed_char top_def)
lemma fp_inf_sup_closed_dual': "infimum_closed' (fp \<phi>) \<Longrightarrow> supremum_closed' (fp \<phi>\<^sup>d)" unfolding supremum_closed'_def infimum_closed'_def by (metis dom_compl_char fp_d iDM_b setequ_equ)
lemma fp_inf_sup_closed_dual: "infimum_closed (fp \<phi>) \<Longrightarrow> supremum_closed (fp \<phi>\<^sup>d)" by (simp add: bottom_def compl_def fp_d fp_inf_sup_closed_dual' inf_closed_char sup_closed_char top_def)


subsection \<open>Adding quantifiers (restricted and unrestricted)\<close>

(**We can harness HOL to define quantification over individuals of arbitrary type (using polymorphism).
These (unrestricted) quantifiers take a propositional function and give a proposition.*)  
definition mforall::"('e,'w)\<rho> \<Rightarrow> 'w \<sigma>" ("\<Q>\<^sup>\<forall>_" [55]56) 
  where "\<Q>\<^sup>\<forall>\<pi> \<equiv> \<lambda>w. \<forall>X. (\<pi> X) w"
definition mexists::"('e,'w)\<rho> \<Rightarrow> 'w \<sigma>" ("\<Q>\<^sup>\<exists>_" [55]56) 
  where "\<Q>\<^sup>\<exists>\<pi> \<equiv> \<lambda>w. \<exists>X. (\<pi> X) w"
(**To improve readability, we introduce for them standard binder notation.*)
abbreviation mforallB (binder"\<^bold>\<forall>"[55]56) where "\<^bold>\<forall>X. \<pi> X \<equiv> \<Q>\<^sup>\<forall>\<pi>"
abbreviation mexistsB (binder"\<^bold>\<exists>"[55]56) where "\<^bold>\<exists>X. \<pi> X \<equiv> \<Q>\<^sup>\<exists>\<pi>"

(**Moreover, we define restricted quantifiers which take a 'functional domain' as additional parameter.
The latter is a propositional function that maps each element 'e' to the proposition 'e exists'.*)
definition mforall_restr::"('e,'w)\<rho> \<Rightarrow> ('e,'w)\<rho> \<Rightarrow> 'w \<sigma>" ("\<Q>\<^sup>\<forall>[_]_") 
  where "\<Q>\<^sup>\<forall>[\<delta>]\<pi> \<equiv> \<lambda>w.\<forall>X. (\<delta> X) w \<longrightarrow> (\<pi> X) w" 
definition mexists_restr::"('e,'w)\<rho> \<Rightarrow> ('e,'w)\<rho> \<Rightarrow> 'w \<sigma>" ("\<Q>\<^sup>\<exists>[_]_") 
  where "\<Q>\<^sup>\<exists>[\<delta>]\<pi> \<equiv> \<lambda>w.\<exists>X. (\<delta> X) w  \<and>  (\<pi> X) w"

declare mforall_def[iconn] mexists_def[iconn] mforall_restr_def[iconn] mexists_restr_def[iconn]

(**We check some facts concerning duality for quantifiers (using both notations).*)
lemma QDM_a: "\<Q>\<^sup>\<forall>\<pi>\<^sup>c \<^bold>\<approx> \<^bold>\<midarrow>(\<Q>\<^sup>\<exists>\<pi>)" by (simp add: iconn compl_def op_compl_def setequ_equ)
lemma QDM_b: "\<Q>\<^sup>\<exists>\<pi>\<^sup>c \<^bold>\<approx> \<^bold>\<midarrow>(\<Q>\<^sup>\<forall>\<pi>)" by (simp add: iconn compl_def op_compl_def setequ_equ)
lemma "\<^bold>\<exists>X. \<^bold>\<midarrow>(\<pi> X) \<^bold>\<approx> \<^bold>\<midarrow>(\<^bold>\<forall>X. \<pi> X)" by (simp add: iconn compl_def setequ_equ)
lemma "\<^bold>\<forall>X. \<^bold>\<midarrow>(\<pi> X) \<^bold>\<approx> \<^bold>\<midarrow>(\<^bold>\<exists>X. \<pi> X)" by (simp add: iconn compl_def setequ_equ)

lemma QDM_restr_a: "\<Q>\<^sup>\<forall>[\<delta>]\<pi>\<^sup>c \<^bold>\<approx> \<^bold>\<midarrow>(\<Q>\<^sup>\<exists>[\<delta>]\<pi>)" by (simp add: iconn compl_def op_compl_def setequ_char)
lemma QDM_restr_b: "\<Q>\<^sup>\<exists>[\<delta>]\<pi>\<^sup>c \<^bold>\<approx> \<^bold>\<midarrow>(\<Q>\<^sup>\<forall>[\<delta>]\<pi>)" by (simp add: iconn compl_def op_compl_def setequ_char)

(**Finally we check that taking infinite joins/meets (suprema/infima) over the range of a propositional function
can be equivalently codified by using quantifiers. This is a quite useful simplifying relationship.*)

lemma Ra_all: "\<Q>\<^sup>\<forall>\<pi> \<^bold>\<approx> \<^bold>\<And>\<lbrakk>\<pi> -\<rbrakk>" by (smt (verit) iconn infimum_def range_def setequ_char)
lemma Ra_ex:  "\<Q>\<^sup>\<exists>\<pi> \<^bold>\<approx> \<^bold>\<Or>\<lbrakk>\<pi> -\<rbrakk>" by (smt (verit) iconn range_def setequ_char supremum_def)

(**The following 'type-lifting' function is useful for converting sets into 'rigid' propositional functions.*)
abbreviation lift_conv::"('e \<Rightarrow> bool) \<Rightarrow> ('e,'w)\<rho>" ("\<lparr>_\<rparr>") where "\<lparr>S\<rparr> \<equiv> \<lambda>X. \<lambda>w. S X"

lemma Ra_restr_all: "\<Q>\<^sup>\<forall>[\<lparr>D\<rparr>]\<pi> \<^bold>\<approx> \<^bold>\<And>\<lbrakk>\<pi> D\<rbrakk>" by (smt (verit) iconn infimum_def img_dir_def setequ_char)
lemma Ra_restr_ex:  "\<Q>\<^sup>\<exists>[\<lparr>D\<rparr>]\<pi> \<^bold>\<approx> \<^bold>\<Or>\<lbrakk>\<pi> D\<rbrakk>" by (smt (verit) iconn img_dir_def setequ_char supremum_def)

(**The previous definitions allow us to nicely characterize the interaction
between function composition and (restricted) quantification:*)
lemma Ra_all_comp: "\<Q>\<^sup>\<forall>(\<pi>\<circ>\<gamma>) \<^bold>\<approx> \<Q>\<^sup>\<forall>[\<lparr>\<lbrakk>\<gamma> -\<rbrakk>\<rparr>] \<pi>" by (smt (verit, best) iconn fun_comp_def setequ_char range_def)
lemma Ra_ex_comp:  "\<Q>\<^sup>\<exists>(\<pi>\<circ>\<gamma>) \<^bold>\<approx> \<Q>\<^sup>\<exists>[\<lparr>\<lbrakk>\<gamma> -\<rbrakk>\<rparr>] \<pi>" by (smt (verit, best) iconn fun_comp_def setequ_char range_def)

end