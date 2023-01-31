theory specialization
   imports separation
begin

section \<open>Generalized specialization orderings and Alexandrov topologies\<close>

(**A topology is called 'Alexandrov' (after the Russian mathematician Pavel Alexandrov) if the intersection
(resp. union) of any (finite or infinite) family of open (resp. closed) sets is open (resp. closed);
in algebraic terms, this means that the set of fixed points of the interior (closure) operation is closed
under infinite meets (joins). Another common algebraic formulation requires the closure (interior) operation
to satisfy the infinitary variants of additivity (multiplicativity), i.e. iADDI (iMULT) as introduced before.

In the literature, the well-known Kuratowski conditions for the closure (resp. interior) operation are assumed,
namely: ADDI, EXPN, NORM, IDEM (resp. MULT, CNTR, DNRM, IDEM). This makes both formulations equivalent.
However, this is not the case in general if those conditions become negotiable.*)

(**Alexandrov topologies have interesting properties relating them to the semantics of modal logic.
Assuming Kuratowski conditions, Alexandrov topological operations defined on subsets of S are in one-to-one
correspondence with preorders on S; in topological terms, Alexandrov topologies are uniquely determined by
their specialization preorders. Since we do not presuppose any Kuratowski conditions to begin with, the
preorders in question are in general not even transitive. Here we just call them 'specialization relations'.
We will still call (generalized) closure/interior-like operations as such (for lack of a better name).
We explore minimal conditions under which some relevant results for the semantics of modal logic obtain.*)

subsection \<open>Specialization relations\<close>

(**Closure/interior(-like) operators can be derived from an arbitrary relation (as in modal logic)*)
definition Cl_rel::"('w,'w)\<rho> \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("\<C>[_]") 
  where "\<C>[R] \<equiv> \<lambda>A. \<lambda>w. \<exists>v. R w v \<and> A v"
definition Int_rel::"('w,'w)\<rho> \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("\<I>[_]") 
  where "\<I>[R] \<equiv> \<lambda>A. \<lambda>w. \<forall>v. R w v \<longrightarrow> A v"

(**Duality between interior and closure follows directly:*)
lemma dual_rel1: "\<C>[R] = \<I>[R]\<^sup>d" by (simp add: Cl_rel_def Int_rel_def compl_def op_dual_def setequ_char)
lemma dual_rel2: "\<I>[R] = \<C>[R]\<^sup>d" using dual_rel1 dual_symm op_equal_equ by blast

(**We explore minimal conditions of the specialization relation under which some operation's conditions obtain.*) 
lemma rMONO: "MONO \<C>[R]" by (smt (verit, del_insts) Cl_rel_def MONO_def subset_def)
lemma rC1i: "iCl_1 \<C>[R]" unfolding iADDI_def Cl_rel_def img_dir_def supremum_def using setequ_char by fastforce
lemma rC2: "reflexive R \<longrightarrow> Cl_2 \<C>[R]" by (smt (verit, ccfv_threshold) Cl_rel_def EXPN_def reflexive_def subset_def)
lemma rC3: "Cl_3 \<C>[R]" by (simp add: iADDI_NORM rC1i)
lemma rC4: "reflexive R \<and> transitive R \<longrightarrow> Cl_4 \<C>[R]" by (smt (verit, best) Cl_rel_def EXPN_def IDEM_def rC2 setequ_char subset_def transitive_def)

(**A specialization relation can be derived from a given operation (intended as a closure-like operation).*)
definition spec_rel::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w,'w)\<rho>" ("sp[_]") 
  where "sp[\<C>] \<equiv> \<lambda>w v. \<C> {v} w"

(**Preorder properties of the specialization relation follow directly from the corresponding operation's conditions.*)
lemma sp_rel_refl: "Cl_2 \<C> \<Longrightarrow> reflexive sp[\<C>]"by (simp add: singleton_def EXPN_def reflexive_def spec_rel_def subset_def)
lemma sp_rel_trans: "MONO \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> transitive sp[\<C>]" unfolding singleton_def transitive_def IDEM_def MONO_def spec_rel_def by (smt (verit, best) setequ_equ subset_def)

(**However, we can obtain finite countermodels for antisymmetry and symmetry given all relevant conditions.
We will revisit this issue later and examine their relation with the topological separation axioms T0 and T1 resp.*)
lemma "iCl_1 \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_3 \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> antisymmetric sp[\<C>]" nitpick oops (*counterexample*)
lemma "iCl_1 \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_3 \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> symmetric sp[\<C>]" nitpick oops (*counterexample*)


subsection \<open>Alexandrov topology\<close>

(**As mentioned previously, Alexandrov closure (and by duality interior) operations correspond to specialization
relations. It is worth mentioning that in Alexandrov topologies every point has a minimal/smallest neighborhood,
namely the set of points related to it by the specialization (aka. accessibility) relation.
We examine below  minimal conditions under which these relations obtain.*)

lemma sp_rel_a:   "MONO \<C>  \<Longrightarrow> \<forall>A. \<C>[sp[\<C>]] A \<preceq> \<C> A" by (smt (verit, best) singleton_def Cl_rel_def MONO_def spec_rel_def subset_def)
lemma sp_rel_b: "iADDI_a \<C> \<Longrightarrow> \<forall>A. \<C>[sp[\<C>]] A \<succeq> \<C> A" proof -
  assume iaddia: "iADDI_a \<C>"
  { fix A::"'a \<sigma>"
    let ?S="\<lambda>B. \<exists>w. A w \<and> B=(\<lambda>u. u=w)"
    have "A \<approx> (\<^bold>\<Or>?S)" by (smt (verit, best) setequ_char supremum_def)
    hence "\<C>(A) \<approx> \<C>(\<^bold>\<Or>?S)" by (simp add: setequ_equ) 
    moreover have "\<^bold>\<Or>\<lbrakk>\<C> ?S\<rbrakk> \<approx> \<C>[sp[\<C>]] A" unfolding spec_rel_def singleton_def by (smt (verit) Cl_rel_def img_dir_def setequ_char supremum_def)
    moreover from iaddia have "\<C>(\<^bold>\<Or>?S) \<preceq> \<^bold>\<Or>\<lbrakk>\<C> ?S\<rbrakk>" unfolding iADDI_a_def by simp
    ultimately have "\<C> A \<preceq> \<C>[sp[\<C>]] A" by (simp add: setequ_equ)
  } thus ?thesis by simp
qed
lemma sp_rel: "iCl_1 \<C> \<Longrightarrow> \<C> = \<C>[sp[\<C>]]" by (meson MONO_iADDIb ext iADDI_char setequ_def setequ_equ sp_rel_a sp_rel_b)

(**It is instructive to expand the definitions in the above result:*)
lemma "iCl_1 \<C> \<Longrightarrow>  \<forall>A. \<forall>w. (\<C> A) w \<longleftrightarrow> (\<exists>v. A v \<and> \<C>{v} w)" by (smt (z3) Cl_rel_def singleton_def sp_rel)

(**We now turn to the more traditional characterization of Alexandrov topologies in terms of closure under
infinite joins/meets.*)

(**As shown above, closure (interior) operations derived from relations readily satisfy iADDI (iMULT),
being thus closed under infinite joins (meets).*)
lemma "supremum_closed (fp \<C>[R])" by (simp add: fp_sup_closed_cond1 rC1i)
lemma "infimum_closed  (fp \<I>[R::('w,'w)\<rho>])" by (simp add: dual_rel2 fp_sup_closed_cond1 fp_sup_inf_closed_dual rC1i)

subsection \<open>(Anti)symmetry and the separation axioms T0 and T1\<close>
(**We can now revisit the relationship between (anti)symmetry and the separation axioms T1 and T0.*)

(**Under appropriate conditions, T0-separation corresponds to antisymmetry of the specialization relation (here an ordering).*)
lemma "T0 \<C> \<longleftrightarrow> antisymmetric sp[\<C>]" nitpick oops (*counterexample*)
lemma T0_antisymm_a: "MONO \<C> \<Longrightarrow> T0 \<C> \<longrightarrow> antisymmetric sp[\<C>]" 
  unfolding T0_def antisymmetric_def using sp_rel_a Cl_rel_def by (smt (z3) compl_def fixpoint_pred_def op_dual_def setequ_char subset_def)
lemma T0_antisymm_b: "Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> antisymmetric sp[\<C>] \<longrightarrow> T0 \<C>" by (metis (full_types) Cl_Closed EXPN_def IDEM_a_def IDEM_char T0_def2 antisymmetric_def reflexive_def sp_rel_refl spec_rel_def)
lemma T0_antisymm: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4' \<C> \<Longrightarrow> T0 \<C> = antisymmetric sp[\<C>]" by (metis T0_antisymm_a T0_antisymm_b)

(**Also, under the appropriate conditions, T1-separation corresponds to symmetry of the specialization relation.*)
lemma T1_symm_a: "MONO \<C> \<Longrightarrow> T1 \<C> \<longrightarrow> symmetric sp[\<C>]" by (smt (verit) Cl_rel_def T1_def2 fixpoint_pred_def setequ_char sp_rel_a subset_def symmetric_def)
lemma T1_symm_b: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T0 \<C> \<Longrightarrow> symmetric sp[\<C>] \<longrightarrow> T1 \<C>" using T0_antisymm_a sp_rel_refl unfolding T1_def3 fixpoint_pred_def singleton_def antisymmetric_def reflexive_def symmetric_def spec_rel_def singleton_def by (smt (verit) setequ_char)
lemma T1_symm: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> T0 \<C> \<Longrightarrow> symmetric sp[\<C>] = T1 \<C>" by (metis T1_symm_a T1_symm_b)

end