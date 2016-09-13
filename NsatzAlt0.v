Require Export NsatzTest.SetupAlt.
Definition pre_goal1 : goal0 * Prop.
  start.
  intros *.
  intros ???.
  let power := constr:(6) in
  let power_N := (eval compute in (BinNat.N.of_nat power)) in
  let sugar := constr:(BinInt.Z0) in
  let power := power_N in
  let domain := constr:(_:Integral_domain.Integral_domain (ring_eq:=Qeq)) in
  let nparams := constr:(BinInt.Zneg BinPos.xH) in (* some symbols can be "parameters", treated as coefficients *)
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    nsatz_clear_duplicates_for_bug_4851 domain;
      nsatz_rewrite_and_revert domain;
      let reified_package := nsatz_reify_equations eq zero in
      pose reified_package as r; revert r
  end. (*
    let fv := nsatz_get_free_variables reified_package in
    let interp := constr:(@Nsatz.PEevalR _ _ _ _ _ _ _ _ Fops fv) in
    let reified_givens := nsatz_get_reified_givens reified_package in
    let reified_goal := nsatz_get_reified_goal reified_package in
    nsatz_compute_to_goal sugar nparams reified_goal power reified_givens;
    let a := nsatz_compute_get_leading_coefficient in
    let crt := nsatz_compute_get_certificate in
    intros _ (* discard [nsatz_compute] output *); intros;
    apply (fun Haa refl cond => @Integral_domain.Rintegral_domain_pow _ _ _ _ _ _ _ _ _ _ _ domain (interp a) _ (BinNat.N.to_nat power) Haa (@Nsatz.check_correct _ _ _ _ _ _ _ _ _ _ FCring fv reified_givens (PEmul a (PEpow reified_goal power)) crt refl cond));
    [ nsatz_nonzero; cbv iota beta delta [Nsatz.PEevalR PEeval InitialRing.gen_phiZ InitialRing.gen_phiPOS]
    | solve [vm_compute; exact (eq_refl true)] (* exact_no_check (eq_refl true) *)
    | solve [repeat (split; [assumption|]); exact I] ]
  end. *)
  finish.
Defined.

Definition goal1 : Prop.
Proof. get_snd pre_goal1. Defined.
