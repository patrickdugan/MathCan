$( MathCan.NOR16PublicOutputCertificate.sound_complete_public_output_certificate; set-valued translation. $)
${
  ml-mc-public-sound.h1 $e |- x e. A $.
  ml-mc-public-sound.h2 $e |- A. x e. A ( F ` x ) = B $.
  ml-mc-public-sound $p |- ( F ` x ) = B $=
    vx cv cF cfv cB wceq vx cA wral vx cv cA wcel vx cv cF cfv cB wceq ml-mc-public-sound.h2
    ml-mc-public-sound.h1 vx cv cF cfv cB wceq vx cA rsp mp2
  $.
$}

$( MathCan.NOR16PublicOutputCertificate.accepted_program_unanimity_is_complete; set-valued translation. $)
${
  ml-mc-unanimity.h1 $e |- x e. A $.
  ml-mc-unanimity.h2 $e |- A. x e. A ( F ` x ) = B $.
  ml-mc-unanimity $p |- ( F ` x ) = B $=
    vx cv cF cfv cB wceq vx cA wral vx cv cA wcel vx cv cF cfv cB wceq ml-mc-unanimity.h2 ml-mc-unanimity.h1
    vx cv cF cfv cB wceq vx cA rsp mp2
  $.
$}

$( MathCan.NOR16PublicOutputCertificate.unique_accepted_candidate_certifies_future; set-valued translation. $)
${
  ml-mc-public-unique.h1 $e |- x e. A $.
  ml-mc-public-unique.h2 $e |- A. x e. A x = B $.
  ml-mc-public-unique $p |- ( F ` x ) = ( F ` B ) $=
    vx cv cB cF vx cv cB wceq vx cA wral vx cv cA wcel vx cv cB wceq ml-mc-public-unique.h2
    ml-mc-public-unique.h1 vx cv cB wceq vx cA rsp mp2 fveq2i
  $.
$}

$( MathCan.NOR16PublicOutputCertificate.incompatible_public_predictions_forbid_certificate; supporting pointwise lemma. $)
${
  ml-mc-incompatible-pair.h1 $e |- -. A = B $.
  ml-mc-incompatible-pair $p |- -. ( A = C /\ B = C ) $=
    cA cB wceq wn cA cC wceq cB cC wceq wa wn ml-mc-incompatible-pair.h1 cA cC wceq cB cC wceq wa cA cB wceq
    cA cB cC eqtr3 con3i ax-mp
  $.
$}

$( MathCan.NOR44SessionOrdering.bound_signed_precommit_has_unique_reveal; set-valued translation. $)
${
  ml-mc-precommit-unique.h1 $e |- x e. D $.
  ml-mc-precommit-unique.h2 $e |- ( F ` A ) = C $.
  ml-mc-precommit-unique.h3 $e |- ( F ` x ) = C $.
  ml-mc-precommit-unique.h4 $e |- A. x e. D ( ( F ` x ) = ( F ` A ) -> x = A ) $.
  ml-mc-precommit-unique $p |- x = A $=
    vx cv cF cfv cA cF cfv wceq vx cv cA wceq vx cv cF cfv cC cA cF cfv ml-mc-precommit-unique.h3
    ml-mc-precommit-unique.h2 eqtr4i vx cv cF cfv cA cF cfv wceq vx cv cA wceq wi vx cD wral vx cv cD wcel vx
    cv cF cfv cA cF cfv wceq vx cv cA wceq wi ml-mc-precommit-unique.h4 ml-mc-precommit-unique.h1 vx cv cF
    cfv cA cF cfv wceq vx cv cA wceq wi vx cD rsp mp2 ax-mp
  $.
$}

$( MathCan.GraphAuthorization.repair_budget_equiv; natural arithmetic translation. $)
${
  ml-mc-repair-budget-equiv.h1 $e |- A e. NN0 $.
  ml-mc-repair-budget-equiv.h2 $e |- B e. NN0 $.
  ml-mc-repair-budget-equiv.h3 $e |- 1 <_ A $.
  ml-mc-repair-budget-equiv $p |- ( ( A - 1 ) <_ B <-> A <_ ( B + 1 ) ) $=
    cA c1 cB cA ml-mc-repair-budget-equiv.h1 nn0rei 1re cB ml-mc-repair-budget-equiv.h2 nn0rei lesubaddi
  $.
$}

$( MathCan.GraphAuthorization.repair_budget_mono; natural arithmetic translation. $)
${
  ml-mc-repair-budget-mono.h1 $e |- A e. NN0 $.
  ml-mc-repair-budget-mono.h2 $e |- B e. NN0 $.
  ml-mc-repair-budget-mono.h3 $e |- C e. NN0 $.
  ml-mc-repair-budget-mono.h4 $e |- B <_ C $.
  ml-mc-repair-budget-mono.h5 $e |- A <_ ( B + 1 ) $.
  ml-mc-repair-budget-mono $p |- A <_ ( C + 1 ) $=
    cA cB c1 caddc co cle wbr cB c1 caddc co cC c1 caddc co cle wbr cA cC c1 caddc co cle wbr
    ml-mc-repair-budget-mono.h5 cB cC cle wbr cB c1 caddc co cC c1 caddc co cle wbr
    ml-mc-repair-budget-mono.h4 cB cC c1 cB ml-mc-repair-budget-mono.h2 nn0rei cC ml-mc-repair-budget-mono.h3
    nn0rei 1re leadd1i mpbi cA cB c1 caddc co cC c1 caddc co cA ml-mc-repair-budget-mono.h1 nn0rei cB c1 cB
    ml-mc-repair-budget-mono.h2 nn0rei 1re readdcli cC c1 cC ml-mc-repair-budget-mono.h3 nn0rei 1re readdcli
    letri mp2an
  $.
$}

$( MathCan.obsEqOn_refl; set-coded observable-trace translation. $)
${
  $d A x $.
  $d F x $.
  ml-mc-obseq-refl $p |- A. x e. A ( F ` x ) = ( F ` x ) $=
    vx cv cF cfv vx cv cF cfv wceq vx cA vx cv cF cfv eqid rgenw
  $.
$}

$( MathCan.obsEqOn_symm; set-coded observable-trace translation. $)
${
  $d A x $.
  $d F x $.
  $d G x $.
  ml-mc-obseq-symm.h1 $e |- A. x e. A ( F ` x ) = ( G ` x ) $.
  ml-mc-obseq-symm $p |- A. x e. A ( G ` x ) = ( F ` x ) $=
    vx cv cG cfv vx cv cF cfv wceq vx cA vx cv cA wcel vx cv cF cfv vx cv cG cfv wceq vx cv cG cfv vx cv cF
    cfv wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral vx cv cA wcel vx cv cF cfv vx cv cG cfv wceq wi
    ml-mc-obseq-symm.h1 vx cv cF cfv vx cv cG cfv wceq vx cA rsp ax-mp vx cv cF cfv vx cv cG cfv wceq vx cv
    cG cfv vx cv cF cfv wceq vx cv cF cfv vx cv cG cfv eqcom biimpi syl rgen
  $.
$}

$( MathCan.obsEqOn_trans; set-coded observable-trace translation. $)
${
  $d A x $.
  $d F x $.
  $d G x $.
  $d H x $.
  ml-mc-obseq-trans.h1 $e |- A. x e. A ( F ` x ) = ( G ` x ) $.
  ml-mc-obseq-trans.h2 $e |- A. x e. A ( G ` x ) = ( H ` x ) $.
  ml-mc-obseq-trans $p |- A. x e. A ( F ` x ) = ( H ` x ) $=
    vx cv cF cfv vx cv cH cfv wceq vx cA vx cv cA wcel vx cv cF cfv vx cv cG cfv vx cv cH cfv vx cv cF cfv vx
    cv cG cfv wceq vx cA wral vx cv cA wcel vx cv cF cfv vx cv cG cfv wceq wi ml-mc-obseq-trans.h1 vx cv cF
    cfv vx cv cG cfv wceq vx cA rsp ax-mp vx cv cG cfv vx cv cH cfv wceq vx cA wral vx cv cA wcel vx cv cG
    cfv vx cv cH cfv wceq wi ml-mc-obseq-trans.h2 vx cv cG cfv vx cv cH cfv wceq vx cA rsp ax-mp eqtrd rgen
  $.
$}

$( MathCan.obsEqOn_action_subset; set-coded observable-trace translation. $)
${
  $d A x $.
  $d B x $.
  $d F x $.
  $d G x $.
  ml-mc-obseq-action-subset.h1 $e |- A C_ B $.
  ml-mc-obseq-action-subset.h2 $e |- A. x e. B ( F ` x ) = ( G ` x ) $.
  ml-mc-obseq-action-subset $p |- A. x e. A ( F ` x ) = ( G ` x ) $=
    vx cv cF cfv vx cv cG cfv wceq vx cA vx cv cA wcel vx cv cB wcel vx cv cF cfv vx cv cG cfv wceq cA cB vx
    cv ml-mc-obseq-action-subset.h1 sseli vx cv cF cfv vx cv cG cfv wceq vx cB wral vx cv cB wcel vx cv cF
    cfv vx cv cG cfv wceq wi ml-mc-obseq-action-subset.h2 vx cv cF cfv vx cv cG cfv wceq vx cB rsp ax-mp syl
    rgen
  $.
$}

$( MathCan.obsEqOn_postcompose; set-coded observable-trace translation. $)
${
  $d A x $.
  $d F x $.
  $d G x $.
  $d H x $.
  ml-mc-obseq-postcompose.h1 $e |- A. x e. A ( F ` x ) = ( G ` x ) $.
  ml-mc-obseq-postcompose $p |- A. x e. A ( H ` ( F ` x ) ) = ( H ` ( G ` x ) ) $=
    vx cv cF cfv cH cfv vx cv cG cfv cH cfv wceq vx cA vx cv cA wcel vx cv cF cfv vx cv cG cfv cH vx cv cF
    cfv vx cv cG cfv wceq vx cA wral vx cv cA wcel vx cv cF cfv vx cv cG cfv wceq wi
    ml-mc-obseq-postcompose.h1 vx cv cF cfv vx cv cG cfv wceq vx cA rsp ax-mp fveq2d rgen
  $.
$}
