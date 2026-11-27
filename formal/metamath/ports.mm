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
