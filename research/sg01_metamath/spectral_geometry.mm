$( Standalone additive-group equational fragment; arithmetic and equality axioms are explicit. $)
$c term |- eq add neg zero $.
$v a b c $.
ta $f term a $.
tb $f term b $.
tc $f term c $.
zero-t $a term zero $.
neg-t $a term neg a $.
add-t $a term add a b $.
assoc $a |- eq add add a b c add a add b c $.
comm $a |- eq add a b add b a $.
inv $a |- eq add neg a a zero $.
left-id $a |- eq add zero a a $.
${ sh $e |- eq a b $. sym $a |- eq b a $. $}
${ th1 $e |- eq a b $. th2 $e |- eq b c $. trans $a |- eq a c $. $}
${ lh $e |- eq a b $. lc $a |- eq add c a add c b $. $}
${ rh $e |- eq a b $. rc $a |- eq add a c add b c $. $}
cancel-middle $p |- eq add add a neg b add b c add a c $=
  ta tb neg-t add-t tb tc add-t add-t ta zero-t tc add-t
  add-t ta tc add-t ta tb neg-t add-t tb tc add-t add-t
  ta tb neg-t tb add-t tc add-t add-t ta zero-t tc add-t
  add-t ta tb neg-t add-t tb tc add-t add-t ta tb neg-t
  tb tc add-t add-t add-t ta tb neg-t tb add-t tc add-t
  add-t ta tb neg-t tb tc add-t assoc tb neg-t tb tc
  add-t add-t tb neg-t tb add-t tc add-t ta tb neg-t tb
  add-t tc add-t tb neg-t tb tc add-t add-t tb neg-t tb
  tc assoc sym lc trans tb neg-t tb add-t tc add-t zero-t
  tc add-t ta tb neg-t tb add-t zero-t tc tb inv rc
  lc trans zero-t tc add-t tc ta tc left-id lc trans
$.
wire-concat $p |- eq add add b neg a add c neg b add c neg a $=
  tb ta neg-t add-t tc tb neg-t add-t add-t tc tb neg-t
  add-t tb ta neg-t add-t add-t tc ta neg-t add-t tb ta
  neg-t add-t tc tb neg-t add-t comm tc tb ta neg-t cancel-middle
  trans
$.
