
extern function pyon.internal.complex.repr_Complex
  (unit, owned) -> owned;

extern function pyon.internal.complex.AdditiveDict_Complex_add
  (unit, owned, owned, pointer, pointer, pointer) -> ();
extern function pyon.internal.complex.AdditiveDict_Complex_sub
  (unit, owned, owned, pointer, pointer, pointer) -> ();
extern function pyon.internal.complex.AdditiveDict_Complex_negate
  (unit, owned, owned, pointer, pointer) -> ();
extern function pyon.internal.complex.AdditiveDict_Complex_zero
  (unit, owned, owned, pointer) -> ();

extern function pyon.internal.complex.MultiplicativeDict_Complex_mul
  (unit, owned, owned, pointer, pointer, pointer) -> ();
extern function pyon.internal.complex.MultiplicativeDict_Complex_fromInt
  (unit, owned, owned, int, pointer) -> ();
extern function pyon.internal.complex.MultiplicativeDict_Complex_one
  (unit, owned, owned, pointer) -> ();

extern function pyon.internal.complex.FractionalDict_Complex_div
  (unit, owned, owned, pointer, pointer, pointer) -> ();
