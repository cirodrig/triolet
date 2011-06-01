
extern function pyon.internal.complex.repr_Complex
  (owned) -> owned;

extern function pyon.internal.complex.AdditiveDict_Complex_add
  (owned, owned, pointer, pointer, pointer) -> ();
extern function pyon.internal.complex.AdditiveDict_Complex_sub
  (owned, owned, pointer, pointer, pointer) -> ();
extern function pyon.internal.complex.AdditiveDict_Complex_negate
  (owned, owned, pointer, pointer) -> ();
extern function pyon.internal.complex.AdditiveDict_Complex_zero
  (owned, owned, pointer) -> ();

extern function pyon.internal.complex.MultiplicativeDict_Complex_mul
  (owned, owned, pointer, pointer, pointer) -> ();
extern function pyon.internal.complex.MultiplicativeDict_Complex_fromInt
  (owned, owned, int, pointer) -> ();
extern function pyon.internal.complex.MultiplicativeDict_Complex_one
  (owned, owned, pointer) -> ();

extern function pyon.internal.complex.FractionalDict_Complex_div
  (owned, owned, pointer, pointer, pointer) -> ();
