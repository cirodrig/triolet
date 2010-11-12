# Test whether members of "Additive" class work correctly

def adds(a, b):
  return -b - (a + zero)

export ccall "addsi" adds : int * int -> int;
export ccall "addsf" adds : float * float -> float;
